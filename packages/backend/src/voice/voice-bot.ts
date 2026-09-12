import { EventEmitter } from 'events';
import type { Readable } from 'stream';
import { Ts3Client, type Ts3ClientOptions, generateIdentity, type IdentityData, buildCommand } from './tslib/index.js';
import { AudioPipeline, FRAME_MS, BYTES_PER_FRAME } from './audio/pipeline.js';
import { PlayQueue, type QueueItem } from './playlist/queue.js';
import { fetchIcyMetadata } from './audio/icy-metadata.js';
import { StreamSignaling, type ActiveStream, type SignalingMessage } from './streaming/stream-signaling.js';
import { SidecarClient } from './streaming/sidecar-client.js';
import { SidecarProcess, type SidecarConfig } from './streaming/sidecar-process.js';
import { STREAM_PRESETS, DEFAULT_PRESET, type VideoViewerInfo, type VideoStreamStatus } from './streaming/types.js';
import { getCookieArgs } from './audio/youtube.js';
import { spawn } from 'child_process';

/** Resolve a YouTube/yt-dlp-compatible URL to a direct stream URL */
function resolveVideoUrl(url: string, maxHeight: number = 720): Promise<string> {
  // Only resolve YouTube and other yt-dlp-supported sites
  if (!url.includes('youtube.com/') && !url.includes('youtu.be/') && !url.includes('twitch.tv/')) {
    return Promise.resolve(url);
  }

  return new Promise((resolve, reject) => {
    // Request best combined format (video+audio) up to the target height
    const formatFilter = `best[height<=${maxHeight}][ext=mp4]/best[height<=${maxHeight}]/best[ext=mp4]/best`;
    const proc = spawn('yt-dlp', [
      ...getCookieArgs(),
      '-f', formatFilter,
      '--no-playlist',
      '-g',  // print direct URL only
      url,
    ], { shell: false });

    let stdout = '';
    let stderr = '';
    proc.stdout.on('data', (chunk: Buffer) => { stdout += chunk.toString(); });
    proc.stderr.on('data', (chunk: Buffer) => { stderr += chunk.toString(); });

    proc.on('close', (code) => {
      if (code !== 0) {
        return reject(new Error(`yt-dlp failed (code ${code}): ${stderr.slice(0, 200)}`));
      }
      // yt-dlp -g returns the direct URL(s), take the first one
      const directUrl = stdout.trim().split('\n')[0];
      if (!directUrl) {
        return reject(new Error('yt-dlp returned no URL'));
      }
      console.log(`[VideoResolve] Resolved: ${url.substring(0, 60)}... → direct URL`);
      resolve(directUrl);
    });

    proc.on('error', (err) => {
      reject(new Error(`yt-dlp not found: ${err.message}`));
    });
  });
}

export type VoiceBotStatus = 'stopped' | 'starting' | 'connected' | 'playing' | 'paused' | 'error';

export interface PlaybackProgress {
  position: number;  // seconds
  duration: number;  // seconds
}

export interface VoiceBotConfig {
  id: number;
  serverConfigId: number;
  name: string;
  serverHost: string;
  serverPort: number;
  nickname: string;
  serverPassword?: string;
  defaultChannel?: string;
  channelPassword?: string;
  volume: number; // 0-100
  identity?: IdentityData;
  sidecarBinaryPath?: string;
  sidecarPort?: number;
  streamPreset?: string;
}

export class VoiceBot extends EventEmitter {
  private client: Ts3Client;
  private pipeline: AudioPipeline;
  readonly queue: PlayQueue;
  private config: VoiceBotConfig;
  private _status: VoiceBotStatus = 'stopped';
  private _lastError: string = '';
  private identity: IdentityData | null = null;
  private playbackTimer: ReturnType<typeof setTimeout> | null = null;
  private _nowPlaying: QueueItem | null = null;

  // File playback state — audio is decoded incrementally via ffmpeg and paced
  // out frame-by-frame instead of being fully buffered in memory up front
  // (a multi-hour track could otherwise need well over a gigabyte of PCM
  // before playback even started, which is enough to get OOM-killed).
  private fileStdout: Readable | null = null;
  private fileFramesSent: number = 0;
  private fileBaseSeconds: number = 0;
  private _fileStreamActive: boolean = false;
  private fileFfmpegEnded: boolean = false;
  private fileNextDue: number = 0;
  private fileStreamStartEpoch: number = 0;
  private loopEpoch: number = 0;

  private lastVoiceSendAt = 0;       // performance.now() timestamp
  private lastVoiceLogAt = 0;        // rate limit logs

  private statWindowStart = 0;
  private statCount = 0;
  private statDtSum = 0;
  private statDtMin = Number.POSITIVE_INFINITY;
  private statDtMax = 0;

  // Streaming state (radio)
  private _isStreaming: boolean = false;
  private streamKill: (() => void) | null = null;
  private streamChunks: Buffer[] = [];
  private streamChunksSize: number = 0;
  private streamStartTime: number = 0;

  // Nickname "now playing" state
  private _originalNickname: string;

  // ICY metadata polling (radio)
  private icyPollTimer: ReturnType<typeof setInterval> | null = null;
  private lastStreamTitle: string = '';

  // Reconnect: distinguishes manual stop from unexpected disconnect
  private _manuallyStopped: boolean = false;

  // Video streaming state
  private signaling: StreamSignaling | null = null;
  private sidecarProc: SidecarProcess | null = null;
  private sidecarHttp: SidecarClient | null = null;
  private _videoStreaming: boolean = false;
  private _activeStreamId: string | null = null;
  private _videoSource: string | null = null;
  private _videoPreset: string = DEFAULT_PRESET;
  private _videoFramerate: number = STREAM_PRESETS[DEFAULT_PRESET]?.framerate ?? 30;
  private _videoBitrate: string = STREAM_PRESETS[DEFAULT_PRESET]?.bitrate ?? '2500k';
  private _videoStartedAt: number | null = null;
  private _viewers: Map<number, VideoViewerInfo> = new Map();

  constructor(config: VoiceBotConfig) {
    super();
    this.config = config;
    this._originalNickname = config.nickname;
    this.client = new Ts3Client();
    this.pipeline = new AudioPipeline();
    this.queue = new PlayQueue();

    this.client.on('error', (err) => {
      this._status = 'error';
      this.emit('error', err);
      this.emit('statusChange', this._status);
    });

    this.client.on('disconnected', () => {
      this.stopIcyPolling();
      this.stopPlayback();
      this._status = 'stopped';
      this._nowPlaying = null;
      this.emit('statusChange', this._status);
      this.emit('disconnected');
    });

    this.client.on('ts3error', (params: Record<string, string>) => {
      const id = parseInt(params.id || '0');
      const msg = params.msg || 'unknown error';
      this._lastError = `TS3 error ${id}: ${msg}`;
      // Fatal errors that should not trigger reconnect
      // 2568 = invalid password, 3329 = banned, 1796 = max clients reached
      if (id === 2568 || id === 3329 || id === 1796) {
        this._status = 'error';
        this.emit('statusChange', this._status);
        this.emit('fatalError', this._lastError);
      }
    });

    this.client.on('command', (cmd) => {
      this.emit('command', cmd);
    });

    this.client.on('textMessage', (data: Record<string, string>) => {
      this.emit('textMessage', data);
    });
  }

  get id(): number {
    return this.config.id;
  }

  get status(): VoiceBotStatus {
    return this._status;
  }

  get nowPlaying(): QueueItem | null {
    return this._nowPlaying;
  }

  get isStreaming(): boolean {
    return this._isStreaming;
  }

  get manuallyStopped(): boolean {
    return this._manuallyStopped;
  }

  get playbackProgress(): PlaybackProgress | null {
    if (!this._nowPlaying) return null;
    if (this._isStreaming) {
      return {
        position: (Date.now() - this.streamStartTime) / 1000,
        duration: 0, // Live stream — no known duration
      };
    }
    if (!this._fileStreamActive) return null;
    return {
      position: this.fileBaseSeconds + (this.fileFramesSent * FRAME_MS) / 1000,
      duration: this._nowPlaying.duration ?? 0,
    };
  }

  get lastError(): string {
    return this._lastError;
  }

  get ts3ClientId(): number {
    return this.client.getClientId();
  }

  sendTextMessage(targetClid: number, msg: string): void {
    const cmd = buildCommand('sendtextmessage', {
      targetmode: 1,
      target: targetClid,
      msg,
    });
    this.client.sendCommand(cmd);
  }

  get currentConfig(): VoiceBotConfig {
    return { ...this.config };
  }

  updateConfig(partial: Partial<VoiceBotConfig>): void {
    Object.assign(this.config, partial);
    if (partial.nickname) this._originalNickname = partial.nickname;
  }

  /** Update the TS3 nickname to show what's playing. Max 30 chars. */
  private updateNowPlayingNickname(title: string): void {
    if (this._status === 'stopped') return;
    const prefix = this._originalNickname;
    const sep = ' \u266A '; // ♪
    const maxLen = 30;
    let nick = prefix + sep + title;
    if (nick.length > maxLen) {
      const available = maxLen - prefix.length - sep.length - 1; // -1 for …
      nick = prefix + sep + (available > 0 ? title.substring(0, available) + '\u2026' : '\u2026');
    }
    try {
      this.client.sendCommand(buildCommand('clientupdate', { client_nickname: nick }));
    } catch { }
  }

  /** Reset TS3 nickname to original. */
  private resetNickname(): void {
    if (this._status === 'stopped') return;
    try {
      this.client.sendCommand(buildCommand('clientupdate', { client_nickname: this._originalNickname }));
    } catch { }
  }

  /** Start polling ICY metadata for a radio stream. */
  private startIcyPolling(streamUrl: string): void {
    this.stopIcyPolling();
    this.lastStreamTitle = '';

    // Immediate first fetch
    this.fetchAndUpdateIcy(streamUrl);

    this.icyPollTimer = setInterval(() => {
      this.fetchAndUpdateIcy(streamUrl);
    }, 15000);
  }

  private async fetchAndUpdateIcy(streamUrl: string): Promise<void> {
    try {
      const title = await fetchIcyMetadata(streamUrl);
      if (!title || title === this.lastStreamTitle || !this._nowPlaying) return;
      this.lastStreamTitle = title;

      // Parse "Artist - Title" format
      const dashIdx = title.indexOf(' - ');
      if (dashIdx > 0) {
        this._nowPlaying.artist = title.substring(0, dashIdx).trim();
        this._nowPlaying.title = title.substring(dashIdx + 3).trim();
      } else {
        this._nowPlaying.title = title;
      }

      this.updateNowPlayingNickname(title);
      this.emit('metadataChange', this._nowPlaying);
    } catch { }
  }

  private stopIcyPolling(): void {
    if (this.icyPollTimer) {
      clearInterval(this.icyPollTimer);
      this.icyPollTimer = null;
    }
    this.lastStreamTitle = '';
  }

  async start(): Promise<void> {
    if (this._status === 'connected' || this._status === 'playing' || this._status === 'paused') {
      throw new Error('Bot is already running');
    }

    this._manuallyStopped = false;
    this._status = 'starting';
    this.emit('statusChange', this._status);

    this.identity = this.config.identity ?? generateIdentity(8);

    const opts: Ts3ClientOptions = {
      host: this.config.serverHost,
      port: this.config.serverPort,
      identity: this.identity,
      nickname: this.config.nickname,
      serverPassword: this.config.serverPassword,
      defaultChannel: this.config.defaultChannel,
      channelPassword: this.config.channelPassword,
    };

    await this.client.connect(opts);
    this._status = 'connected';
    this.emit('statusChange', this._status);
    this.emit('connected');
  }

  async stop(): Promise<void> {
    this._manuallyStopped = true;
    this.stopIcyPolling();
    this.resetNickname();
    this.stopPlayback();
    this._nowPlaying = null;
    // Stop video stream if active
    if (this._videoStreaming) {
      await this.stopVideoStream();
    }
    this.client.disconnect();
  }

  /** Force-close the underlying socket if still open, without triggering reconnect */
  ensureDisconnected(): void {
    this.client.forceClose();
  }

  async restart(): Promise<void> {
    await this.stop();
    await new Promise<void>((resolve) => {
      const check = () => {
        if (this._status === 'stopped') resolve();
        else setTimeout(check, 100);
      };
      setTimeout(check, 600);
    });
    await this.start();
  }

  async play(item: QueueItem): Promise<void> {
    if (this._status !== 'connected' && this._status !== 'playing' && this._status !== 'paused') {
      throw new Error('Bot is not connected');
    }

    this.stopIcyPolling();
    this.stopPlayback();
    this._nowPlaying = item;
    this._status = 'playing';
    this.emit('statusChange', this._status);
    this.emit('nowPlaying', item);
    this.updateNowPlayingNickname(item.title);

    try {
      await this.startFileStream(item.filePath, 0);
    } catch (err) {
      this._status = 'connected';
      this._nowPlaying = null;
      this.emit('statusChange', this._status);
      throw err;
    }
  }

  /** Start (or restart, e.g. after a seek) decoding a local file incrementally from startSeconds. */
  private async startFileStream(filePath: string, startSeconds: number): Promise<void> {
    const stream = await this.pipeline.toPcmFileStream(filePath, startSeconds);
    this.fileStreamStartEpoch = ++this.loopEpoch;
    const epoch = this.fileStreamStartEpoch;

    this.streamKill = stream.kill;
    this.fileStdout = stream.stdout;
    this.streamChunks = [];
    this.streamChunksSize = 0;
    this.fileBaseSeconds = startSeconds;
    this.fileFramesSent = 0;
    this.fileFfmpegEnded = false;
    this._fileStreamActive = true;

    stream.stdout.on('data', (chunk: Buffer) => {
      if (epoch !== this.loopEpoch) return;
      this.streamChunks.push(chunk);
      this.streamChunksSize += chunk.length;
    });

    stream.process.on('close', () => {
      if (epoch !== this.loopEpoch) return;
      this.fileFfmpegEnded = true;
    });

    stream.process.on('error', (err) => {
      if (epoch !== this.loopEpoch) return;
      this._fileStreamActive = false;
      this.streamKill = null;
      this.fileStdout = null;
      this._status = 'error';
      this.emit('error', err);
      this.emit('statusChange', this._status);
    });

    this.fileNextDue = performance.now() + 200; // initial buffer delay
    this.playbackTimer = setTimeout(this.fileTick, 200);
  }

  /** Resume the pacing tick after a pause, from the current buffer position (no re-seek/respawn). */
  private resumeFileStreamTick(): void {
    this.fileNextDue = performance.now() + FRAME_MS;
    this.playbackTimer = setTimeout(this.fileTick, FRAME_MS);
  }

  private fileTick = (): void => {
    if (this.fileStreamStartEpoch !== this.loopEpoch) return;

    const now = performance.now();

    // If we're early, wait until the next due time
    if (now < this.fileNextDue) {
      this.playbackTimer = setTimeout(this.fileTick, Math.max(1, this.fileNextDue - now));
      return;
    }

    // If we're behind, resync clock (no bursts)
    const lagMs = now - this.fileNextDue;
    if (lagMs >= FRAME_MS) {
      this.fileNextDue = now + FRAME_MS;
    }

    let frame = this.takeFromStreamChunks(BYTES_PER_FRAME);
    if (!frame && this.fileFfmpegEnded && this.streamChunksSize > 0) {
      // Drain the trailing partial frame instead of dropping the end of the track
      const raw = this.takeFromStreamChunks(this.streamChunksSize)!;
      const padded = Buffer.alloc(BYTES_PER_FRAME, 0);
      raw.copy(padded);
      frame = padded;
    }

    if (frame) {
      const opusFrame = this.pipeline.encodeFrame(frame, this.config.volume);
      this.sendVoiceFrame(opusFrame);
      this.fileFramesSent++;
    } else if (this.fileFfmpegEnded) {
      this.finishFileTrack();
      return;
    }

    // Next slot
    this.fileNextDue += FRAME_MS;

    // If we fell way behind, resync to avoid long "catch-up"
    if (now - this.fileNextDue > 5 * FRAME_MS) {
      this.fileNextDue = now + FRAME_MS;
    }

    const delay = this.fileNextDue - performance.now();
    if (delay > 2) {
      this.playbackTimer = setTimeout(this.fileTick, delay);
    } else {
      setImmediate(this.fileTick);
    }
  };

  private finishFileTrack(): void {
    this.client.sendVoiceStop();
    this.clearTimer();
    this._fileStreamActive = false;
    this.streamKill = null;
    this.fileStdout = null;

    const finished = this._nowPlaying;
    this._nowPlaying = null;
    this._status = 'connected';
    this.emit('statusChange', this._status);
    this.emit('trackEnd', finished);

    if (this.queue.repeat === 'track' && finished) {
      this.play(finished).catch((err) => this.emit('error', err));
      return;
    }

    const next = this.queue.next();
    if (next) this.play(next).catch((err) => this.emit('error', err));
    else this.resetNickname();
  }

  async playStream(item: QueueItem): Promise<void> {
    if (this._status !== 'connected' && this._status !== 'playing' && this._status !== 'paused') {
      throw new Error('Bot is not connected');
    }
    if (!item.streamUrl) {
      throw new Error('No streamUrl provided');
    }

    this.stopIcyPolling();
    this.stopPlayback();
    this._nowPlaying = item;
    this._isStreaming = true;
    this._status = 'playing';
    this.streamStartTime = Date.now();
    this.emit('statusChange', this._status);
    this.emit('nowPlaying', item);
    this.updateNowPlayingNickname(item.title);
    this.startIcyPolling(item.streamUrl);

    try {
      const stream = await this.pipeline.toPcmStream(item.streamUrl);
      this.streamKill = stream.kill;
      this.streamChunks = [];
      this.streamChunksSize = 0;

      const epoch = ++this.loopEpoch;
      let framesSent = 0;
      const startTime = performance.now();

      stream.stdout.on('data', (chunk: Buffer) => {
        if (epoch !== this.loopEpoch) return;
        this.streamChunks.push(chunk);
        this.streamChunksSize += chunk.length;
      });

      stream.process.on('close', () => {
        if (epoch !== this.loopEpoch) return;
        this.client.sendVoiceStop();
        this._isStreaming = false;
        this.streamKill = null;
        this._nowPlaying = null;
        this._status = 'connected';
        this.emit('statusChange', this._status);
        this.emit('trackEnd', item);
      });

      stream.process.on('error', (err) => {
        if (epoch !== this.loopEpoch) return;
        this._isStreaming = false;
        this.streamKill = null;
        this._status = 'error';
        this.emit('error', err);
        this.emit('statusChange', this._status);
      });

      let nextDue = performance.now() + 200; // initial buffer delay

      const tick = () => {
        if (epoch !== this.loopEpoch) return;

        const now = performance.now();

        // If we're early, wait until the next due time
        if (now < nextDue) {
          this.playbackTimer = setTimeout(tick, Math.max(1, nextDue - now));
          return;
        }

        // If we're behind, resync clock (no bursts)
        const lagMs = now - nextDue;
        if (lagMs >= FRAME_MS) {
          nextDue = now + FRAME_MS;
        }

        // Send exactly one frame if available
        const frame = this.takeFromStreamChunks(BYTES_PER_FRAME);
        if (frame) {
          const opusFrame = this.pipeline.encodeFrame(frame, this.config.volume);
          this.sendVoiceFrame(opusFrame);
        }

        // Next slot
        nextDue += FRAME_MS;

        // If we fell way behind, resync to avoid long "catch-up"
        if (now - nextDue > 5 * FRAME_MS) {
          nextDue = now + FRAME_MS;
        }

        const delay = nextDue - performance.now();

        if (delay > 2) {
          this.playbackTimer = setTimeout(tick, delay);
        } else {
          setImmediate(tick);
        }
      };

      this.playbackTimer = setTimeout(tick, 200);
    } catch (err) {
      this._isStreaming = false;
      this.streamKill = null;
      this._status = 'connected';
      this._nowPlaying = null;
      this.emit('statusChange', this._status);
      throw err;
    }
  }

  pause(): void {
    if (this._status !== 'playing') return;
    this.client.sendVoiceStop();
    if (this._fileStreamActive) {
      // Only cancel the pending tick — don't bump loopEpoch, so the same
      // ffmpeg process and its data/close/error listeners stay valid and
      // resume() can just continue from the current buffer position.
      if (this.playbackTimer) {
        clearTimeout(this.playbackTimer);
        this.playbackTimer = null;
      }
      this.fileStdout?.pause();
    } else {
      this.clearTimer();
    }
    this._status = 'paused';
    this.emit('statusChange', this._status);
  }

  resume(): void {
    if (this._status !== 'paused') return;
    if (this._fileStreamActive) {
      this._status = 'playing';
      this.emit('statusChange', this._status);
      this.fileStdout?.resume();
      this.resumeFileStreamTick();
    } else if (this._isStreaming && this._nowPlaying) {
      this._status = 'playing';
      this.emit('statusChange', this._status);
      // Live radio has no buffered position to resume from — rejoin the live stream.
      this.playStream(this._nowPlaying).catch((err) => this.emit('error', err));
    }
  }

  async seek(seconds: number): Promise<void> {
    if (this._status !== 'playing' && this._status !== 'paused') return;
    if (!this._fileStreamActive || !this._nowPlaying) return;

    const duration = this._nowPlaying.duration ?? Infinity;
    const target = Math.max(0, Math.min(seconds, duration));
    const wasPlaying = this._status === 'playing';
    const filePath = this._nowPlaying.filePath;

    // Tear down the current ffmpeg process/tick and spawn a fresh one at the seek point.
    // (startFileStream() below overwrites fileStdout/streamKill/_fileStreamActive itself.)
    this.clearTimer();
    if (this.streamKill) {
      this.streamKill();
      this.streamKill = null;
    }
    this._fileStreamActive = false;

    await this.startFileStream(filePath, target);

    if (!wasPlaying) {
      // Stay paused at the new position instead of auto-resuming playback.
      if (this.playbackTimer) {
        clearTimeout(this.playbackTimer);
        this.playbackTimer = null;
      }
      this.fileStdout?.pause();
    }
  }

  setVolume(volume: number): void {
    this.config.volume = Math.max(0, Math.min(100, volume));
    this.emit('volumeChange', this.config.volume);
  }

  skip(): void {
    this.stopIcyPolling();
    this.stopPlayback();
    this._nowPlaying = null;
    this._status = 'connected';
    this.emit('statusChange', this._status);

    const next = this.queue.next();
    if (next) {
      this.play(next).catch((err) => this.emit('error', err));
    } else {
      this.resetNickname();
    }
  }

  previous(): void {
    this.stopIcyPolling();
    this.stopPlayback();
    this._nowPlaying = null;
    this._status = 'connected';
    this.emit('statusChange', this._status);

    const prev = this.queue.previous();
    if (prev) {
      this.play(prev).catch((err) => this.emit('error', err));
    } else {
      this.resetNickname();
    }
  }

  stopAudio(): void {
    this.stopIcyPolling();
    this.stopPlayback();
    this.client.sendVoiceStop();
    this._nowPlaying = null;
    this.resetNickname();
    if (this._status === 'playing' || this._status === 'paused') {
      this._status = 'connected';
      this.emit('statusChange', this._status);
    }
  }

  private takeFromStreamChunks(n: number): Buffer | null {
    if (this.streamChunksSize < n) return null;

    const out = Buffer.allocUnsafe(n);
    let offset = 0;

    while (offset < n) {
      const head = this.streamChunks[0];
      const need = n - offset;

      if (head.length <= need) {
        head.copy(out, offset);
        offset += head.length;
        this.streamChunks.shift();
      } else {
        head.copy(out, offset, 0, need);
        this.streamChunks[0] = head.subarray(need);
        offset += need;
      }
    }

    this.streamChunksSize -= n;
    return out;
  }

  private sendVoiceFrame(opusFrame: Buffer): void {
    const now = performance.now();
    const dt = this.lastVoiceSendAt ? (now - this.lastVoiceSendAt) : 0;
    this.lastVoiceSendAt = now;

    const VOICE_DEBUG = process.env.VOICE_DEBUG === '1';

    if (VOICE_DEBUG) {
      // 1s stats
      if (!this.statWindowStart) this.statWindowStart = now;
      if (dt > 0) {
        this.statCount++;
        this.statDtSum += dt;
        this.statDtMin = Math.min(this.statDtMin, dt);
        this.statDtMax = Math.max(this.statDtMax, dt);
      }

      if (now - this.statWindowStart >= 1000) {
        const avg = this.statCount ? (this.statDtSum / this.statCount) : 0;
        console.log(
          `[voice] rate=${this.statCount}/s avg=${avg.toFixed(1)}ms min=${this.statDtMin.toFixed(1)} max=${this.statDtMax.toFixed(1)} streaming=${this._isStreaming}`
        );
        this.statWindowStart = now;
        this.statCount = 0;
        this.statDtSum = 0;
        this.statDtMin = Number.POSITIVE_INFINITY;
        this.statDtMax = 0;
      }
    }

    this.client.sendVoice(opusFrame);
  }

  private clearTimer(): void {
    this.loopEpoch++;
    if (this.playbackTimer) {
      clearTimeout(this.playbackTimer);
      this.playbackTimer = null;
    }
  }

  private stopPlayback(): void {
    this.clearTimer();
    this._fileStreamActive = false;
    this.fileStdout = null;
    this.fileFramesSent = 0;
    this.fileBaseSeconds = 0;
    this.fileFfmpegEnded = false;

    // Kill streaming FFmpeg if active
    if (this.streamKill) {
      this.streamKill();
      this.streamKill = null;
    }
    this._isStreaming = false;
    this.streamChunks = [];
    this.streamChunksSize = 0;
  }

  // ─── Video Streaming ────────────────────────────────────────

  get videoStreaming(): boolean {
    return this._videoStreaming;
  }

  get videoStreamStatus(): VideoStreamStatus {
    return {
      streaming: this._videoStreaming,
      streamId: this._activeStreamId,
      source: this._videoSource,
      preset: this._videoPreset,
      framerate: this._videoFramerate,
      bitrate: this._videoBitrate,
      startedAt: this._videoStartedAt,
      viewerCount: this._viewers.size,
      viewers: Array.from(this._viewers.values()),
      sidecar: null,
    };
  }

  /** Start video streaming to TS6 via WebRTC */
  async startVideoStream(source: string, preset?: string, framerate?: number, bitrate?: string): Promise<void> {
    if (this._status !== 'connected' && this._status !== 'playing' && this._status !== 'paused') {
      throw new Error('Bot is not connected');
    }
    if (this._videoStreaming) {
      throw new Error('Video stream already active');
    }

    const sidecarBinary = this.config.sidecarBinaryPath || process.env.SIDECAR_BINARY_PATH || 'sidecar';
    const sidecarPort = this.config.sidecarPort || 9800;
    this._videoPreset = preset ?? this.config.streamPreset ?? DEFAULT_PRESET;
    const presetConfig = STREAM_PRESETS[this._videoPreset] || STREAM_PRESETS[DEFAULT_PRESET];
    const effectiveFramerate = framerate && framerate > 0
      ? framerate
      : presetConfig.framerate;
    const effectiveBitrate = bitrate?.trim()
      ? bitrate.trim()
      : presetConfig.bitrate;

    this._videoFramerate = effectiveFramerate;
    this._videoBitrate = effectiveBitrate;

    // Check if sidecar URL is set (Docker mode — sidecar runs as separate container)
    const sidecarUrl = process.env.SIDECAR_URL;

    if (sidecarUrl) {
      // Docker mode: sidecar is an external service, don't spawn it
      this.sidecarHttp = new SidecarClient(sidecarUrl);
    } else {
      // Local mode: spawn sidecar binary
      const sidecarConfig: SidecarConfig = {
        binaryPath: sidecarBinary,
        port: sidecarPort,
        videoBitrate: effectiveBitrate,
        videoResolution: { width: presetConfig.width, height: presetConfig.height },
        videoFramerate: effectiveFramerate,
      };

      this.sidecarProc = new SidecarProcess(sidecarConfig);
      this.sidecarProc.on('exited', (code: number | null) => {
        console.log(`[VoiceBot ${this.config.id}] Sidecar exited (code=${code})`);
        if (this._videoStreaming) {
          this._videoStreaming = false;
          this._activeStreamId = null;
          this._viewers.clear();
          this.emit('videoStreamStopped');
          this.emit('statusChange', this._status);
        }
      });
      try {
        this.sidecarProc.start();
      } catch (err: any) {
        this.sidecarProc = null;
        throw new Error(`Failed to start sidecar: ${err.message}`);
      }
      this.sidecarHttp = new SidecarClient(sidecarPort);
    }

    // Wait for sidecar to be healthy
    await this.sidecarHttp.waitHealthy();
    console.log(`[VoiceBot ${this.config.id}] Sidecar ready`);

    // Setup stream signaling on the TS3 client
    this.signaling = new StreamSignaling(this.client);
    this.setupSignalingListeners();
    this.signaling.registerStreamNotifications();

    // Wait for server to confirm stream
    const streamPromise = new Promise<ActiveStream>((resolve, reject) => {
      const timeout = setTimeout(() => reject(new Error('setupstream timeout')), 10000);
      const handler = (stream: ActiveStream) => {
        if (stream.clid === this.client.getClientId()) {
          clearTimeout(timeout);
          this.signaling!.removeListener('streamStarted', handler);
          resolve(stream);
        }
      };
      this.signaling!.on('streamStarted', handler);
    });

    // Send setupstream command
    this.signaling.sendSetupStream({
      name: `${this.config.nickname} Stream`,
      type: 3,
      bitrate: 4608,
      accessibility: 1,
      mode: 1,
      viewerLimit: 0,
      audio: true,
    });

    const stream = await streamPromise;
    this._activeStreamId = stream.id;
    this._videoStreaming = true;
    this._videoSource = source;
    this._videoStartedAt = Date.now();

    // Resolve YouTube/streaming URLs via yt-dlp, then start ffmpeg
    const resolvedSource = await resolveVideoUrl(source, presetConfig.height);
    await this.sidecarHttp.setSource(
      resolvedSource,
      presetConfig.width,
      presetConfig.height,
      effectiveFramerate,
      effectiveBitrate,
    );

    console.log(`[VoiceBot ${this.config.id}] Video stream started: ${stream.id}, source: ${source}`);
    this.emit('videoStreamStarted', { streamId: stream.id, source, preset: this._videoPreset });
    this.emit('statusChange', this._status);
  }

  /** Stop video streaming */
  async stopVideoStream(): Promise<void> {
    if (!this._videoStreaming) return;

    // Remove all viewers from TS6 stream first
    if (this.signaling && this._activeStreamId) {
      for (const [clid] of this._viewers) {
        this.signaling.sendRemoveClient(clid, this._activeStreamId);
      }
    }

    // Stop ffmpeg and close WebRTC peers
    try { await this.sidecarHttp?.stopSource(); } catch { /* ignore */ }
    for (const [clid] of this._viewers) {
      try { await this.sidecarHttp?.closePeer(String(clid)); } catch { /* ignore */ }
    }
    this._viewers.clear();

    // Stop TS6 stream
    if (this.signaling && this._activeStreamId) {
      console.log(`[VoiceBot ${this.config.id}] Sending stopstream: ${this._activeStreamId}`);
      this.signaling.sendStreamStop(this._activeStreamId);
    }

    // Wait for the stopstream command to be sent and ACKed over UDP
    await new Promise((r) => setTimeout(r, 1000));

    // Stop sidecar process (only in local mode)
    if (this.sidecarProc) {
      await this.sidecarProc.stop();
      this.sidecarProc = null;
    }

    this._activeStreamId = null;
    this._videoSource = null;
    this._videoStreaming = false;
    this._videoStartedAt = null;
    this.signaling = null;

    console.log(`[VoiceBot ${this.config.id}] Video stream stopped`);
    this.emit('videoStreamStopped');
    this.emit('statusChange', this._status);
  }

  /** Change video source while streaming */
  async setVideoSource(source: string): Promise<void> {
    if (!this._videoStreaming || !this.sidecarHttp) {
      throw new Error('No active video stream');
    }
    this._videoSource = source;
    const currentPreset = STREAM_PRESETS[this._videoPreset] || STREAM_PRESETS[DEFAULT_PRESET];
    const resolvedSource = await resolveVideoUrl(source, currentPreset.height);

    await this.sidecarHttp.setSource(
      resolvedSource,
      currentPreset.width,
      currentPreset.height,
      this._videoFramerate,
      this._videoBitrate,
    );
    console.log(`[VoiceBot ${this.config.id}] Video source changed: ${source}`);
    this.emit('videoSourceChanged', source);
  }

  /** Kick a viewer from the video stream */
  async kickVideoViewer(clid: number): Promise<void> {
    if (!this._videoStreaming || !this.signaling || !this._activeStreamId) {
      throw new Error('No active video stream');
    }
    try { await this.sidecarHttp?.closePeer(String(clid)); } catch { /* ignore */ }
    this.signaling.sendRemoveClient(clid, this._activeStreamId);
    this._viewers.delete(clid);
    this.emit('videoViewerLeft', clid);
  }

  /** Get WebRTC offer for WebUI preview player */
  async getWebRtcOffer(): Promise<{ sdp: string } | null> {
    if (!this._videoStreaming || !this.sidecarHttp) return null;
    return this.sidecarHttp.createPeer('webui-preview');
  }

  /** Set WebRTC answer from WebUI preview player */
  async setWebRtcAnswer(sdp: string): Promise<void> {
    if (!this.sidecarHttp) throw new Error('No sidecar');
    await this.sidecarHttp.setAnswer('webui-preview', sdp);
  }

  /** Add ICE candidate from WebUI preview player */
  async addWebRtcIceCandidate(candidate: string, sdpMid: string, sdpMLineIndex: number): Promise<void> {
    if (!this.sidecarHttp) throw new Error('No sidecar');
    await this.sidecarHttp.addIceCandidate('webui-preview', candidate, sdpMid, sdpMLineIndex);
  }

  private setupSignalingListeners(): void {
    if (!this.signaling) return;

    this.signaling.on('signalingMessage', (msg: SignalingMessage) => {
      this.handleSignalingMessage(msg);
    });

    this.signaling.on('joinStreamRequest', (params: Record<string, string>) => {
      const viewerClid = parseInt(params.clid) || 0;
      const streamId = params.id || this._activeStreamId;
      if (!streamId || !viewerClid) return;
      console.log(`[VoiceBot ${this.config.id}] Viewer join request: clid=${viewerClid}`);
      this.handleViewerJoin(viewerClid, streamId);
    });

    this.signaling.on('streamClientLeft', (params: Record<string, string>) => {
      const clid = parseInt(params.clid) || 0;
      if (this._viewers.has(clid)) {
        console.log(`[VoiceBot ${this.config.id}] Viewer left: clid=${clid}`);
        this.sidecarHttp?.closePeer(String(clid)).catch(() => { });
        this._viewers.delete(clid);
        this.emit('videoViewerLeft', clid);
      }
    });
  }

  private async handleSignalingMessage(msg: SignalingMessage): Promise<void> {
    if (!this.sidecarHttp) return;

    switch (msg.type) {
      case 'answer':
        if (msg.sdp && msg.clid) {
          try {
            await this.sidecarHttp.setAnswer(String(msg.clid), msg.sdp);
          } catch (err: any) {
            console.error(`[VoiceBot ${this.config.id}] setAnswer error (clid=${msg.clid}): ${err.message}`);
          }
        }
        break;
      case 'ice_candidate':
        if (msg.candidate && msg.clid) {
          try {
            await this.sidecarHttp.addIceCandidate(
              String(msg.clid),
              msg.candidate,
              msg.sdpMid || '0',
              msg.sdpMlineIndex ?? 0
            );
          } catch (err: any) {
            console.error(`[VoiceBot ${this.config.id}] addIceCandidate error (clid=${msg.clid}): ${err.message}`);
          }
        }
        break;
      case 'reconnect':
        if (msg.clid && this._activeStreamId) {
          console.log(`[VoiceBot ${this.config.id}] Reconnect from clid=${msg.clid}`);
          try { await this.sidecarHttp.closePeer(String(msg.clid)); } catch { /* ignore */ }
          this._viewers.delete(msg.clid);
          await this.handleViewerJoin(msg.clid, this._activeStreamId);
        }
        break;
    }
  }

  private async handleViewerJoin(viewerClid: number, streamId: string): Promise<void> {
    if (!this.sidecarHttp || !this.signaling) return;

    try {
      if (this._viewers.has(viewerClid)) {
        try { await this.sidecarHttp.closePeer(String(viewerClid)); } catch { /* ignore */ }
      }

      const result = await this.sidecarHttp.createPeer(String(viewerClid));

      const viewer: VideoViewerInfo = {
        clid: viewerClid,
        joinedAt: Date.now(),
        iceState: 'new',
      };
      this._viewers.set(viewerClid, viewer);

      this.signaling.sendJoinResponse(viewerClid, streamId, true, result.sdp);
      console.log(`[VoiceBot ${this.config.id}] Viewer accepted: clid=${viewerClid} (${this._viewers.size} total)`);
      this.emit('videoViewerJoined', viewer);
    } catch (err: any) {
      console.error(`[VoiceBot ${this.config.id}] handleViewerJoin error (clid=${viewerClid}): ${err.message}`);
      this._viewers.delete(viewerClid);
    }
  }
}
