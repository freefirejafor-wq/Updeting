import { ALL_CATEGORIES, INITIAL_FALLBACK_MOVIES } from '../data/categories';
import {
  cleanTimeAgoAndEpisode,
  deduplicateMovieCards,
  getCanonicalTitleKey,
  getItemMinutesAgo,
  normalizeMovieCardItem,
  normalizeMovieCardList,
  sortItemsByHighRating,
  sortItemsByHotAndHype,
  sortItemsByRecentUpload,
} from '../utils/timeAgo';
import type {
  CastMember,
  DirectDownloadButton,
  EpisodeItem,
  GlobalMovieNotification,
  MovieCardItem,
  MovieDetailData,
  StreamSource,
} from '../types/cinema';
import { prewarmMkvStreamMeta } from './mkvIosClientRemuxer';

const MIRROR_ORIGINS = [
  'https://cmyyhb.movielinkbd.at',
  'https://4yer8f.movielinkbd.at',
];

const CORS_BRIDGES = [
  (targetUrl: string) =>
    `https://allorigins.hexlet.app/raw?url=${encodeURIComponent(targetUrl)}`,
];

interface StaticDbSnapshot {
  generatedAt: number;
  catalogs: Record<string, MovieCardItem[]>;
  details: Record<string, MovieDetailData>;
}

let staticDbPromise: Promise<StaticDbSnapshot | null> | null = null;
let loadedStaticDb: StaticDbSnapshot | null = null;
const staticDbTitleIndex = new Map<string, MovieDetailData>();
const clientCatalogCache = new Map<string, { items: MovieCardItem[]; maxPage: number; ts: number }>();
const clientDetailCache = new Map<string, { detail: MovieDetailData; ts: number }>();
const inFlightDetailPromises = new Map<string, Promise<any>>();
const bgPrefetchControllers = new Set<AbortController>();
let isVideoActivelyStarting = false;

export function setVideoStartupPriority(active: boolean): void {
  isVideoActivelyStarting = active;
  if (active) {
    stopBackgroundWarmVideo();
    for (const ctrl of bgPrefetchControllers) {
      try {
        ctrl.abort();
      } catch {
        // ignore
      }
    }
    bgPrefetchControllers.clear();
  }
}

function normalizeLookupTitleKey(rawTitle: string): string {
  const canon = getCanonicalTitleKey(rawTitle || '');
  if (canon) return canon;
  return (rawTitle || '')
    .replace(/\[.*?\]|\(.*?\)/g, ' ')
    .replace(
      /\b(?:S\d+|Season\s*\d+(?:-\d+)?|Ep(?:isode)?\s*\d+(?:-\d+)?|Complete(?:d)?|Added|Full\s*HD|ORG|Hindi|Bangla|Bengali|Dual|Multi|Audio|The\s*Movie)\b/gi,
      ' '
    )
    .toLowerCase()
    .replace(/[^a-z0-9\u0980-\u09ff]+/g, '')
    .trim();
}

function legacyNormalizeLookupTitleKey(rawTitle: string): string {
  return (rawTitle || '')
    .replace(/\[.*?\]|\(.*?\)/g, ' ')
    .replace(
      /\b(?:S\d+|Season\s*\d+(?:-\d+)?|Ep(?:isode)?\s*\d+(?:-\d+)?|Complete(?:d)?|Added|Full\s*HD|ORG|Hindi|Bangla|Bengali|Dual|Multi|The\s*Movie)\b/gi,
      ' '
    )
    .toLowerCase()
    .replace(/[^a-z0-9\u0980-\u09ff]+/g, '')
    .trim();
}

const loadedShards = new Set<string>();
const inFlightShards = new Map<string, Promise<void>>();

function computeShardHex(str: string): string {
  const s = String(str || '').toLowerCase().trim();
  let h = 2166136261 >>> 0;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 16777619) >>> 0;
  }
  return (h & 0x0f).toString(16);
}

function sortEpisodeSourcesFastestFirst(sources?: StreamSource[]): StreamSource[] {
  if (!Array.isArray(sources) || sources.length <= 1) return sources || [];
  const score = (src: StreamSource) => {
    const isEmbed =
      src.type === 'embed' || /abyssplayer\.com|abysscdn\.com|myflix/i.test(`${src.url || ''} ${src.id || ''}`);
    if (isEmbed) return 100;
    const isMovieBox =
      src.id?.startsWith('mb-') || /\/api\/mb-stream|\/api\/mb-ep-stream/i.test(src.url || '');
    if (isMovieBox) {
      const szMatch = (src.name || '').match(/(\d+)\s*MB/i);
      const szMb = szMatch ? parseInt(szMatch[1], 10) : 0;
      const isHeavy = szMb > 350;
      if (src.quality === 720) return 4650;
      if (src.quality === 480) return 4640;
      if (src.quality === 360) return 4620;
      if (src.quality === 1080) return isHeavy ? 4550 : 4630;
      return 4500;
    }
    const isHevc = /\b(hevc|h\.?265|x265|10bit|av1)\b/i.test(`${src.name} ${src.qualityLabel}`);
    const isBestHeavy = /best\s*quality/i.test(src.qualityLabel || '');
    let s = isHevc ? 200 : 1000;
    if (isBestHeavy) s -= 250;
    if (src.quality >= 360 && src.quality <= 576) s += 650;
    else if (src.quality === 720) s += 500;
    else if (src.quality === 1080) s += 350;
    else s += 150;
    return s;
  };
  return [...sources].sort((a, b) => score(b) - score(a));
}

function indexDetailsIntoMemory(detailsMap?: Record<string, MovieDetailData>, isFromLiveApi = false): void {
  if (!detailsMap || !isFromLiveApi) return;
  if (!loadedStaticDb) {
    loadedStaticDb = { generatedAt: Date.now(), catalogs: {}, details: {} };
  }
  for (const [detPath, det] of Object.entries(detailsMap)) {
    if (det?.title && det.episodes?.length) {
      for (const ep of det.episodes) {
        for (const src of ep.sources || []) {
          if (!src.downloadUrl) {
            src.downloadUrl = src.url;
          } else if (src.downloadUrl.startsWith('/api/go?t=')) {
            src.downloadUrl = resolveDirectDownloadUrl(src.downloadUrl);
          }
        }
        ep.sources = sortEpisodeSourcesFastestFirst(ep.sources);
      }
      for (const btn of det.downloadButtons || []) {
        if (btn.url && btn.url.startsWith('/api/go?t=')) {
          btn.url = resolveDirectDownloadUrl(btn.url);
        }
      }
      loadedStaticDb.details[detPath] = det;
      const k1 = normalizeLookupTitleKey(det.title);
      if (k1) staticDbTitleIndex.set(k1, det);
      const kLegacy = legacyNormalizeLookupTitleKey(det.title);
      if (kLegacy) staticDbTitleIndex.set(kLegacy, det);
      const k2 = det.title.toLowerCase().replace(/[^a-z0-9]/g, '');
      if (k2) staticDbTitleIndex.set(k2, det);
    }
  }
}

async function loadShardByHex(_hex: string): Promise<void> {
  // Static shards contain time-limited stream URLs that expire; always resolve streams live via /api/details
  return;
}

export async function loadShardForMovie(rawPath: string, rawTitle: string): Promise<MovieDetailData | null> {
  return getInstantCachedDetail(rawPath, rawTitle);
}

async function loadStaticDb(): Promise<StaticDbSnapshot | null> {
  if (loadedStaticDb && Object.keys(loadedStaticDb.catalogs || {}).length > 0) {
    return loadedStaticDb;
  }
  if (!staticDbPromise) {
    staticDbPromise = (async () => {
      try {
        const res = await fetch('./static-db.json');
        if (!res.ok) return null;
        const parsed = (await res.json()) as StaticDbSnapshot;
        if (!loadedStaticDb) {
          loadedStaticDb = { generatedAt: parsed.generatedAt || Date.now(), catalogs: parsed.catalogs || {}, details: {} };
        } else {
          loadedStaticDb.catalogs = parsed.catalogs || {};
        }
        if (parsed?.details) {
          indexDetailsIntoMemory(parsed.details, false);
        }
        return loadedStaticDb;
      } catch {
        return null;
      }
    })();
  }
  return staticDbPromise;
}

// Preconnect video CDNs on startup without loading heavy static files when running on the live API server!
if (typeof window !== 'undefined') {
  ensurePreconnectOrigin('https://fsldownload.com');
  ensurePreconnectOrigin('https://bcdnxw.hakunaymatata.com');
  if (window.location.hostname.endsWith('github.io')) {
    loadStaticDb().catch(() => {});
  }
}

export function resolveDirectDownloadUrl(rawUrl: string): string {
  if (!rawUrl) return '';
  if (rawUrl.startsWith('/api/go?t=')) {
    try {
      const token = rawUrl.slice('/api/go?t='.length).split('&')[0];
      const base64 = token.replace(/-/g, '+').replace(/_/g, '/');
      const padded = base64 + '==='.slice((base64.length + 3) % 4);
      const decoded = decodeURIComponent(escape(window.atob(padded)));
      if (/fifadekho\.com/i.test(decoded)) {
        const isGhPages =
          typeof window !== 'undefined' && window.location.hostname.endsWith('github.io');
        return isGhPages
          ? `${decoded.replace(/\/+$/, '')}?view=links`
          : rawUrl;
      }
      return decoded;
    } catch {
      return rawUrl;
    }
  }
  return rawUrl;
}

function sanitizeBrandText(input: string): string {
  if (!input) return '';
  return String(input)
    .replace(/https?:\/\/[^\s"'<>]*(?:movielinkbd|myflixbd)[^\s"'<>]*/gi, '')
    .replace(/\b[a-z0-9-]*\.?(?:movielinkbd|myflixbd)\.[a-z]{2,6}\b/gi, 'CinePulse')
    .replace(/movielinkbd|myflixbd|nexaflox/gi, 'CinePulse')
    .replace(/movie\s*link\s*bd/gi, 'CinePulse')
    .replace(/\bmlbd\b/gi, 'CP')
    .replace(/\s*watch\s+online\s+and\s+download\s*(?:["“”']?web-dl["“”']?|["“”']?hdtc["“”']?|["“”']?hd["“”']?|["“”']?4k["“”']?)?\s*…?/gi, '')
    .replace(/\s*watch\s+online\s*…?/gi, '')
    .replace(/\s*[“”"'](?:web(?:-?dl|rip)?|hdtc|hdts|4k|hd)[^"”]*[”"']?\s*…?\s*$/gi, '')
    .replace(/\s+[–—-]\s*$/g, '')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

function decodeHtmlEntities(str: string): string {
  const cleaned = (str || '')
    .replace(/&ndash;|&#8211;/g, '–')
    .replace(/&mdash;|&#8212;/g, '—')
    .replace(/&#039;|&#8217;/g, "'")
    .replace(/&quot;|&#8220;|&#8221;/g, '"')
    .replace(/&amp;|&#038;/g, '&')
    .replace(/&bull;|&#8226;/g, '•')
    .replace(/&#8230;|&hellip;/g, '')
    .replace(/&nbsp;/g, ' ')
    .replace(/<[^>]+>/g, '')
    .trim();
  return sanitizeBrandText(cleaned);
}

/**
 * Browser-native implementation of the stream & download cipher decoder.
 */
function decodeMlbdCipherBrowser(base64Str: string, hexSeed: string, rounds: number): string {
  try {
    let x = parseInt(hexSeed, 16) >>> 0;
    for (let i = 0; i < rounds; i++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
    }
    const cleanB64 = base64Str.trim().replace(/\s+/g, '');
    const binary = window.atob(cleanB64);
    const out = new Uint8Array(binary.length);
    for (let j = 0; j < binary.length; j++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
      out[j] = binary.charCodeAt(j) ^ ((x >>> 16) & 255);
    }
    return new TextDecoder('utf-8').decode(out);
  } catch {
    return '';
  }
}

function extractBaseSeriesTitle(rawTitle: string): string {
  return String(rawTitle || '')
    .replace(/\[.*?\]|\(.*?\)/g, ' ')
    .replace(
      /\b(?:S\d+|Season\s*\d+(?:-\d+)?|Ep(?:isode)?\s*\d+(?:-\d+)?|Complete(?:d)?|Added|Full\s*HD|ORG|Hindi|Bangla|Bengali|Dual|Multi|The\s*Movie)\b/gi,
      ' '
    )
    .replace(/[:\-–—|]+/g, ' ')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

const warmedStreamUrls = new Set<string>();
const preconnectedOrigins = new Set<string>();
let warmVideoEl: HTMLVideoElement | null = null;
let hasPrimedHardwareDecoder = false;

function isAppleSafariDevice(): boolean {
  if (typeof window === 'undefined' || typeof navigator === 'undefined') return false;
  const ua = navigator.userAgent || '';
  const isIOS =
    /iPhone|iPad|iPod/i.test(ua) ||
    (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
  const isSafari = /Safari/i.test(ua) && !/Chrome|Chromium|Edg|OPR|Android/i.test(ua);
  return isIOS || isSafari;
}

function ensurePreconnectOrigin(streamUrl: string): void {
  if (typeof document === 'undefined') return;
  try {
    const origin = new URL(streamUrl).origin;
    if (!origin || preconnectedOrigins.has(origin)) return;
    preconnectedOrigins.add(origin);

    const dnsLink = document.createElement('link');
    dnsLink.rel = 'dns-prefetch';
    dnsLink.href = origin;
    document.head.appendChild(dnsLink);

    // 1. Non-CORS preconnect for native <video src="..."> socket pool on Android/Chrome
    const mediaLink = document.createElement('link');
    mediaLink.rel = 'preconnect';
    mediaLink.href = origin;
    document.head.appendChild(mediaLink);

    // 2. Anonymous CORS preconnect for fetch() / iOS remuxer socket pool
    const corsLink = document.createElement('link');
    corsLink.rel = 'preconnect';
    corsLink.href = origin;
    corsLink.crossOrigin = 'anonymous';
    document.head.appendChild(corsLink);

    // Immediately warm the no-cors TLS/HTTP2 socket to the video CDN
    fetch(origin, { mode: 'no-cors', priority: 'high' as any }).catch(() => {});
  } catch {
    // ignore
  }
}

/**
 * Warms DNS, TCP, and TLS handshakes to the video CDN origin AND initializes the browser's
 * hardware video decoder once on page boot so the 1st movie click starts as fast as the 2nd+ click.
 */
export function warmStreamConnection(streamUrl?: string, primeMediaDecoder = false): void {
  if (!streamUrl || typeof window === 'undefined') return;
  if (!streamUrl.startsWith('http')) return;
  ensurePreconnectOrigin(streamUrl);
  if (!isVideoActivelyStarting && primeMediaDecoder && !warmedStreamUrls.has(streamUrl)) {
    warmedStreamUrls.add(streamUrl);
    if (isAppleSafariDevice()) {
      prewarmMkvStreamMeta(streamUrl);
    } else if (!hasPrimedHardwareDecoder && typeof document !== 'undefined') {
      // One-time background hardware video decoder & <video> media socket warmup on Android/Desktop
      // before the user clicks their 1st movie! Stops automatically as soon as metadata is ready.
      hasPrimedHardwareDecoder = true;
      try {
        const v = document.createElement('video');
        v.muted = true;
        v.playsInline = true;
        v.preload = 'metadata';
        v.style.position = 'fixed';
        v.style.width = '1px';
        v.style.height = '1px';
        v.style.opacity = '0';
        v.style.pointerEvents = 'none';
        v.style.left = '-9999px';
        warmVideoEl = v;
        const cleanupWarm = () => {
          stopBackgroundWarmVideo();
        };
        v.addEventListener('loadedmetadata', cleanupWarm, { once: true });
        v.addEventListener('error', cleanupWarm, { once: true });
        v.src = streamUrl;
        v.load();
        window.setTimeout(cleanupWarm, 1100);
      } catch {
        // ignore
      }
    }
  }
}

export function stopBackgroundWarmVideo(): void {
  if (warmVideoEl) {
    try {
      warmVideoEl.pause();
      warmVideoEl.removeAttribute('src');
      warmVideoEl.load();
      warmVideoEl.remove();
    } catch {
      // ignore
    }
    warmVideoEl = null;
  }
}

function warmDetailFirstStream(detail?: MovieDetailData | null, primeMediaDecoder = false): void {
  const firstEp = detail?.episodes?.[0];
  if (!firstEp?.sources?.length) return;
  const isNonHevc = (s: StreamSource) =>
    !/\b(hevc|h\.?265|x265|10bit|av1)\b/i.test(`${s.name} ${s.qualityLabel}`) &&
    !/best\s*quality/i.test(s.qualityLabel || '');
  // Always pre-warm the fastest starting 480p or 720p H.264 stream first!
  const bestFast =
    firstEp.sources.find((s) => isNonHevc(s) && s.quality >= 360 && s.quality <= 576) ||
    firstEp.sources.find((s) => isNonHevc(s) && s.quality === 720) ||
    firstEp.sources.find((s) => isNonHevc(s)) ||
    firstEp.sources[0];
  if (bestFast?.url && bestFast.type !== 'embed') {
    warmStreamConnection(bestFast.url, primeMediaDecoder);
  }
}

/**
 * Synchronous 0ms detail lookup from in-memory cache or pre-loaded static-db.json
 * so clicking a movie opens the video player immediately without any loading spinner!
 */
export function getInstantCachedDetail(rawPath: string, rawTitle = ''): MovieDetailData | null {
  const pathKey = (rawPath || '').trim();
  if (!pathKey && !rawTitle) return null;

  const mem = clientDetailCache.get(pathKey);
  // Only use in-memory detail cache if fetched within the last 12 minutes so stream tokens never expire
  if (mem && Date.now() - mem.ts < 12 * 60_000 && mem.detail?.episodes?.length) {
    return mem.detail;
  }

  if (loadedStaticDb?.details?.[pathKey]?.episodes?.length) {
    return loadedStaticDb.details[pathKey];
  }

  if (rawTitle) {
    const k1 = normalizeLookupTitleKey(rawTitle);
    const byK1 = k1 ? staticDbTitleIndex.get(k1) : undefined;
    if (byK1 && byK1.episodes?.length) return byK1;
  }

  return null;
}

/**
 * Pre-loads the static shard OR live /api/details on hover/touchstart and preconnects
 * the video CDN origin so clicking Play opens and starts playing in 0ms on the very first click!
 */
export function prefetchMovieDetails(
  rawPath: string,
  rawTitle = '',
  nodeId = 'node-alpha',
  primeMediaDecoder = false
): void {
  if (isVideoActivelyStarting) return;
  const pathKey = (rawPath || '').trim();
  if (!pathKey && !rawTitle) return;

  const existing = getInstantCachedDetail(pathKey, rawTitle);
  if (existing) {
    if (primeMediaDecoder) warmDetailFirstStream(existing, false);
    return;
  }

  if (!pathKey || inFlightDetailPromises.has(pathKey) || bgPrefetchControllers.size >= 2) return;
  const ctrl = new AbortController();
  bgPrefetchControllers.add(ctrl);
  const params = new URLSearchParams({
    path: pathKey,
    title: rawTitle,
    node: nodeId,
  });
  const p = fetch(`/api/details?${params.toString()}`, { signal: ctrl.signal })
    .then((r) => (r.ok ? r.json() : null))
    .then((json) => {
      if (json?.ok && json?.detail?.episodes?.length) {
        for (const ep of json.detail.episodes || []) {
          for (const src of ep.sources || []) {
            if (src.downloadUrl) src.downloadUrl = resolveDirectDownloadUrl(src.downloadUrl);
          }
        }
        clientDetailCache.set(pathKey, { detail: json.detail, ts: Date.now() });
        indexDetailsIntoMemory({ [pathKey]: json.detail }, true);
      }
      return json;
    })
    .catch(() => null)
    .finally(() => {
      bgPrefetchControllers.delete(ctrl);
      inFlightDetailPromises.delete(pathKey);
    });
  inFlightDetailPromises.set(pathKey, p);
}

function scheduleBackgroundCatalogDetailWarmup(items: MovieCardItem[], nodeId: string): void {
  if (typeof window === 'undefined' || !items?.length) return;
  // Gently pre-warm only the top 2 visible items after 800ms so background requests never clog the browser's 6-connection pool!
  items.slice(0, 2).forEach((item, idx) => {
    window.setTimeout(() => {
      if (!isVideoActivelyStarting && item?.path) {
        prefetchMovieDetails(item.path, item.title, nodeId, false);
      }
    }, 800 + idx * 450);
  });
}

const NODE_ORIGIN_MAP: Record<string, string> = {
  'node-alpha': 'https://cmyyhb.movielinkbd.at',
  'node-beta': 'https://4yer8f.movielinkbd.at',
  'node-gamma': 'https://cmyyhb.movielinkbd.at',
  'node-delta': 'https://4yer8f.movielinkbd.at',
};

async function fetchMirrorHtmlClientSide(
  relativePath: string,
  preferredNodeId = 'node-alpha',
  bustCache = false
): Promise<{ html: string; finalOrigin: string }> {
  let cleanPath = relativePath.startsWith('http')
    ? new URL(relativePath).pathname + new URL(relativePath).search
    : relativePath.startsWith('/')
      ? relativePath
      : `/${relativePath}`;

  if (bustCache) {
    const sep = cleanPath.includes('?') ? '&' : '?';
    cleanPath = `${cleanPath}${sep}_live=${Math.floor(Date.now() / 30000)}`;
  }

  const preferredOrigin = NODE_ORIGIN_MAP[preferredNodeId] || MIRROR_ORIGINS[0];
  const orderedOrigins = [
    preferredOrigin,
    ...MIRROR_ORIGINS.filter((o) => o !== preferredOrigin),
  ];

  // Try primary origin first without flooding duplicate CORS bridge requests, with a generous 10s timeout for 370KB HTML pages
  for (const origin of orderedOrigins) {
    const targetUrl = `${origin}${cleanPath}`;
    const url = CORS_BRIDGES[0](targetUrl);
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), 10000);
    try {
      const res = await fetch(url, { signal: controller.signal });
      if (!res.ok) throw new Error('Bad status');
      const html = await res.text();
      if (
        html &&
        html.length > 800 &&
        (html.includes('movie-card') || html.includes('mlbdInlinePlayerData'))
      ) {
        return { html, finalOrigin: origin };
      }
    } catch {
      // try backup origin
    } finally {
      clearTimeout(timer);
    }
  }
  throw new Error('Client mirror bridges unreachable');
}

function parseClientCatalogHtml(html: string): { items: MovieCardItem[]; maxPage: number } {
  const bodyIdx = html.indexOf('<body');
  const body = bodyIdx >= 0 ? html.slice(bodyIdx) : html;
  const blocks = body.split(/<div class="movie-card"/i).slice(1);
  const items: MovieCardItem[] = [];
  const seenPaths = new Set<string>();

  for (const block of blocks) {
    const chunk = block.slice(0, 3200);
    if (chunk.includes("'+esc(") || chunk.includes('${')) continue;

    const titleMatch =
      chunk.match(/class=["']title["'][^>]*>([\s\S]*?)<\/a>/i) ||
      chunk.match(/alt=["']([^"']+)["']/i);
    const hrefMatch = chunk.match(/<a[^>]+href=["']([^"']+)["']/i);
    if (!titleMatch || !hrefMatch) continue;

    const rawHref = hrefMatch[1].trim();
    if (!rawHref || rawHref.includes("'+") || rawHref === '#') continue;

    const itemPath = rawHref.startsWith('http')
      ? new URL(rawHref).pathname
      : rawHref.startsWith('/')
        ? rawHref
        : `/${rawHref}`;

    if (seenPaths.has(itemPath)) continue;
    seenPaths.add(itemPath);

    const title = decodeHtmlEntities(titleMatch[1]);
    if (!title) continue;

    const posterMatch =
      chunk.match(/data-src=["'](https?:\/\/[^"']+)["']/i) ||
      chunk.match(/src=["'](https?:\/\/[^"']+)["']/i);
    const poster = posterMatch ? posterMatch[1].trim() : '';

    const quality = decodeHtmlEntities(
      (chunk.match(/<span class=["']quality["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'WEB-DL'
    );
    const language = decodeHtmlEntities(
      (chunk.match(/<span class=["']language["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'MULTI'
    );
    const views = decodeHtmlEntities(
      (chunk.match(/<span class=["']views-badge-top["'][^>]*>[\s\S]*?<\/i>\s*([^<]+)<\/span>/i) ||
        [])[1] || '2.4K'
    );
    const rawTimeAgo = decodeHtmlEntities(
      (chunk.match(/<div class=["']upload-time["'][^>]*>([\s\S]*?)<\/div>/i) || [])[1] ||
        'Recently added'
    );
    const rawEpisodePill = decodeHtmlEntities(
      (chunk.match(/<span class=["']badge ep-badge[^"']*["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] ||
        ''
    );
    const cleanedTime = cleanTimeAgoAndEpisode(
      rawTimeAgo,
      rawEpisodePill,
      itemPath || title,
      items.length
    );

    const isPinned = chunk.includes('pin-badge') || chunk.includes('data-pin="1"');
    const isAdult =
      chunk.includes('data-18="1"') ||
      itemPath.includes('18plus') ||
      cleanedTime.episodePill.toUpperCase().includes('18+');

    let typeBadge: 'MOVIE' | 'SERIES' | 'ANIME' | 'DRAMA' = 'MOVIE';
    if (itemPath.includes('/anime/')) typeBadge = 'ANIME';
    else if (itemPath.includes('/drama/')) typeBadge = 'DRAMA';
    else if (itemPath.includes('/series/') || Boolean(cleanedTime.episodePill)) typeBadge = 'SERIES';

    items.push({
      id: itemPath.replace(/[^a-zA-Z0-9_-]/g, '_'),
      title,
      url: itemPath,
      path: itemPath,
      poster,
      quality: quality || 'HD',
      views: views || '1.9K',
      language: language || 'MULTI',
      typeBadge,
      timeAgo: cleanedTime.timeAgo,
      episodePill: cleanedTime.episodePill,
      isPinned,
      isAdult,
      uploadedAtMs: Date.now() - cleanedTime.minutesAgo * 60_000,
    });
  }

  const pageMatches = [...body.matchAll(/\/page\/(\d+)/g)]
    .map((m) => Number(m[1]))
    .filter((n) => !isNaN(n) && n > 0 && n <= 2000);
  const maxPage = pageMatches.length > 0 ? Math.max(...pageMatches) : 520;

  return { items, maxPage };
}

function parseClientDetailHtml(html: string, itemPath: string, origin: string): MovieDetailData {
  let inlineData: any = null;
  const playerScriptMatch = html.match(
    /<script[^>]*id=["']mlbdInlinePlayerData["'][^>]*data-s=["']([^"']+)["'][^>]*data-r=["'](\d+)["'][^>]*>([\s\S]*?)<\/script>/i
  );
  if (playerScriptMatch) {
    const decodedJson = decodeMlbdCipherBrowser(
      playerScriptMatch[3],
      playerScriptMatch[1],
      parseInt(playerScriptMatch[2], 10) || 600
    );
    try {
      inlineData = JSON.parse(decodedJson);
    } catch {
      inlineData = null;
    }
  }

  const downloadButtons: DirectDownloadButton[] = [];
  const dlRegex =
    /<a[^>]*data-dl=["']([^"']+)["'][^>]*data-ds=["']([^"']+)["'][^>]*data-dr=["'](\d+)["'][^>]*>([\s\S]*?)<\/a>/gi;
  for (const match of html.matchAll(dlRegex)) {
    const decodedHref = decodeMlbdCipherBrowser(
      match[1],
      match[2],
      parseInt(match[3], 10) || 300
    );
    const label = decodeHtmlEntities(match[4]);
    if (decodedHref) {
      const fullDlUrl = decodedHref.startsWith('http')
        ? decodedHref
        : `${origin}${decodedHref.startsWith('/') ? '' : '/'}${decodedHref}`;
      const bracketMatch = label.match(/\[(.*?)\]/);
      const parts = bracketMatch ? bracketMatch[1].split('•').map((s) => s.trim()) : [];
      downloadButtons.push({
        label: sanitizeBrandText(label || 'High-Speed Direct Download'),
        url: fullDlUrl,
        quality: parts[0] || 'HD',
        size: parts[1] || '',
      });
    }
  }

  const rawTitle =
    inlineData?.title ||
    decodeHtmlEntities((html.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i) || [])[1] || 'Cinema Title');
  const title = sanitizeBrandText(rawTitle);

  const poster =
    inlineData?.poster ||
    (html.match(
      /<div class=["']image-container-view["'][\s\S]*?<img[^>]+src=["'](https?:\/\/[^"']+)["']/i
    ) || [])[1] ||
    '';

  const qualityNote = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<div class=["']movie-info-view["'][\s\S]*?<p[^>]*>([\s\S]*?)<\/p>/i) || [])[1] ||
        '1080p Full HD Stream'
    )
  );

  const extractInfoLine = (keyword: string): string => {
    const regex = new RegExp(
      `<p class=["']info-line["'][^>]*>[\\s\\S]*?${keyword}:?<\\/b>([\\s\\S]*?)<\\/p>`,
      'i'
    );
    const m = html.match(regex);
    return m ? decodeHtmlEntities(m[1]) : '';
  };

  const genre = extractInfoLine('Genre') || 'Cinema, Entertainment';
  const language = extractInfoLine('Language') || 'Multi Audio';
  const quality = extractInfoLine('Quality') || 'WEB-DL';
  const resolution = extractInfoLine('Resolution') || '1080p | 720p | 480p';
  const releaseDate = extractInfoLine('Released') || '2026';

  const storyline = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<p class=["']story-text["'][^>]*>([\s\S]*?)<\/p>/i) || [])[1] ||
        (html.match(/<meta name=["']description["'] content=["']([^"']+)["']/i) || [])[1] ||
        ''
    )
  );

  const trailerMatch = html.match(/data-mlbd-trailer=["']([a-zA-Z0-9_-]{6,20})["']/i);
  const youtubeTrailerId = trailerMatch ? trailerMatch[1] : '';

  const cast: CastMember[] = [];
  const castRegex =
    /<a class=["']mlbd-cast__p["'][^>]+href=["']([^"']+)["'][^>]*>[\s\S]*?<img[^>]+src=["']([^"']+)["'][^>]*>[\s\S]*?<b>([\s\S]*?)<\/b>[\s\S]*?<small>([\s\S]*?)<\/small>/gi;
  for (const m of html.matchAll(castRegex)) {
    const actorName = decodeHtmlEntities(m[3]);
    if (actorName) {
      cast.push({
        url: `/search?q=${encodeURIComponent(actorName)}`,
        photo: m[2],
        name: actorName,
        role: decodeHtmlEntities(m[4]),
      });
    }
  }

  const inferStreamQuality = (s: any): number => {
    const combined = `${s?.quality_label || ''} ${s?.name || ''}`.toLowerCase();
    if (/\b(2160p|4k)\b/.test(combined)) return 2160;
    if (/\b(1080p|full\s*hd)\b/.test(combined)) return 1080;
    if (/\b(480p|360p)\b/.test(combined)) return 480;
    if (/\b720p\b/.test(combined)) return 720;
    const q = Number(s?.quality);
    if (q === 480 || q === 720 || q === 1080 || q === 2160) return q;
    if (/best\s*quality/i.test(combined)) return 1080;
    return 720;
  };

  const scoreSourceForSmoothPlay = (src: StreamSource): number => {
    const isHevc = /\b(hevc|h\.?265|x265|10bit)\b/i.test(`${src.name} ${src.qualityLabel}`);
    const isBestHeavy = /best\s*quality/i.test(src.qualityLabel || '');
    let score = isHevc ? 200 : 1000;
    if (isBestHeavy) score -= 250;
    if (/\.(mp4|m4v|m3u8)(\?|$)/i.test(src.url)) score += 90;
    if (/r2\.dev|workers\.dev|cloudflare|fsldownload|pixeldrain/i.test(src.url)) score += 50;
    if (src.quality >= 360 && src.quality <= 576) score += 650;
    else if (src.quality === 720) score += 500;
    else if (src.quality === 1080) score += 350;
    else if (src.quality === 2160) score += 150;
    else score += 200;
    return score;
  };

  const mapRawEpisode = (ep: any, idx: number): EpisodeItem => {
    const rawSources: StreamSource[] = Array.isArray(ep.sources)
      ? ep.sources
          .filter((s: any) => s && (s.url || s.download_url))
          .map((s: any, sIdx: number) => {
            const rawUrl = String(s.url || '');
            const rawStreamUrl = rawUrl.startsWith('http')
              ? rawUrl
              : rawUrl
                ? `${origin}${rawUrl.startsWith('/') ? '' : '/'}${rawUrl}`
                : '';
            const rawDlUrl = String(s.download_url || s.url || '');
            const fullDlUrl = rawDlUrl.startsWith('http')
              ? rawDlUrl
              : rawDlUrl
                ? `${origin}${rawDlUrl.startsWith('/') ? '' : '/'}${rawDlUrl}`
                : '';
            const realQuality = inferStreamQuality(s);
            return {
              id: String(s.id || `src-${idx}-${realQuality}-${sIdx}`),
              quality: realQuality,
              qualityLabel: s.quality_label || `${realQuality}p`,
              audio: sanitizeBrandText(String(s.audio || 'Multi Audio')),
              audioLanguages: Array.isArray(s.audio_languages)
                ? s.audio_languages.map((a: any) => sanitizeBrandText(String(a)))
                : [sanitizeBrandText(String(s.audio || 'Original'))],
              provider: `Cloud Stream #${sIdx + 1}`,
              url: rawStreamUrl,
              downloadUrl: fullDlUrl,
              type: String(s.type || 'mkv').toLowerCase(),
              name: sanitizeBrandText(String(s.name || `${title} - ${realQuality}p`)),
              screenshot: s.screenshot || undefined,
            };
          })
      : [];

    const sources = [...rawSources].sort(
      (a, b) => scoreSourceForSmoothPlay(b) - scoreSourceForSmoothPlay(a)
    );

    const rawLabel = sanitizeBrandText(
      String(ep.label || (ep.number ? `Episode ${ep.number}` : 'Full Movie'))
    );

    const rangeMatch = rawLabel.match(/(?:ep(?:isode)?|e)\s*0*(\d{1,4})\s*[-–—]\s*0*(\d{1,4})/i);
    const singleEpMatch =
      rawLabel.match(/s\d+\s*e0*(\d{1,4})/i) ||
      rawLabel.match(/(?:ep(?:isode)?|e)\s*0*(\d{1,4})/i);
    const seasonMatch = rawLabel.match(/\bs(?:eason)?\s*0*(\d{1,2})\b/i);

    const parsedStart = rangeMatch
      ? Number(rangeMatch[1])
      : singleEpMatch
        ? Number(singleEpMatch[1])
        : null;
    const parsedEnd = rangeMatch ? Number(rangeMatch[2]) : parsedStart;

    const number =
      ep.number !== null && ep.number !== undefined
        ? Number(ep.number)
        : ep.range_start !== null && ep.range_start !== undefined
          ? Number(ep.range_start)
          : parsedStart;

    const rangeStart =
      ep.range_start !== null && ep.range_start !== undefined ? Number(ep.range_start) : number;
    const rangeEnd =
      ep.range_end !== null && ep.range_end !== undefined
        ? Number(ep.range_end)
        : parsedEnd ?? rangeStart;

    const season =
      ep.season !== null && ep.season !== undefined
        ? Number(ep.season)
        : seasonMatch
          ? Number(seasonMatch[1])
          : null;

    return {
      id: String(ep.id || `ep-${idx + 1}`),
      label: rawLabel,
      number,
      rangeStart,
      rangeEnd,
      season,
      kind: String(ep.kind || (number !== null ? 'episode' : 'movie')),
      sources,
    };
  };

  const episodes: EpisodeItem[] = Array.isArray(inlineData?.episodes)
    ? inlineData.episodes
        .map((ep: any, idx: number) => mapRawEpisode(ep, idx))
        .filter((ep: EpisodeItem) => ep.sources.length > 0)
        .sort((a: EpisodeItem, b: EpisodeItem) => {
          const sA = a.season ?? 0;
          const sB = b.season ?? 0;
          if (sA !== sB && a.season !== null && b.season !== null) return sA - sB;
          const nA = a.rangeStart ?? a.number ?? 999999;
          const nB = b.rangeStart ?? b.number ?? 999999;
          if (nA !== nB) return nA - nB;
          return (a.rangeEnd ?? nA) - (b.rangeEnd ?? nB);
        })
    : [];

  const screenshots: string[] = Array.isArray(inlineData?.screenshots)
    ? inlineData.screenshots.map((s: any) => s?.url).filter(Boolean)
    : [];

  return {
    title,
    url: itemPath,
    poster,
    qualityNote,
    typeBadge: inlineData?.content_type === 'series' || episodes.length > 1 ? 'SERIES' : 'MOVIE',
    language,
    quality,
    genre,
    resolution,
    releaseDate,
    storyline,
    youtubeTrailerId,
    screenshots,
    episodes,
    downloadButtons,
    cast: cast.slice(0, 12),
    communityScore: {
      recommendedPercent: 92,
      totalVotes: 420,
      verdict: 'Massive Hit',
    },
  };
}

/**
 * Universal API Fetcher:
 * - On Node.js server (AI Studio / Cloud Run / Render), uses `/api/...`
 * - On Static GitHub Pages (`*.github.io`), uses Instant Pre-Built Snapshot (`./static-db.json`)
 *   + Live Browser Cipher Decryptor (`allorigins.hexlet.app` + `decodeMlbdCipherBrowser`)
 */
export async function universalApiFetch(endpoint: string, init?: RequestInit): Promise<any> {
  const parsedUrl = new URL(endpoint, 'https://cinepulse.local');
  const pathname = parsedUrl.pathname;

  const isGitHubPages =
    typeof window !== 'undefined' && window.location.hostname.endsWith('github.io');

  // 0. Instant 0ms local memory / static-db / shard check for /api/details before any network fetch!
  if (pathname === '/api/details' && parsedUrl.searchParams.get('enrich') !== '1') {
    const rawPath = (parsedUrl.searchParams.get('path') || '').trim();
    const rawTitle = (parsedUrl.searchParams.get('title') || '').trim();
    const instant = getInstantCachedDetail(rawPath, rawTitle);
    if (instant && instant.episodes && instant.episodes.length > 0) {
      return { ok: true, cached: true, detail: instant };
    }
    const shardHit = await loadShardForMovie(rawPath, rawTitle);
    if (shardHit && shardHit.episodes && shardHit.episodes.length > 0) {
      return { ok: true, cached: true, detail: shardHit };
    }
    const existingPromise = rawPath ? inFlightDetailPromises.get(rawPath) : undefined;
    if (existingPromise) {
      const joined = await existingPromise;
      if (joined?.ok && joined?.detail) {
        return joined;
      }
    }
  }

  // 0b. Instant 0ms catalog check from pre-loaded static-db.json (for static GitHub Pages!)
  if (isGitHubPages && pathname === '/api/catalog' && parsedUrl.searchParams.get('refresh') !== '1') {
    const rawPath = parsedUrl.searchParams.get('path') || '/';
    const page = Math.max(1, parseInt(parsedUrl.searchParams.get('page') || '1', 10));
    const search = (parsedUrl.searchParams.get('q') || '').trim();
    const nodeId = parsedUrl.searchParams.get('node') || 'node-moviebox';
    if (!search && loadedStaticDb?.catalogs) {
      const cleanBase = rawPath === '/' ? '' : rawPath.replace(/\/+$/, '');
      const pageKey = page > 1 ? `${cleanBase}/page/${page}` : rawPath;
      const snap = loadedStaticDb.catalogs[pageKey];
      if (snap && snap.length > 0) {
        const sorted =
          rawPath === '/hot-dhamaka' || rawPath === '/'
            ? sortItemsByHotAndHype(snap)
            : rawPath === '/new-uploads' || rawPath === '/new-releases'
              ? sortItemsByRecentUpload(snap)
              : normalizeMovieCardList(snap);
        scheduleBackgroundCatalogDetailWarmup(sorted, nodeId);
        return {
          ok: true,
          cached: true,
          items: sorted,
          page,
          maxPage: 520,
          activeNodeId: nodeId,
        };
      }
    }
  }

  // 1. Unified Server API First (with instant client RAM cache for 0ms category switching!)
  if (!isGitHubPages) {
    if (pathname === '/api/catalog' && parsedUrl.searchParams.get('refresh') !== '1') {
      const cKey = `api::${parsedUrl.searchParams.get('path') || '/'}::p=${parsedUrl.searchParams.get('page') || '1'}::q=${parsedUrl.searchParams.get('q') || ''}::n=${parsedUrl.searchParams.get('node') || 'auto'}`;
      const cHit = clientCatalogCache.get(cKey);
      if (cHit && Date.now() - cHit.ts < 60_000 && cHit.items.length > 0) {
        return {
          ok: true,
          cached: true,
          items: cHit.items,
          page: parseInt(parsedUrl.searchParams.get('page') || '1', 10) || 1,
          maxPage: cHit.maxPage,
          activeNodeId: parsedUrl.searchParams.get('node') || 'node-moviebox',
        };
      }
    }
    try {
      const res = await fetch(endpoint, init);
      const contentType = res.headers.get('content-type') || '';
      if (res.ok && contentType.includes('application/json')) {
        const json = await res.json();
        // Decode any `/api/go?t=` download tokens so direct downloads work everywhere
        if (json?.detail) {
          for (const ep of json.detail.episodes || []) {
            for (const src of ep.sources || []) {
              if (src.downloadUrl) src.downloadUrl = resolveDirectDownloadUrl(src.downloadUrl);
            }
          }
          for (const btn of json.detail.downloadButtons || []) {
            if (btn.url) btn.url = resolveDirectDownloadUrl(btn.url);
          }
          if (json.detail.url) {
            clientDetailCache.set(json.detail.url, { detail: json.detail, ts: Date.now() });
            indexDetailsIntoMemory({ [json.detail.url]: json.detail }, true);
          }
          warmDetailFirstStream(json.detail);
        } else if (pathname === '/api/catalog' && Array.isArray(json?.items) && json.items.length > 0) {
          const cKey = `api::${parsedUrl.searchParams.get('path') || '/'}::p=${parsedUrl.searchParams.get('page') || '1'}::q=${parsedUrl.searchParams.get('q') || ''}::n=${parsedUrl.searchParams.get('node') || 'auto'}`;
          clientCatalogCache.set(cKey, {
            items: json.items,
            maxPage: Number(json.maxPage) || 2500,
            ts: Date.now(),
          });
          if (json.prefetchedDetails && typeof json.prefetchedDetails === 'object') {
            indexDetailsIntoMemory(json.prefetchedDetails, true);
            for (const [detPath, detVal] of Object.entries(json.prefetchedDetails)) {
              if (detVal && (detVal as MovieDetailData).episodes?.length) {
                clientDetailCache.set(detPath, {
                  detail: detVal as MovieDetailData,
                  ts: Date.now(),
                });
              }
            }
          }
          scheduleBackgroundCatalogDetailWarmup(
            json.items,
            parsedUrl.searchParams.get('node') || 'node-moviebox'
          );
        }
        return json;
      }
    } catch {
      // fallback to client engine
    }
  }

  // 2. Built-in Serverless Browser Mirror & Snapshot Engine (100% standalone on GitHub Pages)
  const staticDb = await loadStaticDb();

  if (pathname === '/api/categories') {
    return {
      categories: ALL_CATEGORIES,
      nodes: [
        { id: 'node-moviebox', name: 'MovieBox HD', region: 'Global 4K/1080p Hub' },
        { id: 'node-alpha', name: 'Node Alpha', region: 'BD-Fast Edge' },
        { id: 'node-beta', name: 'Node Beta', region: 'SG-Ultra CDN' },
        { id: 'node-gamma', name: 'Node Gamma', region: 'Global Stream' },
        { id: 'node-delta', name: 'Node Delta', region: 'Backup Core' },
        { id: 'node-myflix', name: 'Node MyFlix', region: 'BD-Dual Hub' },
      ],
    };
  }

  if (pathname === '/api/server-health') {
    return {
      ok: true,
      nodes: [
        { id: 'node-moviebox', name: 'MovieBox HD', region: 'Global 4K/1080p Hub', latencyMs: 24, online: true },
        { id: 'node-alpha', name: 'Node Alpha', region: 'BD-Fast Edge', latencyMs: 38, online: true },
        { id: 'node-beta', name: 'Node Beta', region: 'SG-Ultra CDN', latencyMs: 54, online: true },
        { id: 'node-gamma', name: 'Node Gamma', region: 'Global Stream', latencyMs: 79, online: true },
        { id: 'node-delta', name: 'Node Delta', region: 'Backup Core', latencyMs: 96, online: true },
        { id: 'node-myflix', name: 'Node MyFlix', region: 'BD-Dual Hub', latencyMs: 42, online: true },
      ],
    };
  }

  if (pathname === '/api/suggest') {
    const q = (parsedUrl.searchParams.get('q') || '').trim();
    if (q.length < 1) return { ok: true, items: [], suggestions: [] };

    const lower = q.toLowerCase();
    const pool: MovieCardItem[] = [];
    const seen = new Set<string>();
    const allLists = [
      ...Array.from(clientCatalogCache.values()).map((c) => c.items),
      ...Object.values(staticDb?.catalogs || {}),
      ...Object.values(INITIAL_FALLBACK_MOVIES),
    ];
    for (const list of allLists) {
      for (const item of list) {
        if (!seen.has(item.path) && item.title.toLowerCase().includes(lower)) {
          seen.add(item.path);
          pool.push(item);
        }
      }
    }

    const interleaveSites = (itemsList: MovieCardItem[]): MovieCardItem[] => {
      const mb = itemsList.filter((i) => i.path?.startsWith('/mb/'));
      const mf = itemsList.filter((i) => i.path?.startsWith('/mf/'));
      const mlbd = itemsList.filter(
        (i) => !i.path?.startsWith('/mb/') && !i.path?.startsWith('/mf/')
      );
      const out: MovieCardItem[] = [];
      const maxLen = Math.max(mb.length, mlbd.length, mf.length);
      for (let i = 0; i < maxLen; i++) {
        if (i < mb.length) out.push(mb[i]);
        if (i < mlbd.length) out.push(mlbd[i]);
        if (i < mf.length) out.push(mf[i]);
      }
      return deduplicateMovieCards(out);
    };

    const nodeId = parsedUrl.searchParams.get('node') || 'node-alpha';
    try {
      const { html } = await fetchMirrorHtmlClientSide(`/search?q=${encodeURIComponent(q)}`, nodeId);
      const { items } = parseClientCatalogHtml(html);
      const merged = interleaveSites([...items, ...pool]).slice(0, 16);
      return { ok: true, items: merged, suggestions: merged };
    } catch {
      const top = interleaveSites(pool).slice(0, 16);
      return { ok: true, items: top, suggestions: top };
    }
  }

  if (pathname === '/api/catalog') {
    const rawPath = parsedUrl.searchParams.get('path') || '/';
    const page = Math.max(1, parseInt(parsedUrl.searchParams.get('page') || '1', 10));
    const search = (parsedUrl.searchParams.get('q') || '').trim();
    const nodeId = parsedUrl.searchParams.get('node') || 'node-alpha';
    const forceRefresh = parsedUrl.searchParams.get('refresh') === '1';

    const isNewUploadsView = rawPath === '/new-uploads';
    const isNewReleasesView = rawPath === '/new-releases';
    const isHotDhamakaView = rawPath === '/hot-dhamaka';
    const isTrendingHomeView = rawPath === '/' || rawPath === '';

    let upstreamBase = rawPath.startsWith('/') ? rawPath : `/${rawPath}`;
    if (isNewUploadsView || isNewReleasesView || isHotDhamakaView) {
      upstreamBase = '/';
    }

    let targetPath = upstreamBase;
    if (search) {
      targetPath = `/search?q=${encodeURIComponent(search)}`;
    } else if (page > 1) {
      const cleanBase = upstreamBase === '/' ? '' : upstreamBase.replace(/\/+$/, '');
      targetPath = `${cleanBase}/page/${page}`;
    }

    const cacheKey = `${rawPath}::p=${page}::q=${search}`;
    const memCached = clientCatalogCache.get(cacheKey);
    if (!forceRefresh && memCached && Date.now() - memCached.ts < 30_000) {
      scheduleBackgroundCatalogDetailWarmup(memCached.items, nodeId);
      return {
        ok: true,
        items: normalizeMovieCardList(memCached.items),
        page,
        maxPage: memCached.maxPage,
        activeNodeId: nodeId,
      };
    }

    // Helper to merge freshly scraped live items at the top of the pre-built snapshot
    // so 1-minute-old upstream uploads appear immediately on GitHub Pages without losing catalog depth!
    const mergeLiveWithSnapshot = (
      liveItems: MovieCardItem[],
      baseSnapshot?: MovieCardItem[]
    ): MovieCardItem[] => {
      if (!baseSnapshot || baseSnapshot.length === 0) return deduplicateMovieCards(liveItems);
      return deduplicateMovieCards([...liveItems, ...baseSnapshot]);
    };

    // Return pre-built snapshot immediately if available (including /page/2, /page/3, and all 42+ categories),
    // and refresh in background so initial load is < 50ms!
    const snapshotList = !search
      ? (page === 1 ? staticDb?.catalogs?.[rawPath] : undefined) ||
        staticDb?.catalogs?.[targetPath] ||
        (page === 1 ? staticDb?.catalogs?.[upstreamBase] : undefined)
      : undefined;
    if (snapshotList && snapshotList.length > 0 && !forceRefresh) {
      const finalizedSnapshot = isHotDhamakaView
        ? sortItemsByHotAndHype(snapshotList)
        : isNewUploadsView || isNewReleasesView
          ? sortItemsByRecentUpload(snapshotList)
          : isTrendingHomeView
            ? sortItemsByHotAndHype(snapshotList)
            : normalizeMovieCardList(snapshotList);
      scheduleBackgroundCatalogDetailWarmup(finalizedSnapshot, nodeId);
      // Trigger non-blocking live mirror refresh with cache-busting
      fetchMirrorHtmlClientSide(targetPath, nodeId, true)
        .then(({ html }) => {
          const parsed = parseClientCatalogHtml(html);
          if (parsed.items.length > 0) {
            const mergedRaw = mergeLiveWithSnapshot(parsed.items, snapshotList);
            const listToStore = isHotDhamakaView || isTrendingHomeView
              ? sortItemsByHotAndHype(mergedRaw)
              : isNewUploadsView || isNewReleasesView
                ? sortItemsByRecentUpload(mergedRaw)
                : normalizeMovieCardList(mergedRaw);
            clientCatalogCache.set(cacheKey, {
              items: listToStore,
              maxPage: parsed.maxPage,
              ts: Date.now(),
            });
          }
        })
        .catch(() => {});

      return {
        ok: true,
        items: finalizedSnapshot,
        page,
        maxPage: 520,
        activeNodeId: nodeId,
      };
    }

    const collectLocalSearchMatches = (query: string): MovieCardItem[] => {
      const lower = query.toLowerCase();
      const matched: MovieCardItem[] = [];
      const seen = new Set<string>();
      for (const list of [
        ...Array.from(clientCatalogCache.values()).map((c) => c.items),
        ...Object.values(staticDb?.catalogs || {}),
        ...Object.values(INITIAL_FALLBACK_MOVIES),
      ]) {
        for (const item of list) {
          if (!seen.has(item.path) && item.title.toLowerCase().includes(lower)) {
            seen.add(item.path);
            matched.push(item);
          }
        }
      }
      return matched;
    };

    try {
      const { html } = await fetchMirrorHtmlClientSide(targetPath, nodeId, true);
      const { items: rawLiveItems, maxPage } = parseClientCatalogHtml(html);
      const localSearchMatches = search ? collectLocalSearchMatches(search) : [];
      const rawItems = search
        ? deduplicateMovieCards([...rawLiveItems, ...localSearchMatches])
        : mergeLiveWithSnapshot(rawLiveItems, snapshotList);
      let items = isHotDhamakaView || isTrendingHomeView
        ? sortItemsByHotAndHype(rawItems)
        : isNewUploadsView || isNewReleasesView
          ? sortItemsByRecentUpload(rawItems)
          : normalizeMovieCardList(rawItems);
      if (isNewReleasesView) {
        const filtered = items.filter((i) => i.title.includes('2026') || i.title.includes('2025'));
        if (filtered.length >= 6) items = filtered;
      }
      if (items.length > 0) {
        clientCatalogCache.set(cacheKey, { items, maxPage, ts: Date.now() });
        scheduleBackgroundCatalogDetailWarmup(items, nodeId);
        return { ok: true, items, page, maxPage, activeNodeId: nodeId };
      }
    } catch {
      // fallback
    }

    if (search) {
      const matched = collectLocalSearchMatches(search);
      const normMatched = normalizeMovieCardList(deduplicateMovieCards(matched));
      return { ok: true, items: normMatched, page: 1, maxPage: 1, activeNodeId: nodeId };
    }

    const fallbackList = sortItemsByRecentUpload(
      snapshotList || INITIAL_FALLBACK_MOVIES[rawPath] || INITIAL_FALLBACK_MOVIES['/'] || []
    );
    return { ok: true, items: fallbackList, page: 1, maxPage: 520, activeNodeId: nodeId };
  }

  if (pathname === '/api/details') {
    const rawPath = (parsedUrl.searchParams.get('path') || '').trim();
    const rawTitle = (parsedUrl.searchParams.get('title') || '').trim();
    const nodeId = parsedUrl.searchParams.get('node') || 'node-alpha';

    const attachRelatedSeasons = (detailObj: MovieDetailData): MovieDetailData => {
      if (detailObj.relatedSeasons && detailObj.relatedSeasons.length > 0) return detailObj;
      const baseSeriesName = extractBaseSeriesTitle(rawTitle || detailObj.title);
      if (baseSeriesName && baseSeriesName.length >= 3) {
        const baseLower = baseSeriesName.toLowerCase();
        const allKnownItems = Object.values(staticDb?.catalogs || {}).flat();
        const matchingSeasons = allKnownItems.filter((item) => {
          const itemBase = extractBaseSeriesTitle(item.title).toLowerCase();
          return (
            item.path !== detailObj.url &&
            (itemBase === baseLower ||
              item.title.toLowerCase().startsWith(baseLower) ||
              baseLower.startsWith(itemBase))
          );
        });
        if (matchingSeasons.length > 0) {
          const uniqueSeasons: MovieCardItem[] = [];
          const seenS = new Set<string>();
          for (const s of matchingSeasons) {
            if (!seenS.has(s.path)) {
              seenS.add(s.path);
              uniqueSeasons.push(s);
            }
          }
          return { ...detailObj, relatedSeasons: uniqueSeasons.slice(0, 12) };
        }
      }
      return detailObj;
    };

    const isLiveEnrich = parsedUrl.searchParams.get('enrich') === '1';

    // 1. Check in-memory decrypted cache first (unless live enrich is requested)
    const cachedDetail = clientDetailCache.get(rawPath);
    if (!isLiveEnrich && cachedDetail && Date.now() - cachedDetail.ts < 60_000) {
      return { ok: true, detail: attachRelatedSeasons(cachedDetail.detail) };
    }

    // 2. Live fetch & cipher decrypt in browser (with cache-busting when isLiveEnrich is true)
    try {
      let { html, finalOrigin } = await fetchMirrorHtmlClientSide(
        rawPath || '/',
        nodeId,
        isLiveEnrich
      );
      if (!html.includes('mlbdInlinePlayerData') && rawTitle) {
        const cleanQuery = extractBaseSeriesTitle(rawTitle)
          .split(/\s+/)
          .slice(0, 4)
          .join(' ');
        if (cleanQuery) {
          const searchRes = await fetchMirrorHtmlClientSide(
            `/search?q=${encodeURIComponent(cleanQuery)}`,
            nodeId
          );
          const { items } = parseClientCatalogHtml(searchRes.html);
          if (items.length > 0) {
            const resolved = await fetchMirrorHtmlClientSide(items[0].path, nodeId);
            html = resolved.html;
            finalOrigin = resolved.finalOrigin;
          }
        }
      }

      const detail = parseClientDetailHtml(html, rawPath, finalOrigin);

      // Multi-season & related episodes discovery from staticDb or live search
      const baseSeriesName = extractBaseSeriesTitle(rawTitle || detail.title);
      if (baseSeriesName && baseSeriesName.length >= 3) {
        const baseLower = baseSeriesName.toLowerCase();
        const allKnownItems = Object.values(staticDb?.catalogs || {}).flat();
        const matchingSeasons = allKnownItems.filter((item) => {
          const itemBase = extractBaseSeriesTitle(item.title).toLowerCase();
          return (
            item.path !== rawPath &&
            (itemBase === baseLower ||
              item.title.toLowerCase().startsWith(baseLower) ||
              baseLower.startsWith(itemBase))
          );
        });
        if (matchingSeasons.length > 0) {
          const uniqueSeasons: MovieCardItem[] = [];
          const seenS = new Set<string>();
          for (const s of matchingSeasons) {
            if (!seenS.has(s.path)) {
              seenS.add(s.path);
              uniqueSeasons.push(s);
            }
          }
          detail.relatedSeasons = uniqueSeasons.slice(0, 12);
        }
      }

      if (detail.episodes.length > 0 || detail.downloadButtons.length > 0) {
        clientDetailCache.set(rawPath, { detail, ts: Date.now() });
        return { ok: true, detail };
      }
    } catch {
      // fallback below
    }

    // 4. Fallback: check staticDb by fuzzy title words (never return an unrelated movie!)
    const instantFallback = getInstantCachedDetail(rawPath, rawTitle);
    if (instantFallback && instantFallback.episodes?.length) {
      return { ok: true, detail: attachRelatedSeasons(instantFallback) };
    }

    return { ok: false, error: 'Unable to load stream metadata' };
  }

  if (pathname === '/api/mb-home') {
    const staticDb = await loadStaticDb();
    const homeItems = staticDb?.catalogs?.['/'] || INITIAL_FALLBACK_MOVIES['/'] || [];
    return {
      ok: true,
      banners: homeItems.slice(0, 8),
      liveSports: [
        {
          id: 'sport-football-live',
          title: 'Football Live',
          bnTitle: 'ফুটবল লাইভ ম্যাচ (MovieBox Sports)',
          subtitle: 'UEFA Champions League • Premier League • LaLiga • FIFA Live',
          sportType: 'football',
          liveUrl: 'https://sportsnow.top/live?tab=live&sportType=football',
          categoryPath: '/fifa',
          badge: 'LIVE MATCH',
          accentColor: '#00e68a',
        },
        {
          id: 'sport-basketball-live',
          title: 'Basketball Live',
          bnTitle: 'বাস্কেটবল ও NBA লাইভ ম্যাচ',
          subtitle: 'NBA Playoffs • EuroLeague • FIBA Live Score & Stream',
          sportType: 'basketball',
          liveUrl: 'https://sportsnow.top/live?tab=live&sportType=basketball',
          categoryPath: '/category/sports',
          badge: 'NBA LIVE',
          accentColor: '#f59e0b',
        },
        {
          id: 'sport-wwe-wrestling',
          title: 'WWE & Combat Sports',
          bnTitle: 'ডব্লিউডব্লিউই রেসলিং ও ফাইট শো',
          subtitle: 'WrestleMania • RAW • SmackDown • Royal Rumble Full HD',
          sportType: 'wwe',
          liveUrl: 'https://sportsnow.top/live?tab=live&sportType=football',
          categoryPath: '/category/wwe',
          badge: 'WWE HD',
          accentColor: '#ef4444',
        },
      ],
      quickCategories: [
        {
          id: 'qc-hollywood',
          title: 'Hollywood',
          bnTitle: 'হলিউড মুভি',
          image: 'https://pbcdnw.aoneroom.com/image/2025/01/13/683063a45b61be3be1f9d7ef9b2d3072.png',
          path: '/language/english',
        },
        {
          id: 'qc-bollywood',
          title: 'Bollywood',
          bnTitle: 'বলিউড হিন্দি',
          image: 'https://pbcdnw.aoneroom.com/image/2025/01/13/95be398605ce21b60efbe7e7a5bf9fc2.png',
          path: '/bollywood',
        },
        {
          id: 'qc-bengali',
          title: 'Bengali Movies',
          bnTitle: 'বাংলা মুভি ও নাটক',
          image: 'https://pub-69b6234af505413bbeac2bbc8039195c.r2.dev/poster_4g8viv1792499980.jpg',
          path: '/language/bangla',
        },
        {
          id: 'qc-south',
          title: 'South Indian',
          bnTitle: 'সাউথ ইন্ডিয়ান',
          image: 'https://pub-69b6234af505413bbeac2bbc8039195c.r2.dev/poster_06g5z71792073020.jpg',
          path: '/southIndian',
        },
      ],
      comingSoon: [],
      sections: [],
    };
  }

  if (pathname === '/api/requests') {
    const STORAGE_KEY = 'cp_local_movie_requests_v1';
    const defaultReqs = [
      {
        id: 'req-1',
        title: 'Pushpa 2: The Rule [Bangla Dubbed 4K]',
        type: 'MOVIE',
        language: 'Bangla Dubbed',
        notes: 'Full HD 1080p Dual Audio version',
        status: 'Processing',
        createdAt: Date.now() - 3600_000 * 5,
      },
      {
        id: 'req-2',
        title: 'Solo Leveling Season 2 [Hindi + Japanese Dual Audio]',
        type: 'ANIME',
        language: 'Dual Audio',
        notes: 'All episodes 1080p WEB-DL',
        status: 'Queued',
        createdAt: Date.now() - 3600_000 * 2,
      },
    ];

    let savedReqs = defaultReqs;
    try {
      const raw = localStorage.getItem(STORAGE_KEY);
      if (raw) {
        const parsed = JSON.parse(raw);
        if (Array.isArray(parsed) && parsed.length > 0) savedReqs = parsed;
      }
    } catch {
      // ignore
    }

    if (init?.method === 'POST' && init.body) {
      try {
        const bodyObj = JSON.parse(String(init.body));
        const newReq = {
          id: `req-${Date.now()}`,
          title: sanitizeBrandText(String(bodyObj.title || '')),
          type: bodyObj.type || 'MOVIE',
          language: sanitizeBrandText(String(bodyObj.language || 'Bangla / Dual Audio')),
          notes: sanitizeBrandText(String(bodyObj.notes || '')),
          status: 'Queued',
          createdAt: Date.now(),
        };
        const updated = [newReq, ...savedReqs].slice(0, 25);
        localStorage.setItem(STORAGE_KEY, JSON.stringify(updated));
        return { ok: true, request: newReq, requests: updated };
      } catch {
        // ignore
      }
    }

    return { ok: true, requests: savedReqs };
  }

  if (pathname === '/api/notifications' || pathname === '/api/notifications/broadcast') {
    const now = Date.now();
    const staticDb = await loadStaticDb();
    const pool: MovieCardItem[] = [];
    const seenPaths = new Set<string>();

    for (const entry of clientCatalogCache.values()) {
      for (const rawItem of entry.items.slice(0, 20)) {
        if (rawItem.isAdult || seenPaths.has(rawItem.path)) continue;
        seenPaths.add(rawItem.path);
        pool.push(normalizeMovieCardItem(rawItem, now));
      }
    }
    if (staticDb?.catalogs) {
      for (const [catKey, list] of Object.entries(staticDb.catalogs)) {
        if (catKey.includes('adult18plus') || !Array.isArray(list)) continue;
        for (const rawItem of list.slice(0, 20)) {
          if (rawItem.isAdult || seenPaths.has(rawItem.path)) continue;
          seenPaths.add(rawItem.path);
          pool.push(normalizeMovieCardItem(rawItem, now));
        }
      }
    }
    if (pool.length < 10) {
      for (const rawItem of INITIAL_FALLBACK_MOVIES['/'] || []) {
        if (rawItem.isAdult || seenPaths.has(rawItem.path)) continue;
        seenPaths.add(rawItem.path);
        pool.push(normalizeMovieCardItem(rawItem, now));
      }
    }

    const recentUploads = sortItemsByRecentUpload(pool, now).slice(0, 12);
    const topRatedPopular = sortItemsByHighRating(pool, now).slice(0, 12);
    const notifications: GlobalMovieNotification[] = [];
    const maxLen = Math.max(recentUploads.length, topRatedPopular.length);

    for (let i = 0; i < maxLen; i++) {
      const newItem = recentUploads[i];
      if (newItem) {
        const mins = getItemMinutesAgo(newItem, i, now);
        const ratingNum = parseFloat(newItem.rating || '8.7') || 8.7;
        const isEp = Boolean(newItem.episodePill);
        notifications.push({
          id: `notif-new-${newItem.id}`,
          category: 'NEW_UPLOAD',
          badgeText: isEp ? `নতুন এপিসোড • ${newItem.episodePill}` : 'নতুন মুভি আপলোড 🔥',
          headlineBn: isEp
            ? `নতুন এপিসোড আপলোড হয়েছে: ${newItem.title}`
            : `নতুন মুভি আপলোড হয়েছে: ${newItem.title}`,
          subtitleBn: `${newItem.language || 'Multi Audio'} • ${newItem.quality || '1080p HD'} • রেটিং ★ ${ratingNum.toFixed(1)} • ${newItem.timeAgo}`,
          movie: newItem,
          createdAt: Math.max(now - mins * 60_000, now - 24 * 3600_000),
          ratingScore: ratingNum,
        });
      }
      const popItem = topRatedPopular[i];
      if (popItem) {
        const ratingNum = Math.max(8.4, parseFloat(popItem.rating || '9.1') || 9.1);
        notifications.push({
          id: `notif-pop-${popItem.id}`,
          category: 'TOP_RATED_POPULAR',
          badgeText: `জনপ্রিয় • রেটিং ★ ${ratingNum.toFixed(1)}`,
          headlineBn: `সবার পছন্দের জনপ্রিয় ও হাই-রেটিং মুভি: ${popItem.title}`,
          subtitleBn: `রেটিং ★ ${ratingNum.toFixed(1)}/10 • ${popItem.views || '250K+'} ভিউ • ${popItem.language || 'Dual Audio'} • ${popItem.quality || 'Full HD'}`,
          movie: popItem,
          createdAt: now - (i + 1) * 180_000,
          ratingScore: ratingNum,
        });
      }
    }

    return {
      ok: true,
      serverTime: now,
      notifications: notifications.slice(0, 28),
    };
  }

  if (pathname === '/api/myflix') {
    const rawTitle = (parsedUrl.searchParams.get('title') || '').trim();
    const cleanQuery = rawTitle
      .replace(/\[.*?\]|\(.*?\)/g, ' ')
      .replace(/\b(?:20\d{2}|19\d{2}|S\d+|Season\s*\d+|Ep(?:isode)?\s*\d+|Complete|WEB-?DL|WEBRip|BluRay|HDTC|1080p|720p|480p|Dual\s*Audio|Multi\s*Audio|Hindi|Bangla|Bengali|English|Dubbed)\b/gi, ' ')
      .replace(/\s{2,}/g, ' ')
      .trim();

    if (!cleanQuery || cleanQuery.length < 2) {
      return { ok: false };
    }

    try {
      const searchUrl = `https://myflixbd.to/wp-json/wp/v2/search?search=${encodeURIComponent(cleanQuery)}&per_page=4`;
      const sRes = await fetch(searchUrl, { signal: AbortSignal.timeout(4500) });
      if (!sRes.ok) return { ok: false };
      const results = (await sRes.json()) as Array<{ title?: string; url?: string }>;
      if (!Array.isArray(results) || results.length === 0) return { ok: false };

      const norm = (s: string) => s.toLowerCase().replace(/[^a-z0-9]+/g, '');
      const targetNorm = norm(cleanQuery);
      const matched =
        results.find((r) => norm(String(r.title || '')).includes(targetNorm)) || results[0];
      if (!matched?.url) return { ok: false };

      let html = '';
      for (const buildProxy of CORS_BRIDGES) {
        try {
          const pRes = await fetch(buildProxy(matched.url), { signal: AbortSignal.timeout(5000) });
          if (pRes.ok) {
            html = await pRes.text();
            if (html.includes('player-container-0')) break;
          }
        } catch {
          // try next proxy
        }
      }
      if (!html) return { ok: false };

      const embedServers: Array<{ label: string; url: string }> = [];
      const seenUrls = new Set<string>();
      for (const m of html.matchAll(/data-url=["'](https?:\/\/[^"']+)["']/gi)) {
        const u = m[1].trim();
        if (u && !seenUrls.has(u)) {
          seenUrls.add(u);
          embedServers.push({ label: `Server ${embedServers.length + 1}`, url: u });
        }
      }
      for (const m of html.matchAll(/data-litespeed-src=["'](https?:\/\/player\.[^"']+)["']/gi)) {
        const u = m[1].trim();
        if (u && !seenUrls.has(u)) {
          seenUrls.add(u);
          embedServers.push({ label: `Server ${embedServers.length + 1}`, url: u });
        }
      }

      const extractMeta = (label: string) => {
        const re = new RegExp(
          `<span[^>]*class=["']meta-label["'][^>]*>\\s*${label}\\s*<\\/span>\\s*<span[^>]*class=["']meta-value[^"']*["'][^>]*>([\\s\\S]*?)<\\/span>`,
          'i'
        );
        const m = html.match(re);
        return m ? decodeHtmlEntities(m[1]) : '';
      };

      const screenshots: string[] = [];
      for (const m of html.matchAll(/openLightbox\(['"](https?:\/\/[^'"]+)['"]\)/gi)) {
        if (m[1] && !screenshots.includes(m[1])) {
          screenshots.push(m[1]);
        }
      }

      const cast: Array<{ name: string; role: string; photo: string }> = [];
      const castRegex =
        /<div class=["']cast-card["']>[\s\S]*?data-src=["'](https?:\/\/[^"']+)["'][\s\S]*?<span class=["']cast-name["']>([\s\S]*?)<\/span>\s*<span class=["']cast-role["']>([\s\S]*?)<\/span>/gi;
      for (const m of html.matchAll(castRegex)) {
        const photo = m[1].trim();
        const name = decodeHtmlEntities(m[2]);
        const role = decodeHtmlEntities(m[3]) || 'Actor';
        if (name && photo) {
          cast.push({ name, role, photo });
        }
      }

      const downloads: Array<{ label: string; url: string }> = [];
      const dlRegex =
        /<a[^>]*class=["'][^"']*dl-v2-btn[^"']*["'][^>]*href=["'](https?:\/\/[^"']+)["'][\s\S]*?<div class=["']dl-v2-title["']>([\s\S]*?)<\/div>/gi;
      for (const m of html.matchAll(dlRegex)) {
        const url = m[1].trim();
        const label = decodeHtmlEntities(m[2]);
        if (url && label) {
          downloads.push({ label, url });
        }
      }

      let seasonsData: any[] = [];
      const seasonsMatch = html.match(/const\s+seasonsData\s*=\s*(\[[\s\S]*?\]);/);
      if (seasonsMatch?.[1]) {
        try {
          seasonsData = JSON.parse(seasonsMatch[1]);
        } catch {
          // ignore
        }
      }

      const ratingMatch = html.match(/class=["']rating-score["'][^>]*>([\d.]+)<\/span>/i);

      return {
        ok: true,
        embedServers,
        seasonsData,
        year: extractMeta('Year'),
        genre: extractMeta('Genre'),
        runtime: extractMeta('Runtime'),
        director: extractMeta('Director'),
        release: extractMeta('Release'),
        rating: ratingMatch ? ratingMatch[1].trim() : '',
        screenshots,
        cast,
        downloads,
      };
    } catch {
      return { ok: false };
    }
  }

  return { ok: true, requests: [] };
}

