import { spawn, type ChildProcess } from 'child_process';
import crypto from 'crypto';
import express from 'express';
import fs from 'fs';
import path from 'path';
import { Readable } from 'stream';
import { fileURLToPath } from 'url';
import { createServer as createViteServer } from 'vite';
import { ALL_CATEGORIES, INITIAL_FALLBACK_MOVIES } from './src/data/categories.ts';
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
} from './src/utils/timeAgo.ts';
import type {
  CastMember,
  DirectDownloadButton,
  EpisodeItem,
  GlobalMovieNotification,
  MovieBoxComingSoonItem,
  MovieBoxHomePayload,
  MovieBoxHomeShelf,
  MovieBoxLiveSportItem,
  MovieBoxQuickCategory,
  MovieCardItem,
  MovieDetailData,
  MovieDubOption,
  ServerNodeStatus,
  StreamSource,
  UserMovieRequest,
} from './src/types/cinema.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

process.on('uncaughtException', (err) => {
  console.error('Uncaught exception (kept server alive):', err?.message || err);
});

process.on('unhandledRejection', (reason) => {
  console.error('Unhandled rejection (kept server alive):', reason);
});

interface MirrorNodeConfig {
  id: string;
  name: string;
  region: string;
  origin: string;
}

const SERVER_NODES: MirrorNodeConfig[] = [
  { id: 'node-moviebox', name: 'MovieBox HD', region: 'movie-box.co 4K/1080p API', origin: 'https://movie-box.co' },
  { id: 'node-alpha', name: 'Node Alpha', region: 'BD-Fast Edge', origin: 'https://cmyyhb.movielinkbd.at' },
  { id: 'node-beta', name: 'Node Beta', region: 'SG-Ultra CDN', origin: 'https://4yer8f.movielinkbd.at' },
  { id: 'node-gamma', name: 'Node Gamma', region: 'Global Stream', origin: 'https://movielinkbd.tv' },
  { id: 'node-delta', name: 'Node Delta', region: 'Backup Core', origin: 'https://movielinkbd.one' },
  { id: 'node-myflix', name: 'Node MyFlix', region: 'BD-Dual Hub', origin: 'https://myflixbd.to' },
];

const PRIMARY_MIRROR_NODES = SERVER_NODES.filter((n) => n.id !== 'node-myflix' && n.id !== 'node-moviebox');
const MYFLIX_ORIGIN = 'https://myflixbd.to';
const MOVIEBOX_ORIGIN = 'https://movie-box.co';
const MOVIEBOX_BACKUP_ORIGIN = 'https://movieboxhd.net';
const MOVIEBOX_API_ORIGIN = 'https://movie-box.co';
const MOVIEBOX_FALLBACK_API_ORIGIN = 'https://h5-api.aoneroom.com';

interface CacheEntry<T> {
  data: T;
  expiresAt: number;
}

const FFMPEG_BIN = fs.existsSync('/usr/bin/ffmpeg')
  ? '/usr/bin/ffmpeg'
  : fs.existsSync('/usr/local/bin/ffmpeg')
    ? '/usr/local/bin/ffmpeg'
    : 'ffmpeg';

function pruneCacheMap<K, V>(map: Map<K, V>, maxEntries: number): void {
  if (map.size <= maxEntries) return;
  const excess = map.size - maxEntries;
  let removed = 0;
  for (const key of map.keys()) {
    map.delete(key);
    removed++;
    if (removed >= excess) break;
  }
}

const catalogCache = new Map<string, CacheEntry<{ items: MovieCardItem[]; maxPage: number; activeNodeId: string }>>();
const detailCache = new Map<string, CacheEntry<MovieDetailData>>();
const detailTitleCache = new Map<string, CacheEntry<MovieDetailData>>();
const imdbIdCache = new Map<string, string>();
let healthCache: CacheEntry<ServerNodeStatus[]> | null = null;
const mirrorHtmlCache = new Map<string, CacheEntry<{ html: string; finalOrigin: string; activeNodeId: string }>>();
const inFlightMirrorMap = new Map<string, Promise<{ html: string; finalOrigin: string; activeNodeId: string }>>();
const myFlixHtmlCache = new Map<string, CacheEntry<string>>();
const inFlightMyFlixMap = new Map<string, Promise<string>>();
const inFlightCatalogMap = new Map<string, Promise<any>>();

function sortSourcesFastestFirst(sources?: StreamSource[]): StreamSource[] {
  if (!Array.isArray(sources) || sources.length <= 1) return sources || [];
  const score = (src: StreamSource) => {
    const isEmbed =
      src.type === 'embed' ||
      /abyssplayer\.com|abysscdn\.com|vidsrc|multiembed|autoembed|myflix/i.test(`${src.url || ''} ${src.id || ''}`);
    if (isEmbed) return 400;
    const isMovieBox =
      src.id?.startsWith('mb-') || /\/api\/mb-stream|\/api\/mb-ep-stream/i.test(src.url || '');
    if (isMovieBox) {
      // movie-box.co direct H.264 MP4 streams always get highest priority for instant native <video> playback
      const baseMb = 4500;
      const sizeMatch = (src.name || '').match(/(\d+)\s*MB/i);
      const sizeMb = sizeMatch ? parseInt(sizeMatch[1], 10) : 0;
      const isHeavyFile = sizeMb > 350;
      if (src.quality === 720) return baseMb + 140;
      if (src.quality === 480) return baseMb + 135;
      if (src.quality === 360) return baseMb + 125;
      if (src.quality === 1080) return isHeavyFile ? baseMb + 80 : baseMb + 130;
      return baseMb + 100;
    }
    const isHevc = /\b(hevc|h\.?265|x265|10bit|av1)\b/i.test(`${src.name} ${src.qualityLabel}`);
    const isBestHeavy = /best\s*quality/i.test(src.qualityLabel || '');
    let s = isHevc ? 1400 : 3000;
    if (isBestHeavy) s -= 250;
    if (src.quality >= 360 && src.quality <= 576) s += 650;
    else if (src.quality === 720) s += 550;
    else if (src.quality === 1080) s += 400;
    else s += 150;
    return s;
  };
  return [...sources].sort((a, b) => score(b) - score(a));
}

function storeDetailInCaches(itemPath: string, det: MovieDetailData, expiresAt: number): void {
  if (!det || typeof det !== 'object') return;
  // Cap stream token cache at 12 minutes so signed fsldownload stream URLs never expire into HTTP 410 Gone
  const safeExpiresAt = Math.min(expiresAt, Date.now() + 12 * 60_000);
  if (Array.isArray(det.episodes)) {
    for (const ep of det.episodes) {
      if (Array.isArray(ep.sources)) {
        ep.sources = sortSourcesFastestFirst(ep.sources);
      }
    }
  }
  if (itemPath) {
    pruneCacheMap(detailCache, 180);
    detailCache.set(itemPath, { data: det, expiresAt: safeExpiresAt });
  }
  if (det.title && det.episodes?.length) {
    pruneCacheMap(detailTitleCache, 240);
    const canon = getCanonicalTitleKey(det.title);
    if (canon) detailTitleCache.set(canon, { data: det, expiresAt: safeExpiresAt });
    const base = extractBaseSeriesTitle(det.title).toLowerCase();
    if (base) detailTitleCache.set(base, { data: det, expiresAt: safeExpiresAt });
  }
}

function findCachedDetailByPathOrTitle(itemPath: string, rawTitle = ''): MovieDetailData | null {
  const now = Date.now();
  if (itemPath) {
    const hit = detailCache.get(itemPath);
    if (hit && hit.expiresAt > now && hit.data?.episodes?.length) {
      return hit.data;
    }
  }
  if (rawTitle) {
    const canon = getCanonicalTitleKey(rawTitle);
    const byCanon = canon ? detailTitleCache.get(canon) : undefined;
    if (byCanon && byCanon.expiresAt > now && byCanon.data?.episodes?.length) return byCanon.data;
    const base = extractBaseSeriesTitle(rawTitle).toLowerCase();
    const byBase = base ? detailTitleCache.get(base) : undefined;
    if (byBase && byBase.expiresAt > now && byBase.data?.episodes?.length) return byBase.data;
  }
  return null;
}

const movieRequestsStore: UserMovieRequest[] = [
  {
    id: 'req-1',
    title: 'Pushpa 2: The Rule (2025) [Bangla Dubbed 4K]',
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

const customBroadcastNotifications: GlobalMovieNotification[] = [];

function buildGlobalNotifications(): GlobalMovieNotification[] {
  const now = Date.now();
  const pool: MovieCardItem[] = [];
  const seenPaths = new Set<string>();
  const seenTitles = new Set<string>();

  for (const [key, entry] of catalogCache.entries()) {
    if (key.includes('adult18plus')) continue;
    for (const rawItem of entry.data.items.slice(0, 24)) {
      if (rawItem.isAdult) continue;
      const item = normalizeMovieCardItem(rawItem, now);
      const tKey = item.title.toLowerCase().replace(/[^a-z0-9\u0980-\u09ff]/g, '');
      if (!item.path || seenPaths.has(item.path) || (tKey && seenTitles.has(tKey))) continue;
      seenPaths.add(item.path);
      if (tKey) seenTitles.add(tKey);
      pool.push(item);
    }
  }

  if (pool.length < 10) {
    for (const rawItem of INITIAL_FALLBACK_MOVIES['/'] || []) {
      if (rawItem.isAdult) continue;
      const item = normalizeMovieCardItem(rawItem, now);
      const tKey = item.title.toLowerCase().replace(/[^a-z0-9\u0980-\u09ff]/g, '');
      if (!item.path || seenPaths.has(item.path) || (tKey && seenTitles.has(tKey))) continue;
      seenPaths.add(item.path);
      if (tKey) seenTitles.add(tKey);
      pool.push(item);
    }
  }

  const recentUploads = sortItemsByRecentUpload(pool, now).slice(0, 12);
  const topRatedPopular = sortItemsByHighRating(pool, now).slice(0, 12);

  const notifications: GlobalMovieNotification[] = [...customBroadcastNotifications];
  const notifSeen = new Set<string>(notifications.map((n) => n.movie.path));

  // Interleave New Uploads and Top-Rated Popular Movies so everyone gets both immediately
  const maxLen = Math.max(recentUploads.length, topRatedPopular.length);
  for (let i = 0; i < maxLen; i++) {
    const newItem = recentUploads[i];
    if (newItem && !notifSeen.has(`new::${newItem.path}`)) {
      notifSeen.add(`new::${newItem.path}`);
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
    if (popItem && !notifSeen.has(`pop::${popItem.path}`)) {
      notifSeen.add(`pop::${popItem.path}`);
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

  return notifications.slice(0, 28);
}

function encodeGatewayUrl(rawUrl: string): string {
  if (!rawUrl) return '';
  try {
    const token = Buffer.from(rawUrl, 'utf8').toString('base64url');
    return `/api/go?t=${token}`;
  } catch {
    return rawUrl;
  }
}

function decodeGatewayToken(token: string): string {
  try {
    return Buffer.from(token, 'base64url').toString('utf8');
  } catch {
    return '';
  }
}

/**
 * Strips any upstream site names, domains, watermarks, or tags from scraped text.
 */
function sanitizeBrandText(input: string): string {
  if (!input) return '';
  return input
    .replace(/https?:\/\/[^\s"'<>]*(?:movielinkbd|myflixbd)[^\s"'<>]*/gi, '')
    .replace(/\b[a-z0-9-]*\.?(?:movielinkbd|myflixbd)\.[a-z]{2,6}\b/gi, 'CinePulse')
    .replace(/movielinkbd|myflixbd|nexaflox/gi, 'CinePulse')
    .replace(/\bmlbd\b/gi, 'CP')
    .replace(/\s*watch\s+online\s+and\s+download\s*(?:["“”']?web-dl["“”']?|["“”']?hdtc["“”']?|["“”']?hd["“”']?|["“”']?4k["“”']?)?\s*…?/gi, '')
    .replace(/\s*watch\s+online\s*…?/gi, '')
    .replace(/\s*[“”"'](?:web(?:-?dl|rip)?|hdtc|hdts|4k|hd)[^"”]*[”"']?\s*…?\s*$/gi, '')
    .replace(/\s+[–—-]\s*$/g, '')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

function decodeMlbdCipher(base64Str: string, hexSeed: string, rounds: number): string {
  try {
    let x = parseInt(hexSeed, 16) >>> 0;
    for (let i = 0; i < rounds; i++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
    }
    const raw = Buffer.from(base64Str.trim(), 'base64');
    const out = Buffer.alloc(raw.length);
    for (let j = 0; j < raw.length; j++) {
      x = (Math.imul(x, 1103515245) + 12345) >>> 0;
      out[j] = raw[j] ^ ((x >>> 16) & 255);
    }
    return out.toString('utf8');
  } catch {
    return '';
  }
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

function getOrderedNodes(preferredNodeId?: string): MirrorNodeConfig[] {
  if (!preferredNodeId || preferredNodeId === 'node-myflix') return PRIMARY_MIRROR_NODES;
  const preferred = PRIMARY_MIRROR_NODES.find((n) => n.id === preferredNodeId);
  if (!preferred) return PRIMARY_MIRROR_NODES;
  return [preferred, ...PRIMARY_MIRROR_NODES.filter((n) => n.id !== preferredNodeId)];
}

async function fetchFromMirrors(
  targetPath: string,
  preferredNodeId?: string
): Promise<{ html: string; finalOrigin: string; activeNodeId: string }> {
  const cleanPath = targetPath.startsWith('http')
    ? new URL(targetPath).pathname + new URL(targetPath).search
    : targetPath.startsWith('/')
      ? targetPath
      : `/${targetPath}`;

  const orderedNodes = getOrderedNodes(preferredNodeId);

  const attemptNode = async (node: MirrorNodeConfig, timeoutMs: number) => {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeoutMs);
    try {
      const url = `${node.origin}${cleanPath}`;
      const res = await fetch(url, {
        signal: controller.signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
          Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
          'Accept-Language': 'en-US,en;q=0.9,bn;q=0.8',
          Cookie: 'mlbd_show18=1; hide18On=false',
          Referer: `${node.origin}/`,
        },
      });
      if (!res.ok && res.status !== 404) {
        throw new Error(`HTTP ${res.status}`);
      }
      const html = await res.text();
      if (
        !html ||
        html.length < 1200 ||
        (!html.includes('movie-card') &&
          !html.includes('mlbdInlinePlayerData') &&
          !html.includes('<div class="n">404</div>'))
      ) {
        throw new Error('Challenge or incomplete HTML');
      }
      const finalOrigin = new URL(res.url || url).origin;
      return { html, finalOrigin, activeNodeId: node.id };
    } finally {
      clearTimeout(timer);
    }
  };

  const mirrorKey = `${preferredNodeId || 'auto'}::${cleanPath}`;
  const cachedMirror = mirrorHtmlCache.get(mirrorKey);
  if (cachedMirror && cachedMirror.expiresAt > Date.now()) {
    return cachedMirror.data;
  }
  const existingFlight = inFlightMirrorMap.get(mirrorKey);
  if (existingFlight) {
    return existingFlight;
  }

  const runMirrorFetch = (async () => {
    // Race top 2 mirror nodes in parallel for sub-second response!
    try {
      const winner = await Promise.any(
        orderedNodes.slice(0, 2).map((node) => attemptNode(node, 4500))
      );
      pruneCacheMap(mirrorHtmlCache, 60);
      mirrorHtmlCache.set(mirrorKey, { data: winner, expiresAt: Date.now() + 45_000 });
      return winner;
    } catch {
      for (const node of orderedNodes.slice(2)) {
        try {
          const fallbackWinner = await attemptNode(node, 5000);
          pruneCacheMap(mirrorHtmlCache, 60);
          mirrorHtmlCache.set(mirrorKey, { data: fallbackWinner, expiresAt: Date.now() + 45_000 });
          return fallbackWinner;
        } catch {
          // try next
        }
      }
    }
    throw new Error('All cinema stream nodes unreachable');
  })();

  inFlightMirrorMap.set(mirrorKey, runMirrorFetch);
  try {
    return await runMirrorFetch;
  } finally {
    inFlightMirrorMap.delete(mirrorKey);
  }
}

function parseMovieCards(html: string): { items: MovieCardItem[]; maxPage: number } {
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

    let itemPath = '';
    try {
      itemPath = rawHref.startsWith('http')
        ? new URL(rawHref).pathname
        : rawHref.startsWith('/')
          ? rawHref
          : `/${rawHref}`;
    } catch {
      continue;
    }

    if (seenPaths.has(itemPath)) continue;

    const title = decodeHtmlEntities(titleMatch[1]);
    if (!title) continue;

    const titleKey = getCanonicalTitleKey(title);
    if (titleKey && seenPaths.has(`title::${titleKey}`)) continue;

    const posterMatch =
      chunk.match(/data-src=["'](https?:\/\/[^"']+)["']/i) ||
      chunk.match(/src=["'](https?:\/\/[^"']+)["']/i);
    const poster = posterMatch ? posterMatch[1].trim() : '';
    const posterKey = poster ? poster.toLowerCase().split('?')[0].trim() : '';
    if (posterKey && seenPaths.has(`poster::${posterKey}`)) continue;

    seenPaths.add(itemPath);
    if (titleKey) seenPaths.add(`title::${titleKey}`);
    if (posterKey) seenPaths.add(`poster::${posterKey}`);

    const quality = decodeHtmlEntities(
      (chunk.match(/<span class=["']quality["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'WEB-DL'
    );
    const language = decodeHtmlEntities(
      (chunk.match(/<span class=["']language["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'MULTI'
    );
    const views = decodeHtmlEntities(
      (chunk.match(/<span class=["']views-badge-top["'][^>]*>[\s\S]*?<\/i>\s*([^<]+)<\/span>/i) || [])[1] || '2.4K'
    );
    const rawTimeAgo = decodeHtmlEntities(
      (chunk.match(/<div class=["']upload-time["'][^>]*>([\s\S]*?)<\/div>/i) || [])[1] || 'Recently added'
    );
    const rawEpisodePill = decodeHtmlEntities(
      (chunk.match(/<span class=["']badge ep-badge[^"']*["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || ''
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

    // Extract real R2 upload Unix timestamp if embedded in poster URL (e.g. poster_v778gm1793478302.webp)
    const r2TsMatch = poster.match(/poster_[a-z0-9_]*?(17\d{8})\./i);
    const r2EpochMs = r2TsMatch ? parseInt(r2TsMatch[1], 10) * 1000 : 0;
    const nowMs = Date.now();
    let pathHash = 2166136261 >>> 0;
    for (let c = 0; c < itemPath.length; c++) {
      pathHash ^= itemPath.charCodeAt(c);
      pathHash = Math.imul(pathHash, 16777619) >>> 0;
    }
    const minuteJitter = cleanedTime.minutesAgo >= 60 ? (pathHash % 47) : 0;
    const computedUploadMs =
      r2EpochMs > nowMs - 48 * 3600_000 && r2EpochMs <= nowMs
        ? r2EpochMs
        : nowMs - (cleanedTime.minutesAgo + minuteJitter) * 60_000;

    items.push({
      id: itemPath.replace(/[^a-zA-Z0-9_-]/g, '_'),
      title,
      // Never expose upstream URL; keep clean relative path
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
      uploadedAtMs: computedUploadMs,
    });
  }

  const pageMatches = [...body.matchAll(/\/page\/(\d+)/g)]
    .map((m) => Number(m[1]))
    .filter((n) => !isNaN(n) && n > 0 && n <= 2000);
  const maxPage = pageMatches.length > 0 ? Math.max(...pageMatches) : 520;

  return { items, maxPage };
}

function parseMovieDetail(html: string, itemPath: string, origin: string): MovieDetailData {
  let inlineData: any = null;
  const playerScriptMatch = html.match(
    /<script[^>]*id=["']mlbdInlinePlayerData["'][^>]*data-s=["']([^"']+)["'][^>]*data-r=["'](\d+)["'][^>]*>([\s\S]*?)<\/script>/i
  );
  if (playerScriptMatch) {
    const decodedJson = decodeMlbdCipher(
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
  const dlRegex = /<a[^>]*data-dl=["']([^"']+)["'][^>]*data-ds=["']([^"']+)["'][^>]*data-dr=["'](\d+)["'][^>]*>([\s\S]*?)<\/a>/gi;
  for (const match of html.matchAll(dlRegex)) {
    const decodedHref = decodeMlbdCipher(match[1], match[2], parseInt(match[3], 10) || 300);
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
    (html.match(/<div class=["']image-container-view["'][\s\S]*?<img[^>]+src=["'](https?:\/\/[^"']+)["']/i) || [])[1] ||
    '';

  const qualityNote = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<div class=["']movie-info-view["'][\s\S]*?<p[^>]*>([\s\S]*?)<\/p>/i) || [])[1] || ''
    )
  );

  const extractInfoLine = (keyword: string): string => {
    const regex = new RegExp(`<p class=["']info-line["'][^>]*>[\\s\\S]*?${keyword}:?<\\/b>([\\s\\S]*?)<\\/p>`, 'i');
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
  const castRegex = /<a class=["']mlbd-cast__p["'][^>]+href=["']([^"']+)["'][^>]*>[\s\S]*?<img[^>]+src=["']([^"']+)["'][^>]*>[\s\S]*?<b>([\s\S]*?)<\/b>[\s\S]*?<small>([\s\S]*?)<\/small>/gi;
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

  let communityScore: MovieDetailData['communityScore'] | undefined;
  const voteMatch = html.match(/data-summary=["']([^"']+)["']/i);
  if (voteMatch) {
    try {
      const parsedVote = JSON.parse(decodeHtmlEntities(voteMatch[1]));
      communityScore = {
        recommendedPercent: Number(parsedVote.recommended_percent) || 88,
        totalVotes: Number(parsedVote.total) || 24,
        verdict: sanitizeBrandText(parsedVote.verdict || 'দর্শকদের পছন্দ'),
      };
    } catch {
      // ignore
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
              downloadUrl: encodeGatewayUrl(fullDlUrl),
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

    // Parse episode range or season from label if not explicitly set
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
      ep.range_start !== null && ep.range_start !== undefined
        ? Number(ep.range_start)
        : number;
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
    communityScore,
  };
}

function extractBaseSeriesTitle(rawTitle: string): string {
  return String(rawTitle || '')
    .replace(/\[.*?\]|\(.*?\)/g, ' ')
    .replace(/\b(?:S\d+|Season\s*\d+(?:-\d+)?|Ep(?:isode)?\s*\d+(?:-\d+)?|Complete(?:d)?|Added|Full\s*HD|ORG|Hindi|Bangla|Bengali|Dual|Multi|Audio|Watch|Online|Download|WEB-DL|HDTC|4K|The\s*Movie)\b/gi, ' ')
    .replace(/[:\-–—|]+/g, ' ')
    .replace(/\s{2,}/g, ' ')
    .trim();
}

function mapCategoryToMyFlixPath(rawPath: string, page = 1, search = ''): string {
  if (search) {
    return page > 1
      ? `/page/${page}/?s=${encodeURIComponent(search)}`
      : `/?s=${encodeURIComponent(search)}`;
  }

  const p = (rawPath || '/').toLowerCase().replace(/\/page\/\d+\/?$/, '').replace(/\/+$/, '') || '/';
  let mfBase = '/';

  if (p === '/' || p === '/home' || p === '/movies' || p === '/hot-dhamaka' || p === '/new-uploads' || p === '/new-releases' || p === '/mostwatch/7d') mfBase = '/';
  else if (p.includes('bangla-dubbed') || p.includes('bangladubbed')) mfBase = '/movie-genre/bangla-dubbed/';
  else if (p.includes('bangla') || p.includes('bengali') || p.includes('kolkata')) mfBase = '/movie-genre/bangla/';
  else if (p.includes('hindi-dubbed') || p.includes('hindidubbed') || p.includes('dual-audio')) mfBase = '/movie-genre/hindi-dubbed/';
  else if (p.includes('bollywood') || p.includes('hindi')) mfBase = '/movie-genre/hindi/';
  else if (p.includes('south') || p.includes('tamil') || p.includes('telugu') || p.includes('malayalam') || p.includes('kannada'))
    mfBase = '/movie-genre/south-indian/';
  else if (p.includes('hollywood') || p.includes('english')) mfBase = '/movie-genre/hollywood/';
  else if (p.includes('anime')) mfBase = '/tv-genre/anime/';
  else if (p.includes('animation') || p.includes('family')) mfBase = '/movie-genre/animation/';
  else if (p.includes('drama') || p.includes('korean') || p.includes('k-drama') || p.includes('chinese') || p.includes('turkish'))
    mfBase = '/tv-genre/k-drama/';
  else if (p.includes('series') || p.includes('ongoing') || p.includes('tv')) mfBase = '/tv-show/';
  else if (p.includes('action') || p.includes('superhero')) mfBase = '/movie-genre/action/';
  else if (p.includes('thriller') || p.includes('suspense') || p.includes('survival')) mfBase = '/movie-genre/thriller/';
  else if (p.includes('horror')) mfBase = '/movie-genre/horror/';
  else if (p.includes('romance')) mfBase = '/movie-genre/romance/';
  else if (p.includes('comedy')) mfBase = '/movie-genre/comedy/';
  else if (p.includes('crime')) mfBase = '/movie-genre/crime/';
  else if (p.includes('sci-fi')) mfBase = '/movie-genre/sci-fi/';
  else if (p.includes('adventure')) mfBase = '/movie-genre/adventure/';
  else if (p.includes('fantasy')) mfBase = '/movie-genre/fantasy/';
  else if (p.includes('mystery')) mfBase = '/movie-genre/mystery/';
  else {
    const slug = p.split('/').filter(Boolean).pop() || '';
    if (slug && slug !== 'adult18plus') {
      return page > 1 ? `/page/${page}/?s=${encodeURIComponent(slug.replace(/-/g, ' '))}` : `/?s=${encodeURIComponent(slug.replace(/-/g, ' '))}`;
    }
    return '';
  }

  if (page > 1) {
    const clean = mfBase === '/' ? '' : mfBase.replace(/\/+$/, '');
    return `${clean}/page/${page}/`;
  }
  return mfBase;
}

async function fetchMyFlixHtml(mfPath: string, timeoutMs = 4500): Promise<string> {
  if (!mfPath) throw new Error('Empty MyFlix path');
  const cleanPath = mfPath.startsWith('http')
    ? new URL(mfPath).pathname + new URL(mfPath).search
    : mfPath.startsWith('/')
      ? mfPath
      : `/${mfPath}`;

  const cached = myFlixHtmlCache.get(cleanPath);
  if (cached && cached.expiresAt > Date.now()) {
    return cached.data;
  }
  const existing = inFlightMyFlixMap.get(cleanPath);
  if (existing) {
    return existing;
  }

  const promise = (async () => {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeoutMs);
    try {
      const url = `${MYFLIX_ORIGIN}${cleanPath}`;
      const res = await fetch(url, {
        signal: controller.signal,
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
          Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
          'Accept-Language': 'en-US,en;q=0.9,bn;q=0.8',
          Referer: `${MYFLIX_ORIGIN}/`,
        },
      });
      if (!res.ok) throw new Error(`MyFlix HTTP ${res.status}`);
      const html = await res.text();
      if (!html || html.length < 1000) throw new Error('Incomplete MyFlix HTML');
      pruneCacheMap(myFlixHtmlCache, 50);
      myFlixHtmlCache.set(cleanPath, { data: html, expiresAt: Date.now() + 45_000 });
      return html;
    } finally {
      clearTimeout(timer);
    }
  })();

  inFlightMyFlixMap.set(cleanPath, promise);
  try {
    return await promise;
  } finally {
    inFlightMyFlixMap.delete(cleanPath);
  }
}

function parseMyFlixCards(html: string): { items: MovieCardItem[]; maxPage: number } {
  const bodyIdx = html.indexOf('<body');
  const body = bodyIdx >= 0 ? html.slice(bodyIdx) : html;
  const cardRegex = /<a\s+href=["'](https?:\/\/myflixbd\.to\/(?:movie|tv-show)\/[^"']+)["'][^>]*class=["'][^"']*movie-card[^"']*["'][^>]*>([\s\S]*?)<\/a>/gi;
  const items: MovieCardItem[] = [];
  const seenPaths = new Set<string>();

  for (const match of body.matchAll(cardRegex)) {
    const rawHref = match[1].trim();
    const chunk = match[2];
    if (!rawHref) continue;

    let cleanPathname = '';
    try {
      cleanPathname = new URL(rawHref).pathname.replace(/^\/+|\/+$/g, '');
    } catch {
      continue;
    }
    if (!cleanPathname) continue;

    const itemPath = `/mf/${cleanPathname}`;
    if (seenPaths.has(itemPath)) continue;
    seenPaths.add(itemPath);

    const titleMatch =
      chunk.match(/<h3[^>]*class=["'][^"']*movie-title[^"']*["'][^>]*>([\s\S]*?)<\/h3>/i) ||
      chunk.match(/alt=["']([^"']+)["']/i);
    if (!titleMatch) continue;

    const title = decodeHtmlEntities(titleMatch[1]);
    if (!title) continue;

    const posterMatch =
      chunk.match(/data-src=["'](https?:\/\/[^"']+)["']/i) ||
      chunk.match(/src=["'](https?:\/\/[^"']+)["']/i);
    const poster = posterMatch ? posterMatch[1].trim() : '';

    const quality = decodeHtmlEntities(
      (chunk.match(/card-badge-quality["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'WEB-DL'
    );
    const language = decodeHtmlEntities(
      (chunk.match(/card-badge-lang["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || 'MULTI'
    );
    const epBadge = decodeHtmlEntities(
      (chunk.match(/card-badge-ep["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || ''
    );
    const ratingBadge = decodeHtmlEntities(
      (chunk.match(/card-badge-rating["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || ''
    );
    const catBadge = decodeHtmlEntities(
      (chunk.match(/card-badge-category["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || ''
    ).toUpperCase();

    let typeBadge: 'MOVIE' | 'SERIES' | 'ANIME' | 'DRAMA' = 'MOVIE';
    if (catBadge.includes('ANIME') || title.toLowerCase().includes('anime')) typeBadge = 'ANIME';
    else if (catBadge.includes('DRAMA') || language.toUpperCase().includes('KOREAN')) typeBadge = 'DRAMA';
    else if (
      catBadge.includes('SERIES') ||
      cleanPathname.startsWith('tv-show/') ||
      Boolean(epBadge) ||
      /season\s*\d+/i.test(title)
    ) {
      typeBadge = 'SERIES';
    }

    let mfHash = 2166136261 >>> 0;
    for (let c = 0; c < itemPath.length; c++) {
      mfHash ^= itemPath.charCodeAt(c);
      mfHash = Math.imul(mfHash, 16777619) >>> 0;
    }
    const mfYearMatch = title.match(/\((19\d{2}|20\d{2})\)/);
    const mfYearNum = mfYearMatch ? parseInt(mfYearMatch[1], 10) : 2026;
    const isRecentMf = mfYearNum >= 2025 || Boolean(epBadge);
    const mfMinsAgo = isRecentMf
      ? 24 + items.length * 41 + (mfHash % 29)
      : Math.max(2880, (2026 - mfYearNum) * 525600);
    const mfTimeLabel = isRecentMf
      ? mfMinsAgo < 60
        ? `${mfMinsAgo} mins ago`
        : `${Math.floor(mfMinsAgo / 60)} hours ago`
      : `${mfYearNum}`;

    items.push({
      id: itemPath.replace(/[^a-zA-Z0-9_-]/g, '_'),
      title,
      url: itemPath,
      path: itemPath,
      poster,
      quality: quality || 'WEB-DL',
      views: ratingBadge || '★ 8.1',
      language: language || 'MULTI',
      typeBadge,
      timeAgo: mfTimeLabel,
      episodePill: epBadge || (quality.toUpperCase().includes('SEASON') ? quality : ''),
      isPinned: chunk.includes('card-badge-trending') && isRecentMf,
      isAdult: false,
      uploadedAtMs: Date.now() - mfMinsAgo * 60_000,
    });
  }

  const pageMatches = [...body.matchAll(/\/page\/(\d+)/g)]
    .map((m) => Number(m[1]))
    .filter((n) => !isNaN(n) && n > 0 && n <= 2000);
  const maxPage = pageMatches.length > 0 ? Math.max(...pageMatches) : 342;

  return { items, maxPage };
}

function mergeCatalogItems(
  primaryItems: MovieCardItem[],
  secondaryItems: MovieCardItem[],
  preferSecondaryFirst = false
): MovieCardItem[] {
  const firstList = preferSecondaryFirst ? secondaryItems : primaryItems;
  const secondList = preferSecondaryFirst ? primaryItems : secondaryItems;
  const interleaved: MovieCardItem[] = [];
  const maxLen = Math.max(firstList.length, secondList.length);
  for (let i = 0; i < maxLen; i++) {
    if (i < firstList.length) interleaved.push(firstList[i]);
    if (i < secondList.length) interleaved.push(secondList[i]);
  }
  return deduplicateMovieCards(interleaved);
}

function parseMyFlixDetail(html: string, itemPath: string): MovieDetailData {
  const rawTitle = decodeHtmlEntities(
    (html.match(/<h1[^>]*class=["'][^"']*movie-title-text[^"']*["'][^>]*>([\s\S]*?)<\/h1>/i) ||
      html.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i) ||
      [])[1] || 'Cinema Title'
  );
  const title = sanitizeBrandText(rawTitle);

  const poster =
    (html.match(/<div class=["']poster-wrapper["'][\s\S]*?data-src=["'](https?:\/\/[^"']+)["']/i) ||
      html.match(/<div class=["']poster-wrapper["'][\s\S]*?src=["'](https?:\/\/[^"']+)["']/i) ||
      html.match(/property=["']og:image["']\s+content=["'](https?:\/\/[^"']+)["']/i) ||
      [])[1] || '';

  const extractMetaGrid = (label: string): string => {
    const regex = new RegExp(
      `<span class=["']meta-label["'][^>]*>\\s*${label}\\s*<\\/span>\\s*<span class=["']meta-value["'][^>]*>([\\s\\S]*?)<\\/span>`,
      'i'
    );
    const m = html.match(regex);
    return m ? decodeHtmlEntities(m[1]) : '';
  };

  const year = extractMetaGrid('Year') || '2026';
  const genre = extractMetaGrid('Genre') || 'Action, Drama, Thriller';
  const runtime = extractMetaGrid('Runtime') || '';
  const releaseDate = extractMetaGrid('Release') || year;

  const langBracketMatch = rawTitle.match(/\[(.*?)\]/);
  const language = langBracketMatch ? decodeHtmlEntities(langBracketMatch[1]) : 'Multi Audio';
  const quality =
    decodeHtmlEntities((html.match(/<div class=["']badge-hd["'][^>]*>([\s\S]*?)<\/div>/i) || [])[1] || '') ||
    'WEB-DL';

  const storyline = sanitizeBrandText(
    decodeHtmlEntities(
      (html.match(/<p id=["']synopsisText["'][^>]*>([\s\S]*?)<\/p>/i) ||
        html.match(/<div class=["']synopsis-box["'][\s\S]*?<p[^>]*>([\s\S]*?)<\/p>/i) ||
        [])[1] || ''
    )
  );

  const ratingScoreNum = parseFloat(
    (html.match(/<span class=["']rating-score["'][^>]*>([\s\S]*?)<\/span>/i) || [])[1] || '8.4'
  );
  const communityScore = {
    recommendedPercent: Math.min(99, Math.max(70, Math.round((ratingScoreNum || 8.4) * 10))),
    totalVotes: 310,
    verdict: 'দর্শকদের পছন্দ',
  };

  const cast: CastMember[] = [];
  const castRegex =
    /<div class=["']cast-card["'][^>]*>[\s\S]*?(?:data-src|src)=["'](https?:\/\/[^"']+)["'][\s\S]*?<p class=["']cast-name["'][^>]*>([\s\S]*?)<\/p>/gi;
  for (const m of html.matchAll(castRegex)) {
    const actorName = decodeHtmlEntities(m[2]);
    if (actorName) {
      cast.push({
        url: `/search?q=${encodeURIComponent(actorName)}`,
        photo: m[1],
        name: actorName,
        role: 'Cast',
      });
    }
  }

  const downloadButtons: DirectDownloadButton[] = [];
  const dlBtnRegex =
    /<a[^>]*class=["'][^"']*dl-v2-btn[^"']*["'][^>]*href=["']([^"']+)["'][^>]*>[\s\S]*?<div class=["']dl-v2-title["'][^>]*>([\s\S]*?)<\/div>/gi;
  for (const m of html.matchAll(dlBtnRegex)) {
    const rawDlHref = m[1].trim();
    const rawLabel = decodeHtmlEntities(m[2]);
    if (!rawDlHref || rawDlHref === '#') continue;
    const qMatch = rawLabel.match(/(2160p|4k|1080p|720p|480p)/i);
    const qLabel = qMatch ? qMatch[1] : 'HD';
    downloadButtons.push({
      label: sanitizeBrandText(rawLabel || `Download ${qLabel}`),
      url: encodeGatewayUrl(rawDlHref),
      quality: qLabel,
      size: runtime || 'Full HD',
    });
  }

  const episodes: EpisodeItem[] = [];

  // 1. Check if `seasonsData` JSON array is embedded (for Series / K-Drama / Anime)
  const seasonsMatch = html.match(/(?:const|let|var)\s+seasonsData\s*=\s*(\[\s*\{[\s\S]*?\}\s*\])\s*;?/);
  if (seasonsMatch) {
    try {
      const parsedSeasons = JSON.parse(seasonsMatch[1]);
      if (Array.isArray(parsedSeasons)) {
        let globalIdx = 0;
        for (const sObj of parsedSeasons) {
          const seasonNum = Number(sObj?.index) || 1;
          const epArray = Array.isArray(sObj?.episodes) ? sObj.episodes : [];
          for (const epObj of epArray) {
            globalIdx++;
            const epNum = Number(epObj?.index) || globalIdx;
            const epTitle = decodeHtmlEntities(String(epObj?.title || `Episode ${epNum}`));
            const servers = Array.isArray(epObj?.servers) ? epObj.servers : [];
            const sources: StreamSource[] = servers
              .filter((srv: any) => srv && srv.url)
              .map((srv: any, sIdx: number) => {
                const srvUrl = String(srv.url).replace(/\\\//g, '/').trim();
                const fallbackDl = downloadButtons[0]?.url || encodeGatewayUrl(srvUrl);
                return {
                  id: `mf-s${seasonNum}-e${epNum}-srv${sIdx}`,
                  quality: 1080,
                  qualityLabel: decodeHtmlEntities(String(srv.label || `Server ${sIdx + 1} (HD)`)),
                  audio: language,
                  audioLanguages: [language],
                  provider: `Stream Server #${sIdx + 1}`,
                  url: srvUrl,
                  downloadUrl: fallbackDl,
                  type: 'embed',
                  name: `${title} - ${epTitle}`,
                };
              });

            if (sources.length > 0) {
              episodes.push({
                id: `mf-ep-${seasonNum}-${epNum}`,
                label: epTitle.toLowerCase().includes('all')
                  ? `Season ${seasonNum} • Full Stream`
                  : `S${String(seasonNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • ${epTitle}`,
                number: epNum,
                rangeStart: epNum,
                rangeEnd: epNum,
                season: seasonNum,
                kind: 'episode',
                sources,
              });
            }
          }
        }
      }
    } catch {
      // ignore JSON parse issues
    }
  }

  // 2. Also extract inline `.btn-server[data-url]` or `.video-container iframe` for Movies
  if (episodes.length === 0) {
    const serverUrls: Array<{ label: string; url: string }> = [];
    const seenSrv = new Set<string>();

    const btnSrvRegex = /<button[^>]*class=["'][^"']*btn-server[^"']*["'][^>]*data-url=["']([^"']+)["'][^>]*>([\s\S]*?)<\/button>/gi;
    for (const m of html.matchAll(btnSrvRegex)) {
      const u = m[1].trim();
      const lbl = decodeHtmlEntities(m[2]) || `Server ${serverUrls.length + 1}`;
      if (u && u.startsWith('http') && !seenSrv.has(u)) {
        seenSrv.add(u);
        serverUrls.push({ label: lbl, url: u });
      }
    }

    const iframeMatch =
      html.match(/<div class=["']video-container["'][\s\S]*?<iframe[^>]+data-litespeed-src=["'](https?:\/\/[^"']+)["']/i) ||
      html.match(/<div class=["']video-container["'][\s\S]*?<iframe[^>]+src=["'](https?:\/\/[^"']+)["']/i);
    if (iframeMatch && iframeMatch[1] && !seenSrv.has(iframeMatch[1])) {
      seenSrv.add(iframeMatch[1]);
      serverUrls.push({ label: 'Server 1 (HD)', url: iframeMatch[1].trim() });
    }

    if (serverUrls.length > 0) {
      const fallbackDl = downloadButtons[0]?.url || encodeGatewayUrl(serverUrls[0].url);
      episodes.push({
        id: 'mf-movie-main',
        label: 'Full Movie',
        number: 1,
        rangeStart: 1,
        rangeEnd: 1,
        season: null,
        kind: 'movie',
        sources: serverUrls.map((srv, idx) => ({
          id: `mf-movie-srv-${idx}`,
          quality: idx === 0 ? 1080 : 720,
          qualityLabel: srv.label,
          audio: language,
          audioLanguages: [language],
          provider: srv.label,
          url: srv.url,
          downloadUrl: fallbackDl,
          type: 'embed',
          name: `${title} (${srv.label})`,
        })),
      });
    }
  }

  return {
    title,
    url: itemPath,
    poster,
    qualityNote: `${quality} • ${language}${runtime ? ` • ${runtime}` : ''}`,
    typeBadge: itemPath.includes('/tv-show/') || episodes.length > 1 ? 'SERIES' : 'MOVIE',
    language,
    quality,
    genre,
    resolution: '1080p | 720p | 480p',
    releaseDate,
    storyline,
    youtubeTrailerId: '',
    screenshots: [],
    episodes,
    downloadButtons,
    cast: cast.slice(0, 12),
    communityScore,
  };
}

// ============================================================================
// MovieBox HD (https://movie-box.co + movieboxhd.net + h5-api.aoneroom.com) Full Content Engine
// ============================================================================
let cachedMovieBoxToken = '';
let cachedMovieBoxTokenExpiresAt = 0;
let cachedMovieBoxHomeSections: Array<{ title: string; type: string; subjects: any[] }> = [];
let cachedMovieBoxHomeExpiresAt = 0;
let cachedMovieBoxHomePayload: MovieBoxHomePayload | null = null;
let cachedMovieBoxHomePayloadExpiresAt = 0;
let inFlightMovieBoxHomePromise: Promise<MovieBoxHomePayload> | null = null;

function extractMovieBoxNuxtOperatingList(html: string): any[] {
  try {
    const m = html.match(/<script[^>]*id="__NUXT_DATA__"[^>]*>([\s\S]*?)<\/script>/i);
    if (!m?.[1]) return [];
    const arr = JSON.parse(m[1]);
    if (!Array.isArray(arr)) return [];

    const resolve = (idx: any, depth = 0): any => {
      if (depth > 8 || typeof idx !== 'number' || idx < 0 || idx >= arr.length) return idx;
      const val = arr[idx];
      if (Array.isArray(val)) {
        if (val[0] === 'ShallowReactive' || val[0] === 'Reactive' || val[0] === 'Ref') {
          return resolve(val[1], depth + 1);
        }
        return val.map((v) => resolve(v, depth + 1));
      }
      if (val && typeof val === 'object') {
        const out: Record<string, any> = {};
        for (const [k, v] of Object.entries(val)) {
          out[k] = resolve(v, depth + 1);
        }
        return out;
      }
      return val;
    };

    for (let i = 0; i < arr.length; i++) {
      const v = arr[i];
      if (v && typeof v === 'object' && !Array.isArray(v) && 'operatingList' in v) {
        const resolved = resolve(i);
        if (Array.isArray(resolved?.operatingList) && resolved.operatingList.length > 0) {
          return resolved.operatingList;
        }
      }
    }
  } catch {
    // ignore Nuxt parse error
  }
  return [];
}

function mapMovieBoxShelfTitleToMeta(rawTitle: string): { bnTitle: string; categoryPath: string; badge?: string } {
  const t = rawTitle.toLowerCase();
  if (t.includes('trending drama')) {
    return { bnTitle: 'ট্রেন্ডিং ড্রামা সিরিজ', categoryPath: '/category/trending-drama', badge: 'HOT DRAMA' };
  }
  if (t.includes('trending movie')) {
    return { bnTitle: 'ট্রেন্ডিং মুভি (MovieBox Top)', categoryPath: '/type/movies', badge: 'TRENDING' };
  }
  if (t.includes('indian cinema')) {
    return { bnTitle: 'ইন্ডিয়ান সিনেমা ট্রেন্ডিং', categoryPath: '/category/indian-cinema', badge: 'INDIA TOP' };
  }
  if (t.includes('bengali')) {
    return { bnTitle: 'ট্রেন্ডিং বাংলা মুভি ও নাটক', categoryPath: '/language/bangla', badge: 'BANGLA HIT' };
  }
  if (t.includes('bollywood')) {
    return { bnTitle: 'বলিউড হিন্দি মুভি', categoryPath: '/bollywood', badge: 'BOLLYWOOD' };
  }
  if (t.includes('south indian')) {
    return { bnTitle: 'সাউথ ইন্ডিয়ান ব্লকবাস্টার', categoryPath: '/southIndian', badge: 'SOUTH DUB' };
  }
  if (t.includes('hollywood')) {
    return { bnTitle: 'হলিউড ব্লকবাস্টার মুভি', categoryPath: '/language/english', badge: 'HOLLYWOOD' };
  }
  if (t.includes('short tv')) {
    return { bnTitle: 'হট শর্ট টিভি ও মিনি ড্রামা', categoryPath: '/category/short-tv', badge: 'SHORT TV' };
  }
  if (t.includes('asian drama') || t.includes('k-drama')) {
    return { bnTitle: 'কোরিয়ান ও এশিয়ান ড্রামা', categoryPath: '/drama', badge: 'K-DRAMA' };
  }
  if (t.includes('western tv')) {
    return { bnTitle: 'ওয়েস্টার্ন ও হলিউড টিভি শো', categoryPath: '/category/western-tv', badge: 'WESTERN TV' };
  }
  if (t.includes('anime in hindi')) {
    return { bnTitle: 'হিন্দি ডাবিং অ্যানিমে', categoryPath: '/category/anime-hindi', badge: 'HINDI ANIME' };
  }
  if (t.includes('popular anime') || t.includes('anime')) {
    return { bnTitle: 'জনপ্রিয় অ্যানিমে সিরিজ', categoryPath: '/anime', badge: 'ANIME' };
  }
  if (t.includes('movie new release')) {
    return { bnTitle: 'সদ্য মুক্তিপ্রাপ্ত নতুন মুভি', categoryPath: '/type/movies', badge: 'NEW MOVIE' };
  }
  if (t.includes('tv series new release')) {
    return { bnTitle: 'নতুন টিভি ও ওয়েব সিরিজ', categoryPath: '/type/series', badge: 'NEW SERIES' };
  }
  if (t.includes('punjabi')) {
    return { bnTitle: 'সেরা পাঞ্জাবি মুভি', categoryPath: '/language/punjabi', badge: 'PUNJABI' };
  }
  if (t.includes('indian drama')) {
    return { bnTitle: 'ইন্ডিয়ান ড্রামা ও সিরিয়াল', categoryPath: '/category/indian-drama', badge: 'INDIAN DRAMA' };
  }
  if (t.includes('arabic')) {
    return { bnTitle: 'আরবি ড্রামা ও সিরিজ', categoryPath: '/category/arabic-drama', badge: 'ARABIC' };
  }
  if (t.includes('ramadan')) {
    return { bnTitle: 'রমজান স্পেশাল ড্রামা', categoryPath: '/category/arabic-drama', badge: 'SPECIAL' };
  }
  return { bnTitle: rawTitle, categoryPath: '/type/movies' };
}

async function getMovieBoxBearerToken(): Promise<string> {
  if (
    cachedMovieBoxToken &&
    cachedMovieBoxTokenExpiresAt > Date.now() &&
    cachedMovieBoxHomeSections.length > 0 &&
    cachedMovieBoxHomeExpiresAt > Date.now()
  ) {
    return cachedMovieBoxToken;
  }

  // 1. Fetch SSR operatingList from https://movie-box.co/ (contains the 23 South Asian / Bengali / Indian / Sports shelves)
  const ssrPromise = fetch(`${MOVIEBOX_ORIGIN}/`, {
    headers: {
      'User-Agent':
        'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
      Accept: 'text/html,application/xhtml+xml',
      'Accept-Language': 'en-US,en;q=0.9,bn;q=0.8,hi;q=0.7',
    },
    signal: AbortSignal.timeout(5000),
  })
    .then((r) => (r.ok ? r.text() : ''))
    .then((html) => (html ? extractMovieBoxNuxtOperatingList(html) : []))
    .catch(() => []);

  // 2. Fetch Bearer Token & fallback BFF home operatingList in parallel
  const homeEndpoints = [
    `${MOVIEBOX_ORIGIN}/wefeed-h5api-bff/home?host=movie-box.co`,
    `${MOVIEBOX_FALLBACK_API_ORIGIN}/wefeed-h5api-bff/home?host=movie-box.co`,
    `${MOVIEBOX_FALLBACK_API_ORIGIN}/wefeed-h5api-bff/home?host=movieboxhd.net`,
  ];

  let bffOps: any[] = [];
  for (const endpoint of homeEndpoints) {
    try {
      const res = await fetch(endpoint, {
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
          Accept: 'application/json',
          Referer: 'https://movie-box.co/?utm_source=mb_app_inner_btmtip',
          'X-Client-Info': JSON.stringify({ timezone: 'Asia/Dhaka' }),
          'X-Request-Lang': 'en',
        },
        signal: AbortSignal.timeout(4500),
      });
      const xUser = res.headers.get('x-user');
      if (xUser) {
        try {
          const parsed = JSON.parse(xUser);
          if (parsed?.token) {
            cachedMovieBoxToken = String(parsed.token);
            cachedMovieBoxTokenExpiresAt = Date.now() + 6 * 3600_000;
          }
        } catch {
          // ignore
        }
      }
      if (res.ok) {
        const json = (await res.json().catch(() => null)) as any;
        const ops = Array.isArray(json?.data?.operatingList) ? json.data.operatingList : [];
        if (ops.length > 0) {
          bffOps = ops;
        }
        if (cachedMovieBoxToken) break;
      }
    } catch {
      // try next MovieBox gateway
    }
  }

  const ssrOps = await ssrPromise;
  const combinedOps = [...ssrOps, ...bffOps];
  if (combinedOps.length > 0) {
    const seenTitles = new Set<string>();
    const sections: Array<{ title: string; type: string; subjects: any[] }> = [];
    for (const op of combinedOps) {
      const title = String(op?.title || '').trim();
      const type = String(op?.type || '').trim();
      const subjects = Array.isArray(op?.subjects)
        ? op.subjects
        : Array.isArray(op?.banner?.items)
          ? op.banner.items
          : [];
      if (!subjects.length) continue;
      const key = `${type}::${title.toLowerCase()}`;
      if (seenTitles.has(key)) continue;
      seenTitles.add(key);
      sections.push({ title, type, subjects });
    }
    if (sections.length > 0) {
      cachedMovieBoxHomeSections = sections;
      cachedMovieBoxHomeExpiresAt = Date.now() + 240_000;
    }
  }

  return cachedMovieBoxToken;
}

async function fetchMovieBoxHomePayload(): Promise<MovieBoxHomePayload> {
  if (cachedMovieBoxHomePayload && cachedMovieBoxHomePayloadExpiresAt > Date.now()) {
    return cachedMovieBoxHomePayload;
  }
  if (inFlightMovieBoxHomePromise) {
    return inFlightMovieBoxHomePromise;
  }

  const task = (async (): Promise<MovieBoxHomePayload> => {
    try {
      const [ssrHtml] = await Promise.all([
        fetch(`${MOVIEBOX_ORIGIN}/`, {
          headers: {
            'User-Agent':
              'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
            Accept: 'text/html,application/xhtml+xml',
            'Accept-Language': 'en-US,en;q=0.9,bn;q=0.8,hi;q=0.7',
          },
          signal: AbortSignal.timeout(5500),
        })
          .then((r) => (r.ok ? r.text() : ''))
          .catch(() => ''),
        getMovieBoxBearerToken().catch(() => ''),
      ]);

      const ssrOps = ssrHtml ? extractMovieBoxNuxtOperatingList(ssrHtml) : [];
      const banners: MovieCardItem[] = [];
      const seenBannerIds = new Set<string>();
      const comingSoon: MovieBoxComingSoonItem[] = [];
      const seenComingIds = new Set<string>();
      const shelves: MovieBoxHomeShelf[] = [];
      const seenShelfIds = new Set<string>();

      const defaultQuickCategories: MovieBoxQuickCategory[] = [
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
        {
          id: 'qc-kdrama',
          title: 'K-Drama',
          bnTitle: 'কোরিয়ান ড্রামা',
          image: 'https://pbcdnw.aoneroom.com/image/2025/01/13/1e5ef9bffd0b731d7eb4ef2c96ef7c77.png',
          path: '/drama',
        },
        {
          id: 'qc-western',
          title: 'Western TV',
          bnTitle: 'ওয়েস্টার্ন টিভি',
          image: 'https://pbcdnw.aoneroom.com/image/2025/01/13/3f4884c8e0f1fd7c92a4bf2c4a6b5e81.png',
          path: '/category/western-tv',
        },
        {
          id: 'qc-anime',
          title: 'Anime in Hindi',
          bnTitle: 'হিন্দি ও জাপানিজ অ্যানিমে',
          image: 'https://image.tmdb.org/t/p/original/n8rforZjHAB9uxqbwy7g6EdertA.jpg',
          path: '/category/anime-hindi',
        },
        {
          id: 'qc-sports',
          title: 'Sports Live',
          bnTitle: 'লাইভ স্পোর্টস ও WWE',
          image: 'https://image.tmdb.org/t/p/original/78lPtwv72eTNqFW9COBYI0dWDJa.jpg',
          path: '/category/sports',
        },
      ];

      const liveSports: MovieBoxLiveSportItem[] = [
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
      ];

      for (const op of ssrOps) {
        const opType = String(op?.type || '').trim();
        const opTitle = String(op?.title || '').trim();

        if (opType === 'BANNER' && Array.isArray(op?.banner?.items)) {
          for (let idx = 0; idx < op.banner.items.length; idx++) {
            const raw = op.banner.items[idx];
            const rawSubj = raw?.subject || raw;
            const sid = String(rawSubj?.subjectId || raw?.subjectId || '').trim();
            if (!sid || seenBannerIds.has(sid)) continue;
            seenBannerIds.add(sid);
            const card = mapMovieBoxItemToCard(
              {
                ...rawSubj,
                subjectId: sid,
                title: rawSubj?.title || raw?.title,
                detailPath: rawSubj?.detailPath || raw?.detailPath,
                cover: raw?.image || rawSubj?.cover,
              },
              idx
            );
            if (card) banners.push(card);
          }
        } else if (opType === 'APPOINTMENT_LIST' && Array.isArray(op?.subjects)) {
          for (const raw of op.subjects) {
            const sid = String(raw?.subjectId || '').trim();
            const title = String(raw?.title || '').trim();
            const poster = String(raw?.cover?.url || '').trim();
            if (!sid || !title || !poster || seenComingIds.has(sid)) continue;
            seenComingIds.add(sid);
            const detailSlug = String(raw?.detailPath || title)
              .toLowerCase()
              .replace(/[^a-z0-9-]+/g, '-')
              .replace(/^-+|-+$/g, '');
            const releaseDate = String(raw?.releaseDate || raw?.appointmentDate || '').trim();
            let releaseBadge = releaseDate;
            if (/^\d{4}-\d{2}-\d{2}$/.test(releaseDate)) {
              const dt = new Date(`${releaseDate}T00:00:00Z`);
              if (!isNaN(dt.getTime())) {
                releaseBadge = dt.toLocaleDateString('en-US', {
                  month: 'short',
                  day: 'numeric',
                  timeZone: 'UTC',
                });
              }
            }
            comingSoon.push({
              id: `mb_coming_${sid}`,
              title,
              releaseDate,
              releaseBadge: releaseBadge || 'Coming Soon',
              bookedCount: Number(raw?.appointmentCnt) || 120,
              poster,
              path: `/mb/${sid}/${detailSlug || 'movie'}`,
              genre: String(raw?.genre || 'Action, Drama'),
              country: String(raw?.countryName || ''),
            });
          }
        } else if (opType === 'SUBJECTS_MOVIE' && Array.isArray(op?.subjects) && opTitle) {
          const shelfKey = opTitle.toLowerCase();
          if (seenShelfIds.has(shelfKey)) continue;
          const cards: MovieCardItem[] = [];
          const seenCardIds = new Set<string>();
          for (let idx = 0; idx < op.subjects.length; idx++) {
            const raw = op.subjects[idx];
            const card = mapMovieBoxItemToCard(raw, idx);
            if (card && !seenCardIds.has(card.id)) {
              seenCardIds.add(card.id);
              cards.push(card);
            }
          }
          if (cards.length > 0) {
            seenShelfIds.add(shelfKey);
            const meta = mapMovieBoxShelfTitleToMeta(opTitle);
            shelves.push({
              id: `mb-shelf-${shelfKey.replace(/[^a-z0-9]+/g, '-')}`,
              title: opTitle,
              bnTitle: meta.bnTitle,
              categoryPath: meta.categoryPath,
              badge: meta.badge,
              items: cards.slice(0, 18),
            });
          }
        }
      }

      // If SSR shelves missed any sections, supplement from cachedMovieBoxHomeSections
      if (shelves.length === 0 && cachedMovieBoxHomeSections.length > 0) {
        for (const sec of cachedMovieBoxHomeSections) {
          if (sec.type !== 'SUBJECTS_MOVIE' || !sec.title) continue;
          const shelfKey = sec.title.toLowerCase();
          if (seenShelfIds.has(shelfKey)) continue;
          const cards: MovieCardItem[] = [];
          for (let idx = 0; idx < sec.subjects.length; idx++) {
            const card = mapMovieBoxItemToCard(sec.subjects[idx], idx);
            if (card) cards.push(card);
          }
          if (cards.length > 0) {
            seenShelfIds.add(shelfKey);
            const meta = mapMovieBoxShelfTitleToMeta(sec.title);
            shelves.push({
              id: `mb-shelf-${shelfKey.replace(/[^a-z0-9]+/g, '-')}`,
              title: sec.title,
              bnTitle: meta.bnTitle,
              categoryPath: meta.categoryPath,
              badge: meta.badge,
              items: cards.slice(0, 18),
            });
          }
        }
      }

      // Prioritize South Asian & Bengali shelves near the top for our users while keeping MovieBox's authentic order
      const priorityOrder = [
        'trending drama',
        'trending movie',
        'trending bengali movies',
        'trending in indian cinema',
        'bollywood movie',
        'south indian movie',
        'hollywood movie',
        '🔥hot short tv',
        'asian drama',
        'anime in hindi',
        'popular anime',
        'western tv',
        'movie new release',
        'tv series new release',
        'top punjabi movies',
        'indian drama',
        'arabic drama',
      ];
      shelves.sort((a, b) => {
        const ia = priorityOrder.findIndex((k) => a.title.toLowerCase().includes(k));
        const ib = priorityOrder.findIndex((k) => b.title.toLowerCase().includes(k));
        const sa = ia === -1 ? 999 : ia;
        const sb = ib === -1 ? 999 : ib;
        return sa - sb;
      });

      const payload: MovieBoxHomePayload = {
        ok: true,
        banners: banners.slice(0, 12),
        liveSports,
        quickCategories: defaultQuickCategories,
        comingSoon: comingSoon.slice(0, 18),
        sections: shelves,
      };
      if (shelves.length > 0) {
        cachedMovieBoxHomePayload = payload;
        cachedMovieBoxHomePayloadExpiresAt = Date.now() + 240_000;
      }
      return payload;
    } finally {
      inFlightMovieBoxHomePromise = null;
    }
  })();

  inFlightMovieBoxHomePromise = task;
  return task;
}

function getMovieBoxHomeOperatingSubjects(rawPath: string): any[] {
  if (!cachedMovieBoxHomeSections.length) return [];
  const p = (rawPath || '/').toLowerCase().replace(/\/page\/\d+\/?$/, '').replace(/\/+$/, '') || '/';
  const matched: any[] = [];

  for (const sec of cachedMovieBoxHomeSections) {
    const t = sec.title.toLowerCase();
    const isMatch =
      p === '/' ||
      p === '/hot-dhamaka' ||
      p === '/new-uploads' ||
      p === '/new-releases' ||
      p === '/mostwatch/7d' ||
      p === '/movies' ||
      (p === '/category/trending-drama' && t.includes('trending drama')) ||
      (p === '/category/indian-cinema' && (t.includes('indian cinema') || t.includes('bollywood') || t.includes('south indian'))) ||
      (p === '/category/short-tv' && t.includes('short tv')) ||
      (p === '/category/western-tv' && t.includes('western tv')) ||
      (p === '/category/anime-hindi' && t.includes('anime in hindi')) ||
      (p === '/category/indian-drama' && t.includes('indian drama')) ||
      (p === '/category/arabic-drama' && (t.includes('arabic') || t.includes('ramadan'))) ||
      ((p.includes('bangla') || p.includes('bengali')) && t.includes('bengali')) ||
      (p.includes('bollywood') && (t.includes('bollywood') || t.includes('indian cinema'))) ||
      (p.includes('south') && (t.includes('south indian') || t.includes('indian cinema'))) ||
      (p.includes('punjabi') && t.includes('punjabi')) ||
      ((p.includes('english') || p.includes('hollywood')) && (t.includes('hollywood') || t.includes('western'))) ||
      (p.includes('anime') && (t.includes('anime') || t.includes('animation'))) ||
      (p.includes('animation') && (t.includes('animation') || t.includes('anime'))) ||
      ((p.includes('drama') || p.includes('korean')) &&
        (t.includes('asian drama') || t.includes('k-drama') || t.includes('trending drama') || t.includes('drama'))) ||
      (p.includes('chinese') && (t.includes('asian drama') || t.includes('c-drama'))) ||
      ((p.includes('series') || p.includes('ongoing') || p.includes('tv')) &&
        (t.includes('series') || t.includes('shows') || t.includes('short tv') || t.includes('drama') || t.includes('western tv'))) ||
      ((p.includes('action') || p.includes('superhero')) &&
        (t.includes('action') || t.includes('superhero') || t.includes('gangster') || t.includes('hollywood'))) ||
      ((p.includes('thriller') || p.includes('crime')) &&
        (t.includes('thriller') || t.includes('gangster') || t.includes('action'))) ||
      (p.includes('horror') && t.includes('horror')) ||
      (p.includes('romance') && t.includes('romance')) ||
      (p.includes('comedy') && t.includes('comedy')) ||
      ((p.includes('fantasy') || p.includes('sci-fi') || p.includes('adventure')) &&
        (t.includes('fantasy') || t.includes('superhero'))) ||
      (p.includes('upcoming') && t.includes('coming soon'));

    if (isMatch) {
      matched.push(...sec.subjects);
    }
  }
  return matched;
}

function mapCategoryToMovieBoxFilter(rawPath: string, page = 1): Record<string, any> {
  const p = (rawPath || '/').toLowerCase().replace(/\/page\/\d+\/?$/, '').replace(/\/+$/, '') || '/';
  const payload: Record<string, any> = {
    page,
    perPage: 28,
    channelId: 1, // Default: Movies
    sort: 'Hottest',
  };

  if (p === '/' || p === '/hot-dhamaka' || p === '/mostwatch/7d') {
    payload.channelId = 1;
    payload.sort = 'Hottest';
  } else if (p === '/new-uploads' || p === '/new-releases' || p === '/upcoming') {
    payload.channelId = 1;
    payload.sort = 'Latest';
  } else if (p === '/category/trending-drama') {
    payload.channelId = 2;
    payload.sort = 'Hottest';
  } else if (p === '/category/indian-cinema') {
    payload.channelId = 1;
    payload.country = 'India';
    payload.sort = 'Hottest';
  } else if (p === '/category/short-tv') {
    payload.channelId = 2;
    payload.sort = 'Latest';
  } else if (p === '/category/western-tv') {
    payload.channelId = 2;
    payload.country = 'United States';
    payload.sort = 'Hottest';
  } else if (p === '/category/anime-hindi') {
    payload.channelId = 1006;
    payload.classify = 'Hindi dub';
    payload.sort = 'Hottest';
  } else if (p === '/category/indian-drama') {
    payload.channelId = 2;
    payload.country = 'India';
    payload.sort = 'Hottest';
  } else if (p === '/category/arabic-drama') {
    payload.channelId = 2;
    payload.country = 'Egypt';
    payload.sort = 'Hottest';
  } else if (p.includes('anime')) {
    payload.channelId = 1006;
    payload.sort = 'Hottest';
  } else if (p.includes('animation') || p.includes('family')) {
    payload.channelId = 1006;
    payload.sort = 'Hottest';
  } else if (p.includes('series') || p.includes('ongoing') || p.includes('tv')) {
    payload.channelId = 2;
    payload.sort = 'Hottest';
  } else if (p.includes('drama') || p.includes('korean')) {
    payload.channelId = 2;
    payload.country = 'Korea';
    payload.sort = 'Hottest';
  } else if (p.includes('chinese')) {
    payload.channelId = 2;
    payload.country = 'China';
  } else if (p.includes('japanese')) {
    payload.channelId = 1006;
    payload.country = 'Japan';
  } else if (p.includes('turkish')) {
    payload.channelId = 2;
    payload.country = 'Turkey';
  } else if (p.includes('bangla-dubbed')) {
    payload.channelId = 1;
    payload.classify = 'Bengali dub';
  } else if (p.includes('bangla')) {
    payload.channelId = 1;
    payload.country = 'Bangladesh';
  } else if (p.includes('hindi-dubbed') || p.includes('dual-audio')) {
    payload.channelId = 1;
    payload.classify = 'Hindi dub';
  } else if (p.includes('bollywood') || p.includes('hindi')) {
    payload.channelId = 1;
    payload.country = 'India';
  } else if (p.includes('tamil')) {
    payload.channelId = 1;
    payload.classify = 'Tamil dub';
  } else if (p.includes('telugu') || p.includes('south')) {
    payload.channelId = 1;
    payload.classify = 'Telugu dub';
  } else if (p.includes('malayalam')) {
    payload.channelId = 1;
    payload.classify = 'Malayalam dub';
  } else if (p.includes('kannada')) {
    payload.channelId = 1;
    payload.classify = 'Kannada dub';
  } else if (p.includes('punjabi')) {
    payload.channelId = 1;
    payload.classify = 'Punjabi dub';
  } else if (p.includes('english') || p.includes('hollywood') || p.includes('mcu') || p.includes('dc-universe')) {
    payload.channelId = 1;
    payload.country = 'United States';
  } else if (p.includes('indonesian')) {
    payload.channelId = 1;
    payload.country = 'Indonesia';
  } else if (p.includes('spanish')) {
    payload.channelId = 1;
    payload.country = 'Spain';
  } else if (p.includes('french')) {
    payload.channelId = 1;
    payload.country = 'France';
  } else if (p.includes('italian')) {
    payload.channelId = 1;
    payload.country = 'Italy';
  } else if (p.includes('malaysian')) {
    payload.channelId = 1;
    payload.country = 'Malaysia';
  } else if (p.includes('action') || p.includes('superhero')) {
    payload.channelId = 1;
    payload.genre = 'Action';
  } else if (p.includes('thriller') || p.includes('suspense') || p.includes('survival')) {
    payload.channelId = 1;
    payload.genre = 'Thriller';
  } else if (p.includes('horror')) {
    payload.channelId = 1;
    payload.genre = 'Horror';
  } else if (p.includes('romance')) {
    payload.channelId = 1;
    payload.genre = 'Romance';
  } else if (p.includes('comedy')) {
    payload.channelId = 1;
    payload.genre = 'Comedy';
  } else if (p.includes('crime')) {
    payload.channelId = 1;
    payload.genre = 'Crime';
  } else if (p.includes('sci-fi')) {
    payload.channelId = 1;
    payload.genre = 'Sci-Fi';
  } else if (p.includes('adventure')) {
    payload.channelId = 1;
    payload.genre = 'Adventure';
  } else if (p.includes('fantasy')) {
    payload.channelId = 1;
    payload.genre = 'Fantasy';
  } else if (p.includes('mystery')) {
    payload.channelId = 1;
    payload.genre = 'Mystery';
  } else if (p.includes('historical')) {
    payload.channelId = 1;
    payload.genre = 'History';
  } else if (p.includes('war')) {
    payload.channelId = 1;
    payload.genre = 'War';
  } else if (p.includes('documentary')) {
    payload.channelId = 1;
    payload.genre = 'Documentary';
  } else if (p.includes('biographical')) {
    payload.channelId = 1;
    payload.genre = 'Biography';
  } else if (p.includes('sport') || p.includes('fifa') || p.includes('wwe')) {
    payload.channelId = 1;
    payload.genre = 'Sport';
  } else if (p.includes('music')) {
    payload.channelId = 1;
    payload.genre = 'Music';
  }

  return payload;
}

function mapMovieBoxItemToCard(raw: any, index = 0): MovieCardItem | null {
  if (!raw || !raw.subjectId || !raw.title || raw.hasResource === false) return null;
  const subjectId = String(raw.subjectId).trim();
  const detailSlug = String(raw.detailPath || raw.title)
    .toLowerCase()
    .replace(/[^a-z0-9-]+/g, '-')
    .replace(/^-+|-+$/g, '');
  const itemPath = `/mb/${subjectId}/${detailSlug || 'movie'}`;
  const rawTitle = String(raw.title).trim();
  const year = raw.releaseDate ? String(raw.releaseDate).split('-')[0] : '';
  const hasYearInTitle = /\b(19|20)\d{2}\b/.test(rawTitle);
  const displayTitle = year && !hasYearInTitle ? `${rawTitle} (${year})` : rawTitle;

  const poster = String(raw.cover?.url || raw.stills?.url || '').trim();
  if (!poster) return null;

  const ratingVal = parseFloat(String(raw.imdbRatingValue || raw.imdbRate || '8.2')) || 8.2;
  const subjectType = Number(raw.subjectType) || 1;
  const genreStr = String(raw.genre || '').toUpperCase();
  const countryStr = String(raw.countryName || '').toUpperCase();
  const cornerStr = String(raw.corner || '').trim().toUpperCase();

  let typeBadge: 'MOVIE' | 'SERIES' | 'ANIME' | 'DRAMA' = 'MOVIE';
  if (subjectType === 1006 || genreStr.includes('ANIMATION') || countryStr === 'JAPAN') {
    typeBadge = subjectType === 2 ? 'ANIME' : 'MOVIE';
  } else if (subjectType === 2) {
    if (countryStr.includes('KOREA') || countryStr.includes('CHINA') || countryStr.includes('TURKEY')) {
      typeBadge = 'DRAMA';
    } else {
      typeBadge = 'SERIES';
    }
  }

  const dubsList = Array.isArray(raw.dubs)
    ? raw.dubs.map((d: any) => String(d?.lanName || d || '')).filter(Boolean)
    : [];
  const subsStr = String(raw.subtitles || '');
  let language = 'ENGLISH';
  if (cornerStr.includes('BENGALI') || cornerStr.includes('BANGLA') || /\[(bengali|bangla)\]/i.test(rawTitle)) {
    language = /dub/i.test(rawTitle) || (!countryStr.includes('BANGLADESH') && !countryStr.includes('INDIA'))
      ? 'BANGLA DUBBED'
      : 'BANGLA';
  } else if (cornerStr.includes('HINDI') || /\[hindi\]/i.test(rawTitle)) {
    language = !countryStr.includes('INDIA') ? 'HINDI DUBBED' : 'HINDI';
  } else if (cornerStr) {
    language = cornerStr;
  } else if (dubsList.length > 0) {
    language = dubsList[0].toUpperCase();
  } else if (subsStr.includes('বাংলা') || countryStr.includes('BANGLADESH')) {
    language = countryStr.includes('BANGLADESH') ? 'BANGLA' : 'BANGLA SUB';
  } else if (countryStr.includes('INDIA')) {
    language = 'HINDI';
  } else if (countryStr.includes('KOREA')) {
    language = 'KOREAN';
  } else if (countryStr.includes('CHINA')) {
    language = 'CHINESE';
  } else if (countryStr.includes('JAPAN')) {
    language = 'JAPANESE';
  }

  const episodePill =
    subjectType === 2
      ? /\bS\d+/i.test(rawTitle)
        ? rawTitle.match(/\bS\d+(?:-S?\d+)?/i)?.[0]?.toUpperCase() || 'SERIES'
        : 'FULL SERIES'
      : '';

  const releaseYearNum = parseInt(year, 10) || 0;
  const releaseEpochMs = raw.releaseDate ? Date.parse(String(raw.releaseDate)) : NaN;
  const nowMs = Date.now();

  let hash = 2166136261 >>> 0;
  for (let i = 0; i < subjectId.length; i++) {
    hash ^= subjectId.charCodeAt(i);
    hash = Math.imul(hash, 16777619) >>> 0;
  }

  // Extract real CDN upload date from MovieBox poster URL: e.g. /image/2026/11/01/...
  const cdnDateMatch = poster.match(/\/image\/(\d{4})\/(\d{2})\/(\d{2})\//);
  const cdnDateStr = cdnDateMatch ? `${cdnDateMatch[1]}-${cdnDateMatch[2]}-${cdnDateMatch[3]}` : '';
  const cdnEpochMs = cdnDateStr ? Date.parse(`${cdnDateStr}T12:00:00Z`) : NaN;
  const isTodayOrYesterdayCdn =
    !isNaN(cdnEpochMs) && nowMs - cdnEpochMs <= 48 * 3600_000 && cdnEpochMs <= nowMs + 24 * 3600_000;

  let timeAgoLabel = year || 'HD Release';
  let uploadedAtMs = !isNaN(releaseEpochMs) && releaseEpochMs <= nowMs ? releaseEpochMs : 0;

  if (isTodayOrYesterdayCdn && releaseYearNum >= 2025) {
    // Uploaded to MovieBox CDN today or yesterday!
    const minsAgo = 12 + (hash % 380); // 12 mins to 6.5 hours ago
    timeAgoLabel =
      minsAgo < 60 ? `${minsAgo} mins ago` : `${Math.floor(minsAgo / 60)} hours ago`;
    uploadedAtMs = nowMs - minsAgo * 60_000;
  } else if (releaseYearNum >= 2025) {
    const spreadHours = 2 + (hash % 21);
    const spreadMins = spreadHours * 60 + ((hash >>> 8) % 53);
    timeAgoLabel = `${spreadHours} hours ago`;
    uploadedAtMs = nowMs - spreadMins * 60_000;
  } else if (!uploadedAtMs && releaseYearNum > 1900) {
    uploadedAtMs = new Date(`${releaseYearNum}-06-15T00:00:00Z`).getTime();
  }

  return {
    id: `mb_${subjectId}`,
    title: displayTitle,
    url: itemPath,
    path: itemPath,
    poster,
    quality: '1080p FHD',
    views: `★ ${ratingVal.toFixed(1)}`,
    rating: ratingVal.toFixed(1),
    language,
    typeBadge,
    timeAgo: timeAgoLabel,
    episodePill,
    isPinned: releaseYearNum >= 2025 && (isTodayOrYesterdayCdn || ratingVal >= 8.0),
    isAdult: Boolean(raw.isPornographic),
    uploadedAtMs,
  };
}

async function fetchMovieBoxCatalog(
  rawPath: string,
  page = 1,
  search = ''
): Promise<{ items: MovieCardItem[]; maxPage: number }> {
  const token = await getMovieBoxBearerToken();
  const headers: Record<string, string> = {
    'Content-Type': 'application/json',
    Accept: 'application/json',
    'User-Agent':
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
    'X-Client-Info': JSON.stringify({ timezone: 'Asia/Dhaka' }),
    'X-Request-Lang': 'en',
    Referer: 'https://movie-box.co/?utm_source=mb_app_inner_btmtip',
  };
  if (token) {
    headers.Authorization = `Bearer ${token}`;
  }

  if (search) {
    const searchEndpoints = [
      `${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/search`,
      `${MOVIEBOX_FALLBACK_API_ORIGIN}/wefeed-h5api-bff/subject/search`,
    ];
    let rawItems: any[] = [];
    for (const ep of searchEndpoints) {
      try {
        const res = await fetch(ep, {
          method: 'POST',
          headers,
          body: JSON.stringify({
            keyword: search,
            page,
            perPage: 28,
            subjectType: 0,
          }),
          signal: AbortSignal.timeout(4800),
        });
        if (res.ok) {
          const json = (await res.json()) as any;
          if (Array.isArray(json?.data?.items) && json.data.items.length > 0) {
            rawItems = json.data.items;
            break;
          }
        }
      } catch {
        // try fallback gateway
      }
    }
    const lowerQ = search.toLowerCase();
    for (const sec of cachedMovieBoxHomeSections) {
      for (const s of sec.subjects) {
        if (String(s?.title || '').toLowerCase().includes(lowerQ)) {
          rawItems.push(s);
        }
      }
    }
    const seenSearchIds = new Set<string>();
    const cards: MovieCardItem[] = [];
    for (let idx = 0; idx < rawItems.length; idx++) {
      const it = rawItems[idx];
      const sid = String(it?.subjectId || '');
      if (!sid || seenSearchIds.has(sid)) continue;
      seenSearchIds.add(sid);
      const card = mapMovieBoxItemToCard(it, idx);
      if (card) cards.push(card);
    }
    return { items: cards, maxPage: 50 };
  }

  // Fetch BOTH Latest Uploads AND Hottest/All-Time across Movies (channelId 1), Series (channelId 2), and Anime (channelId 1006)
  // plus curated operatingList sections directly from https://movie-box.co!
  const filterPayload: Record<string, any> = { ...mapCategoryToMovieBoxFilter(rawPath, page), perPage: 36 };
  const oppositeSort = filterPayload.sort === 'Latest' ? 'Hottest' : 'Latest';
  const requests: Promise<Response>[] = [
    fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
      method: 'POST',
      headers,
      body: JSON.stringify(filterPayload),
      signal: AbortSignal.timeout(4800),
    }),
    fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
      method: 'POST',
      headers,
      body: JSON.stringify({ ...filterPayload, sort: oppositeSort }),
      signal: AbortSignal.timeout(4800),
    }),
  ];

  // If the filter is on channelId 1 (Movies), also fetch matching TV Series (channelId 2, both Latest & Hottest) in parallel!
  if (filterPayload.channelId === 1) {
    requests.push(
      fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
        method: 'POST',
        headers,
        body: JSON.stringify({ ...filterPayload, channelId: 2, sort: 'Latest' }),
        signal: AbortSignal.timeout(4800),
      }),
      fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/filter`, {
        method: 'POST',
        headers,
        body: JSON.stringify({ ...filterPayload, channelId: 2, sort: 'Hottest' }),
        signal: AbortSignal.timeout(4800),
      })
    );
  }

  if ((rawPath === '/' || rawPath === '/hot-dhamaka' || rawPath === '/new-uploads') && page === 1) {
    requests.unshift(
      fetch(`${MOVIEBOX_API_ORIGIN}/wefeed-h5api-bff/subject/trending?page=1&perPage=28`, {
        headers,
        signal: AbortSignal.timeout(4500),
      })
    );
  }

  const settled = await Promise.allSettled(requests);
  const combinedRaw: any[] = [];
  if (page === 1) {
    combinedRaw.push(...getMovieBoxHomeOperatingSubjects(rawPath));
  }
  let maxPage = 2500;
  for (const r of settled) {
    if (r.status === 'fulfilled' && r.value.ok) {
      const j = (await r.value.json().catch(() => null)) as any;
      const list = j?.data?.subjectList || j?.data?.items || [];
      if (Array.isArray(list)) combinedRaw.push(...list);
      const totalCount = Number(j?.data?.pager?.totalCount || 0);
      if (totalCount > 0) {
        maxPage = Math.max(maxPage, Math.min(3500, Math.ceil(totalCount / 28)));
      }
    }
  }

  const seenIds = new Set<string>();
  const cards: MovieCardItem[] = [];
  for (let i = 0; i < combinedRaw.length; i++) {
    const raw = combinedRaw[i];
    const sid = String(raw?.subjectId || '');
    if (!sid || seenIds.has(sid)) continue;
    seenIds.add(sid);
    const card = mapMovieBoxItemToCard(raw, i);
    if (card) cards.push(card);
  }

  return { items: cards, maxPage };
}

async function resolveImdbIdForTitle(
  rawTitle: string,
  releaseDateStr = '',
  isSeries = false
): Promise<string> {
  const cleanTitle = extractBaseSeriesTitle(rawTitle)
    .replace(/\b(19|20)\d{2}\b/g, '')
    .replace(/\s{2,}/g, ' ')
    .trim();
  if (!cleanTitle || cleanTitle.length < 2) return '';
  const cacheKey = `${cleanTitle.toLowerCase()}::${isSeries ? 'tv' : 'movie'}`;
  const cached = imdbIdCache.get(cacheKey);
  if (cached !== undefined) return cached;

  try {
    const res = await fetch(
      `https://v3.sg.media-imdb.com/suggestion/x/${encodeURIComponent(cleanTitle)}.json`,
      {
        headers: { Accept: 'application/json', 'User-Agent': 'Mozilla/5.0' },
        signal: AbortSignal.timeout(2200),
      }
    );
    if (!res.ok) return '';
    const json = (await res.json()) as any;
    const list: any[] = Array.isArray(json?.d) ? json.d.filter((x: any) => String(x?.id || '').startsWith('tt')) : [];
    if (!list.length) {
      imdbIdCache.set(cacheKey, '');
      return '';
    }
    const wantYear = parseInt(String(releaseDateStr || '').slice(0, 4), 10) || 0;
    const norm = (s: string) => String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '');
    const wantNorm = norm(cleanTitle);

    const scored = list.map((item) => {
      let sc = 0;
      const itemNorm = norm(item.l || '');
      if (itemNorm === wantNorm) sc += 50;
      else if (itemNorm.includes(wantNorm) || wantNorm.includes(itemNorm)) sc += 25;
      const qStr = String(item.q || item.qid || '').toLowerCase();
      const itemIsTv = qStr.includes('tv') || qStr.includes('series') || qStr.includes('mini');
      if (isSeries === itemIsTv) sc += 30;
      if (wantYear > 1900 && item.y && Math.abs(Number(item.y) - wantYear) <= 1) sc += 25;
      return { id: String(item.id), sc };
    });
    scored.sort((a, b) => b.sc - a.sc);
    const bestId = scored[0]?.id || '';
    if (bestId) {
      pruneCacheMap(imdbIdCache, 300);
      imdbIdCache.set(cacheKey, bestId);
    }
    return bestId;
  } catch {
    return '';
  }
}

function buildEmbedBackupSources(
  imdbId: string,
  seasonNum: number,
  epNum: number,
  title: string,
  language: string
): StreamSource[] {
  if (!imdbId || !imdbId.startsWith('tt')) return [];
  if (seasonNum > 0 && epNum > 0) {
    return [
      {
        id: `vidsrc-pro-${imdbId}-s${seasonNum}-e${epNum}`,
        quality: 1080,
        qualityLabel: '1080p Cloud HLS (VidSrc Pro)',
        audio: language,
        audioLanguages: [language],
        provider: 'VidSrc Pro HD',
        url: `https://vidsrc.cc/v2/embed/tv/${imdbId}/${seasonNum}/${epNum}`,
        downloadUrl: `https://vidsrc.cc/v2/embed/tv/${imdbId}/${seasonNum}/${epNum}`,
        type: 'embed',
        name: `${title} - S${seasonNum}E${epNum} (VidSrc Pro 1080p)`,
      },
      {
        id: `multiembed-${imdbId}-s${seasonNum}-e${epNum}`,
        quality: 1080,
        qualityLabel: '1080p Multi-Audio (SuperEmbed)',
        audio: language,
        audioLanguages: [language],
        provider: 'SuperEmbed HD',
        url: `https://multiembed.mov/?video_id=${imdbId}&s=${seasonNum}&e=${epNum}`,
        downloadUrl: `https://multiembed.mov/?video_id=${imdbId}&s=${seasonNum}&e=${epNum}`,
        type: 'embed',
        name: `${title} - S${seasonNum}E${epNum} (SuperEmbed HD)`,
      },
      {
        id: `vidsrc-xyz-${imdbId}-s${seasonNum}-e${epNum}`,
        quality: 720,
        qualityLabel: '720p Fast HLS (VidSrc Global)',
        audio: language,
        audioLanguages: [language],
        provider: 'VidSrc Global',
        url: `https://vidsrc.xyz/embed/tv?imdb=${imdbId}&season=${seasonNum}&episode=${epNum}`,
        downloadUrl: `https://vidsrc.xyz/embed/tv?imdb=${imdbId}&season=${seasonNum}&episode=${epNum}`,
        type: 'embed',
        name: `${title} - S${seasonNum}E${epNum} (VidSrc Global)`,
      },
    ];
  }
  return [
    {
      id: `vidsrc-pro-${imdbId}-movie`,
      quality: 1080,
      qualityLabel: '1080p Cloud HLS (VidSrc Pro)',
      audio: language,
      audioLanguages: [language],
      provider: 'VidSrc Pro HD',
      url: `https://vidsrc.cc/v2/embed/movie/${imdbId}`,
      downloadUrl: `https://vidsrc.cc/v2/embed/movie/${imdbId}`,
      type: 'embed',
      name: `${title} (VidSrc Pro 1080p)`,
    },
    {
      id: `multiembed-${imdbId}-movie`,
      quality: 1080,
      qualityLabel: '1080p Multi-Audio (SuperEmbed)',
      audio: language,
      audioLanguages: [language],
      provider: 'SuperEmbed HD',
      url: `https://multiembed.mov/?video_id=${imdbId}`,
      downloadUrl: `https://multiembed.mov/?video_id=${imdbId}`,
      type: 'embed',
      name: `${title} (SuperEmbed HD)`,
    },
    {
      id: `vidsrc-xyz-${imdbId}-movie`,
      quality: 720,
      qualityLabel: '720p Fast HLS (VidSrc Global)',
      audio: language,
      audioLanguages: [language],
      provider: 'VidSrc Global',
      url: `https://vidsrc.xyz/embed/movie?imdb=${imdbId}`,
      downloadUrl: `https://vidsrc.xyz/embed/movie?imdb=${imdbId}`,
      type: 'embed',
      name: `${title} (VidSrc Global)`,
    },
  ];
}

const mbPlayStreamCache = new Map<
  string,
  { sources: StreamSource[]; buttons: DirectDownloadButton[]; expiresAt: number }
>();

async function fetchMovieBoxPlayStreams(
  subjectId: string,
  detailPath: string,
  seasonNum: number,
  epNum: number,
  title: string,
  language: string,
  fallbackVideoUrl = ''
): Promise<{ sources: StreamSource[]; buttons: DirectDownloadButton[] }> {
  const playCacheKey = `${subjectId}::s${seasonNum}::e${epNum}`;
  const cachedPlay = mbPlayStreamCache.get(playCacheKey);
  if (cachedPlay && cachedPlay.expiresAt > Date.now() && cachedPlay.sources.length > 0) {
    return { sources: cachedPlay.sources, buttons: cachedPlay.buttons };
  }

  const token = await getMovieBoxBearerToken();
  const playOrigins = [MOVIEBOX_ORIGIN, MOVIEBOX_BACKUP_ORIGIN];
  let streams: any[] = [];

  for (const origin of playOrigins) {
    try {
      const playUrl = `${origin}/wefeed-h5api-bff/subject/play?subjectId=${encodeURIComponent(
        subjectId
      )}&se=${seasonNum}&ep=${epNum}&detailPath=${encodeURIComponent(detailPath)}&streamSignType=1`;

      const headers: Record<string, string> = {
        Accept: 'application/json',
        'User-Agent':
          'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
        Referer: `${origin}/movies/${detailPath}?id=${subjectId}`,
        'X-Client-Info': JSON.stringify({ timezone: 'Asia/Dhaka' }),
        'X-Request-Lang': 'en',
      };
      if (token) headers.Authorization = `Bearer ${token}`;

      const res = await fetch(playUrl, { headers, signal: AbortSignal.timeout(4200) });
      if (res.ok) {
        const json = (await res.json()) as any;
        if (Array.isArray(json?.data?.streams) && json.data.streams.length > 0) {
          streams = json.data.streams;
          break;
        }
      }
    } catch {
      // try backup origin
    }
  }

  const sources: StreamSource[] = [];
  const buttons: DirectDownloadButton[] = [];
  const fbParam = fallbackVideoUrl
    ? `&fb=${Buffer.from(String(fallbackVideoUrl), 'utf8').toString('base64url')}`
    : '';

  for (let i = 0; i < streams.length; i++) {
    const st = streams[i];
    if (!st?.url) continue;
    const resNum = parseInt(String(st.resolutions || '720'), 10) || 720;
    const sizeBytes = Number(st.size) || 0;
    const sizeMb = sizeBytes > 0 ? `${(sizeBytes / (1024 * 1024)).toFixed(0)} MB` : 'Full HD';
    const proxiedStreamUrl = `/api/mb-stream.mp4?t=${Buffer.from(String(st.url), 'utf8').toString('base64url')}${fbParam}`;
    const proxiedDlUrl = `/api/mb-stream.mp4?t=${Buffer.from(String(st.url), 'utf8').toString('base64url')}&dl=1&name=${encodeURIComponent(
      `${title.replace(/[^a-zA-Z0-9_-]+/g, '_')}_${resNum}p.mp4`
    )}`;

    sources.push({
      id: `mb-stream-${subjectId}-s${seasonNum}-e${epNum}-${resNum}p-${i}`,
      quality: resNum,
      qualityLabel: `${resNum}p Full HD (MovieBox Direct)`,
      audio: language,
      audioLanguages: [language],
      provider: `MovieBox HD ${resNum}p`,
      url: proxiedStreamUrl,
      downloadUrl: proxiedDlUrl,
      type: 'mp4',
      name: `${title} (${resNum}p MP4 • ${sizeMb})`,
    });

    buttons.push({
      label: `MovieBox Direct Download ${resNum}p MP4 (${sizeMb})`,
      url: proxiedDlUrl,
      quality: `${resNum}p`,
      size: sizeMb,
    });
  }

  sources.sort((a, b) => {
    const rank = (s: StreamSource) => {
      const szMatch = (s.name || '').match(/(\d+)\s*MB/i);
      const szMb = szMatch ? parseInt(szMatch[1], 10) : 0;
      if (s.quality === 720) return 100;
      if (s.quality === 480) return 95;
      if (s.quality === 360) return 90;
      if (s.quality === 1080) return szMb > 350 ? 80 : 98;
      return s.quality;
    };
    return rank(b) - rank(a);
  });
  buttons.sort((a, b) => parseInt(b.quality, 10) - parseInt(a.quality, 10));
  if (sources.length > 0) {
    pruneCacheMap(mbPlayStreamCache, 150);
    mbPlayStreamCache.set(playCacheKey, {
      sources,
      buttons,
      expiresAt: Date.now() + 15 * 60_000,
    });
  }
  return { sources, buttons };
}

async function fetchMovieBoxDetail(rawPath: string): Promise<MovieDetailData> {
  // rawPath format: /mb/<subjectId>/<detailSlug>
  const parts = rawPath.replace(/^\/mb\//, '').split('/').filter(Boolean);
  const subjectId = parts[0] || '';
  const fallbackSlug = parts[1] || 'movie';

  const token = await getMovieBoxBearerToken();
  const headers: Record<string, string> = {
    Accept: 'application/json',
    'User-Agent':
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
    Referer: 'https://movie-box.co/?utm_source=mb_app_inner_btmtip',
    'X-Client-Info': JSON.stringify({ timezone: 'Asia/Dhaka' }),
    'X-Request-Lang': 'en',
  };
  if (token) headers.Authorization = `Bearer ${token}`;

  let detJson: any = null;
  for (const apiBase of [MOVIEBOX_API_ORIGIN, MOVIEBOX_FALLBACK_API_ORIGIN]) {
    try {
      const detRes = await fetch(
        `${apiBase}/wefeed-h5api-bff/detail?subjectId=${encodeURIComponent(subjectId)}`,
        { headers, signal: AbortSignal.timeout(4500) }
      );
      if (detRes.ok) {
        detJson = await detRes.json();
        if (detJson?.data?.subject) break;
      }
    } catch {
      // try fallback gateway
    }
  }
  if (!detJson?.data?.subject) throw new Error('MovieBox detail unavailable');
  const subject = detJson?.data?.subject || {};
  const resource = detJson?.data?.resource || {};
  const stars = Array.isArray(detJson?.data?.stars) ? detJson.data.stars : [];

  const title = String(subject.title || 'MovieBox Title').trim();
  const detailPath = String(subject.detailPath || fallbackSlug).trim();
  const poster = String(subject.cover?.url || '').trim();
  const releaseDate = String(subject.releaseDate || '2026').trim();
  const genre = String(subject.genre || 'Action, Drama').replace(/,/g, ', ');
  const storyline = String(subject.description || '').trim();
  const ratingVal = parseFloat(String(subject.imdbRatingValue || '8.4')) || 8.4;
  const subjectType = Number(subject.subjectType) || 1;
  const trailerMp4Url = String(subject.trailer?.videoAddress?.url || '').trim();
  const uploadedBy = String(resource?.uploadBy || 'MarieNo Ess').trim();

  // Extract all available audio dubs / language versions from subject.dubs (e.g., Hindi dub, Bengali dub, Original Audio, etc.)
  const rawDubs = Array.isArray(subject.dubs) ? subject.dubs : [];
  const dubs: MovieDubOption[] = [];
  const seenDubIds = new Set<string>();
  for (const d of rawDubs) {
    const dId = String(d?.subjectId || '').trim();
    const dLabel = String(d?.lanName || '').trim();
    if (!dId || !dLabel || seenDubIds.has(dId)) continue;
    seenDubIds.add(dId);
    const dSlug = String(d?.detailPath || detailPath).trim();
    dubs.push({
      id: dId,
      label: dLabel,
      lanCode: String(d?.lanCode || '').trim(),
      path: `/mb/${dId}/${dSlug}`,
      active: dId === subjectId,
    });
  }

  // Sort dubs so active dub, Hindi dub, Bangla/Bengali dub, and Original Audio appear at the top
  dubs.sort((a, b) => {
    const rank = (opt: MovieDubOption) => {
      if (opt.active) return 100;
      const l = opt.label.toLowerCase();
      if (l.includes('hindi')) return 90;
      if (l.includes('bengali') || l.includes('bangla')) return 85;
      if (l.includes('original') || l.includes('english')) return 80;
      if (l.includes('dub')) return 70;
      return 40;
    };
    return rank(b) - rank(a);
  });

  // Determine the exact audio/dub label for this subjectId
  const activeDubObj = dubs.find((d) => d.id === subjectId);
  let language = activeDubObj?.label || '';
  if (!language) {
    if (/\[hindi\]|\bhindi\s*dub/i.test(title)) language = 'Hindi dub';
    else if (/\[bengali\]|\[bangla\]|\bbangla\s*dub/i.test(title)) language = 'Bangla dub';
    else if (/\[tamil\]/i.test(title)) language = 'Tamil dub';
    else if (/\[telugu\]/i.test(title)) language = 'Telugu dub';
    else if (/\[arabic\]/i.test(title)) language = 'Arabic dub';
    else if (String(subject.countryName || '').toLowerCase().includes('india')) language = 'Hindi';
    else if (String(subject.countryName || '').toLowerCase().includes('bangladesh')) language = 'Bangla';
    else if (String(subject.countryName || '').toLowerCase().includes('korea')) language = 'Korean';
    else if (dubs.length > 0) language = dubs[0].label;
    else language = 'Original Audio';
  }

  if (dubs.length === 0) {
    dubs.push({
      id: subjectId,
      label: language,
      path: rawPath,
      active: true,
    });
  } else if (!dubs.some((d) => d.active)) {
    dubs.unshift({
      id: subjectId,
      label: language,
      path: rawPath,
      active: true,
    });
  }

  const cast: CastMember[] = (Array.isArray(subject.staffList) ? subject.staffList : stars)
    .slice(0, 12)
    .map((s: any) => ({
      url: `/search?q=${encodeURIComponent(String(s?.name || ''))}`,
      photo: String(s?.avatarUrl || s?.avatar || ''),
      name: String(s?.name || 'Actor'),
      role: String(s?.character || s?.role || 'Cast'),
    }));

  const screenshots: string[] = [];
  if (subject.stills?.url) screenshots.push(String(subject.stills.url));
  if (subject.trailer?.cover?.url) screenshots.push(String(subject.trailer.cover.url));

  const seasonsList = Array.isArray(resource.seasons) ? resource.seasons : [];
  const isMovieType =
    subjectType === 1 ||
    seasonsList.length === 0 ||
    (seasonsList.length === 1 && Number(seasonsList[0]?.se) === 0);

  const episodes: EpisodeItem[] = [];
  let downloadButtons: DirectDownloadButton[] = [];

  if (isMovieType) {
    // Movie (se=0, ep=0, with fallback to se=1, ep=1 if stored as single episode)
    let { sources, buttons } = await fetchMovieBoxPlayStreams(
      subjectId,
      detailPath,
      0,
      0,
      title,
      language,
      trailerMp4Url
    );
    if (sources.length === 0) {
      const fb = await fetchMovieBoxPlayStreams(
        subjectId,
        detailPath,
        1,
        1,
        title,
        language,
        trailerMp4Url
      );
      sources = fb.sources;
      buttons = fb.buttons;
    }
    const imdbId =
      sources.length === 0
        ? await Promise.race([
            resolveImdbIdForTitle(title, releaseDate, false),
            new Promise<string>((r) => setTimeout(() => r(''), 300)),
          ])
        : '';
    const embedBackups = buildEmbedBackupSources(imdbId, 0, 0, title, language);
    const allMovieSources = [...sources, ...embedBackups];
    downloadButtons = buttons;
    if (allMovieSources.length > 0) {
      episodes.push({
        id: `mb-movie-${subjectId}`,
        label: 'Full Movie (MovieBox HD)',
        number: 1,
        rangeStart: 1,
        rangeEnd: 1,
        season: null,
        kind: 'movie',
        sources: allMovieSources,
      });
    }
  } else {
    // Series / Drama / Anime: Preload Episode 1 immediately for <150ms startup!
    const parseSeasonEpNums = (sObj: any): number[] => {
      const maxEp = Math.max(1, Number(sObj?.maxEp) || 1);
      const fromAllEp = String(sObj?.allEp || '')
        .split(',')
        .map((x) => parseInt(x.trim(), 10))
        .filter((n) => !Number.isNaN(n) && n > 0);
      return fromAllEp.length > 0
        ? fromAllEp
        : Array.from({ length: maxEp }, (_, idx) => idx + 1);
    };

    const firstSeason = seasonsList[0] || { se: 1, maxEp: 8 };
    const firstSeNum = Number(firstSeason.se) || 1;
    const firstSeasonEpNums = parseSeasonEpNums(firstSeason);
    const firstEpNum = firstSeasonEpNums[0] || 1;

    const preloadedMap = new Map<number, { sources: StreamSource[]; buttons: DirectDownloadButton[] }>();
    const firstEpRes = await fetchMovieBoxPlayStreams(
      subjectId,
      detailPath,
      firstSeNum,
      firstEpNum,
      `${title} S${firstSeNum}E${firstEpNum}`,
      language,
      trailerMp4Url
    );
    preloadedMap.set(firstEpNum, firstEpRes);
    const imdbId =
      firstEpRes.sources.length === 0
        ? await Promise.race([
            resolveImdbIdForTitle(title, releaseDate, true),
            new Promise<string>((r) => setTimeout(() => r(''), 300)),
          ])
        : '';

    const fbParam = trailerMp4Url
      ? `&fb=${Buffer.from(trailerMp4Url, 'utf8').toString('base64url')}`
      : '';

    for (let sIdx = 0; sIdx < seasonsList.length; sIdx++) {
      const sObj = seasonsList[sIdx];
      const seNum = Number(sObj?.se) || sIdx + 1;
      const epNums = sIdx === 0 ? firstSeasonEpNums : parseSeasonEpNums(sObj);

      for (const epNum of epNums) {
        const pre = sIdx === 0 ? preloadedMap.get(epNum) : undefined;
        const embedBackups = buildEmbedBackupSources(imdbId, seNum, epNum, title, language);
        if (pre && pre.sources.length > 0) {
          if (downloadButtons.length === 0) downloadButtons = pre.buttons;
          episodes.push({
            id: `mb-ep-${subjectId}-s${seNum}-e${epNum}`,
            label: `S${String(seNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • Episode ${epNum}`,
            number: epNum,
            rangeStart: epNum,
            rangeEnd: epNum,
            season: seNum,
            kind: 'episode',
            sources: [...pre.sources, ...embedBackups],
          });
        } else {
          // Dynamic lazy-resolved stream URL via /api/mb-ep-stream.mp4 so ALL seasons and ALL episodes work on click!
          const dynamicStreamUrl = `/api/mb-ep-stream.mp4?subjectId=${encodeURIComponent(
            subjectId
          )}&detailPath=${encodeURIComponent(detailPath)}&se=${seNum}&ep=${epNum}${fbParam}`;
          episodes.push({
            id: `mb-ep-${subjectId}-s${seNum}-e${epNum}`,
            label: `S${String(seNum).padStart(2, '0')}E${String(epNum).padStart(2, '0')} • Episode ${epNum}`,
            number: epNum,
            rangeStart: epNum,
            rangeEnd: epNum,
            season: seNum,
            kind: 'episode',
            sources: [
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-1080`,
                quality: 1080,
                qualityLabel: '1080p Full HD (MovieBox Direct)',
                audio: language,
                audioLanguages: [language],
                provider: 'MovieBox HD 1080p',
                url: `${dynamicStreamUrl}&q=1080`,
                downloadUrl: `${dynamicStreamUrl}&q=1080&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (1080p)`,
              },
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-720`,
                quality: 720,
                qualityLabel: '720p HD (MovieBox Direct)',
                audio: language,
                audioLanguages: [language],
                provider: 'MovieBox HD 720p',
                url: `${dynamicStreamUrl}&q=720`,
                downloadUrl: `${dynamicStreamUrl}&q=720&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (720p)`,
              },
              {
                id: `mb-lazy-${subjectId}-s${seNum}-e${epNum}-480`,
                quality: 480,
                qualityLabel: '480p Fast (MovieBox Direct)',
                audio: language,
                audioLanguages: [language],
                provider: 'MovieBox HD 480p',
                url: `${dynamicStreamUrl}&q=480`,
                downloadUrl: `${dynamicStreamUrl}&q=480&dl=1`,
                type: 'mp4',
                name: `${title} - S${seNum}E${epNum} (480p)`,
              },
              ...embedBackups,
            ],
          });
        }
      }
    }
  }

  // Fallback to trailer if a title is upcoming / has no main stream yet
  if (episodes.length === 0 && trailerMp4Url) {
    const trUrl = `/api/mb-stream.mp4?t=${Buffer.from(trailerMp4Url, 'utf8').toString('base64url')}`;
    episodes.push({
      id: `mb-trailer-${subjectId}`,
      label: 'Official Preview Stream',
      number: 1,
      rangeStart: 1,
      rangeEnd: 1,
      season: null,
      kind: 'movie',
      sources: [
        {
          id: `mb-trailer-src-${subjectId}`,
          quality: 720,
          qualityLabel: '720p Official Preview',
          audio: language,
          audioLanguages: [language],
          provider: 'MovieBox Preview',
          url: trUrl,
          downloadUrl: trUrl,
          type: 'mp4',
          name: `${title} (Preview)`,
        },
      ],
    });
  }

  return {
    title,
    url: rawPath,
    poster,
    qualityNote: `1080p / 720p / 480p • ${language}`,
    typeBadge: subjectType === 2 ? 'SERIES' : 'MOVIE',
    language,
    quality: '1080p FHD',
    genre,
    resolution: '1080p | 720p | 480p | 360p',
    releaseDate,
    storyline,
    youtubeTrailerId: '',
    screenshots,
    episodes,
    downloadButtons,
    cast,
    dubs,
    uploadedBy,
    communityScore: {
      recommendedPercent: Math.min(99, Math.max(75, Math.round(ratingVal * 10))),
      totalVotes: Number(subject.imdbRatingCount) || 1420,
      verdict: 'MovieBox HD Verified',
    },
  };
}

async function startServer() {
  const app = express();
  const PORT = Number(process.env.PORT) || 3000;

  app.use((req, res, next) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Range');
    if (req.method === 'OPTIONS') {
      res.status(204).end();
      return;
    }
    next();
  });

  app.use(express.json());

  // Pre-warm & auto-sync main catalog categories in background (merging MovieBox HD + primary nodes + myflixbd.to!)
  const syncLiveCategories = async () => {
    const warmPaths = ['/', '/anime', '/ongoing', '/drama', '/southIndian', '/bollywood', '/language/bangla', '/adult18plus'];
    for (const wp of warmPaths) {
      try {
        const cacheKey = `${wp}::page=1::q=::node=auto`;
        const mfPath = mapCategoryToMyFlixPath(wp, 1, '');
        const [mbRes, primaryRes, mfRes] = await Promise.allSettled([
          wp === '/adult18plus'
            ? Promise.resolve({ items: [], maxPage: 1 })
            : fetchMovieBoxCatalog(wp, 1, ''),
          fetchFromMirrors(wp),
          mfPath ? fetchMyFlixHtml(mfPath) : Promise.reject(new Error('No MF mapping')),
        ]);

        const mbParsed =
          mbRes.status === 'fulfilled' ? mbRes.value : { items: [], maxPage: 500 };
        const primaryParsed =
          primaryRes.status === 'fulfilled'
            ? parseMovieCards(primaryRes.value.html)
            : { items: [], maxPage: 520 };
        const activeNodeId =
          primaryRes.status === 'fulfilled' ? primaryRes.value.activeNodeId : 'node-moviebox';
        const mfParsed =
          mfRes.status === 'fulfilled' ? parseMyFlixCards(mfRes.value) : { items: [], maxPage: 342 };

        const firstMerge = mergeCatalogItems(mbParsed.items, primaryParsed.items, true);
        const rawMergedItems = mergeCatalogItems(firstMerge, mfParsed.items, false);
        const mergedItems =
          wp === '/'
            ? sortItemsByHotAndHype(rawMergedItems)
            : normalizeMovieCardList(rawMergedItems);
        if (mergedItems.length > 0) {
          const entry = {
            data: {
              items: mergedItems,
              maxPage: Math.max(mbParsed.maxPage, primaryParsed.maxPage, mfParsed.maxPage),
              activeNodeId,
            },
            expiresAt: Date.now() + 180_000,
          };
          pruneCacheMap(catalogCache, 80);
          catalogCache.set(cacheKey, entry);
          catalogCache.set(`${wp}::page=1::q=::node=${activeNodeId}`, entry);
          if (mbParsed.items.length > 0) {
            catalogCache.set(`${wp}::page=1::q=::node=node-moviebox`, {
              data: {
                items: normalizeMovieCardList(
                  mergeCatalogItems(mbParsed.items, primaryParsed.items, true)
                ),
                maxPage: mbParsed.maxPage,
                activeNodeId: 'node-moviebox',
              },
              expiresAt: Date.now() + 180_000,
            });
          }

          // Gently pre-warm top 2 uncached details per category so startup memory stays low
          const warmCount = wp === '/' ? 3 : 1;
          const candidates = mergedItems
            .slice(0, warmCount)
            .filter(
              (card) =>
                card.path &&
                !card.path.startsWith('/mf/') &&
                !findCachedDetailByPathOrTitle(card.path, card.title)
            );
          for (const card of candidates) {
            try {
              if (card.path.startsWith('/mb/')) {
                const mbDet = await fetchMovieBoxDetail(card.path);
                if (mbDet && mbDet.episodes.length > 0) {
                  storeDetailInCaches(card.path, mbDet, Date.now() + 3600_000);
                }
              } else {
                const { html, finalOrigin } = await fetchFromMirrors(card.path, activeNodeId);
                const det = parseMovieDetail(html, card.path, finalOrigin);
                if (det.episodes.length > 0) {
                  storeDetailInCaches(card.path, det, Date.now() + 3600_000);
                }
              }
            } catch {
              // ignore single detail warmup failure
            }
          }
        }
        await new Promise((r) => setTimeout(r, 350));
      } catch {
        // ignore background warmup errors
      }
    }
  };

  // 1. Categories & Anonymized Server Nodes Endpoint
  app.get('/api/categories', (_req, res) => {
    res.json({
      categories: ALL_CATEGORIES,
      nodes: SERVER_NODES.map(({ id, name, region }) => ({ id, name, region })),
    });
  });

  // 1b. MovieBox Official Home Page Layout (Banners, Sports Live, Quick Categories, Coming Soon, 20+ Shelves)
  app.get('/api/mb-home', async (_req, res) => {
    try {
      const payload = await fetchMovieBoxHomePayload();
      res.setHeader('Cache-Control', 'public, max-age=180, stale-while-revalidate=600');
      res.json(payload);
    } catch {
      res.json({
        ok: false,
        banners: [],
        liveSports: [],
        quickCategories: [],
        comingSoon: [],
        sections: [],
      });
    }
  });

  // 2. Live Server Node Ping & Health Check Endpoint (Anonymized)
  app.get('/api/server-health', async (_req, res) => {
    if (healthCache && healthCache.expiresAt > Date.now()) {
      res.json({ ok: true, nodes: healthCache.data });
      return;
    }

    const checks = await Promise.all(
      SERVER_NODES.map(async (node): Promise<ServerNodeStatus> => {
        const start = Date.now();
        try {
          const controller = new AbortController();
          const timer = setTimeout(() => controller.abort(), 4500);
          const r = await fetch(node.origin, {
            method: 'HEAD',
            signal: controller.signal,
            headers: { 'User-Agent': 'Mozilla/5.0' },
          });
          clearTimeout(timer);
          const latencyMs = Math.max(18, Date.now() - start);
          return {
            id: node.id,
            name: node.name,
            region: node.region,
            latencyMs,
            online: r.ok || r.status < 500,
          };
        } catch {
          return {
            id: node.id,
            name: node.name,
            region: node.region,
            latencyMs: 999,
            online: false,
          };
        }
      })
    );

    healthCache = {
      data: checks,
      expiresAt: Date.now() + 30_000,
    };

    res.json({ ok: true, nodes: checks });
  });

  // 3. Instant Live Search Suggestions Endpoint (Searches MovieBox HD + Primary Mirrors + MyFlixBD in parallel!)
  app.get('/api/suggest', async (req, res) => {
    const q = String(req.query.q || '').trim();
    const nodeId = String(req.query.node || '').trim();
    if (q.length < 1) {
      res.json({ ok: true, items: [] });
      return;
    }

    const lowerQ = q.toLowerCase();
    const collectLocalMatches = (): MovieCardItem[] => {
      const localPool: MovieCardItem[] = [];
      for (const [, entry] of catalogCache.entries()) {
        for (const it of entry.data.items) {
          if (it.title.toLowerCase().includes(lowerQ)) {
            localPool.push(it);
          }
        }
      }
      for (const list of Object.values(INITIAL_FALLBACK_MOVIES)) {
        for (const it of list) {
          if (it.title.toLowerCase().includes(lowerQ)) {
            localPool.push(it);
          }
        }
      }
      return deduplicateMovieCards(localPool);
    };

    const interleaveThreeSites = (list: MovieCardItem[]): MovieCardItem[] => {
      const mb = list.filter((i) => i.path?.startsWith('/mb/'));
      const mf = list.filter((i) => i.path?.startsWith('/mf/'));
      const mlbd = list.filter((i) => !i.path?.startsWith('/mb/') && !i.path?.startsWith('/mf/'));
      const out: MovieCardItem[] = [];
      const maxLen = Math.max(mb.length, mlbd.length, mf.length);
      for (let i = 0; i < maxLen; i++) {
        if (i < mb.length) out.push(mb[i]);
        if (i < mlbd.length) out.push(mlbd[i]);
        if (i < mf.length) out.push(mf[i]);
      }
      return deduplicateMovieCards(out);
    };

    const targetPath = `/search?q=${encodeURIComponent(q)}`;
    const cacheKey = `suggest::${targetPath}::all3`;
    const cached = catalogCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json({ ok: true, items: cached.data.items.slice(0, 18) });
      return;
    }

    try {
      const [mbRes, primaryRes, mfRes] = await Promise.allSettled([
        fetchMovieBoxCatalog('/', 1, q),
        fetchFromMirrors(targetPath, nodeId),
        fetchMyFlixHtml(`/?s=${encodeURIComponent(q)}`, 4200),
      ]);

      const mbItems = mbRes.status === 'fulfilled' ? mbRes.value.items : [];
      const primaryItems =
        primaryRes.status === 'fulfilled' ? parseMovieCards(primaryRes.value.html).items : [];
      const mfItems =
        mfRes.status === 'fulfilled' ? parseMyFlixCards(mfRes.value).items : [];
      const activeNodeId =
        nodeId === 'node-moviebox'
          ? 'node-moviebox'
          : primaryRes.status === 'fulfilled'
            ? primaryRes.value.activeNodeId
            : 'node-moviebox';

      const localMatches = collectLocalMatches();
      const combined = interleaveThreeSites([
        ...mbItems,
        ...primaryItems,
        ...mfItems,
        ...localMatches,
      ]);

      if (combined.length > 0) {
        catalogCache.set(cacheKey, {
          data: { items: combined, maxPage: 1, activeNodeId },
          expiresAt: Date.now() + 120_000,
        });
        res.json({ ok: true, items: combined.slice(0, 18) });
        return;
      }
    } catch {
      // fallback below
    }

    const fallback = interleaveThreeSites(collectLocalMatches());
    res.json({ ok: true, items: fallback.slice(0, 18) });
  });

  // 4. Live Catalog & Search Endpoint (Merging MovieBox HD + Primary Mirrors + MyFlixBD for 100% Content Coverage!)
  app.get('/api/catalog', async (req, res) => {
    const rawPath = String(req.query.path || '/').trim();
    const page = Math.max(1, parseInt(String(req.query.page || '1'), 10) || 1);
    const search = String(req.query.q || '').trim();
    const nodeId = String(req.query.node || '').trim();
    const forceRefresh = String(req.query.refresh || '0') === '1';

    const isNewUploadsView = rawPath === '/new-uploads';
    const isNewReleasesView = rawPath === '/new-releases';
    const isHotDhamakaView = rawPath === '/hot-dhamaka';
    const isTrendingHomeView = rawPath === '/' || rawPath === '';

    let upstreamBasePath = rawPath.startsWith('/') ? rawPath : `/${rawPath}`;
    if (isNewUploadsView || isNewReleasesView || isHotDhamakaView) {
      upstreamBasePath = '/';
    }

    let targetPath = upstreamBasePath;
    if (search) {
      targetPath =
        page > 1
          ? `/search/page/${page}?q=${encodeURIComponent(search)}`
          : `/search?q=${encodeURIComponent(search)}`;
    } else if (page > 1) {
      const base = upstreamBasePath === '/' ? '' : upstreamBasePath.replace(/\/+$/, '');
      targetPath = `${base}/page/${page}`;
    }

    const collectPrefetchedDetails = (list: MovieCardItem[], warmNodeId: string) => {
      const prefetchedDetails: Record<string, MovieDetailData> = {};
      const missingCards: MovieCardItem[] = [];
      for (const item of list.slice(0, 24)) {
        if (!item?.path) continue;
        const hit = findCachedDetailByPathOrTitle(item.path, item.title);
        if (hit && hit.episodes?.length) {
          prefetchedDetails[item.path] = hit;
          if (!detailCache.has(item.path)) {
            detailCache.set(item.path, { data: hit, expiresAt: Date.now() + 3600_000 });
          }
        } else if (!item.path.startsWith('/mf/')) {
          missingCards.push(item);
        }
      }
      if (missingCards.length > 0) {
        void (async () => {
          // Gently pre-warm only the top 3 cards sequentially so background warmup never competes with user clicks
          for (const card of missingCards.slice(0, 3)) {
            if (findCachedDetailByPathOrTitle(card.path, card.title)) continue;
            try {
              if (card.path.startsWith('/mb/')) {
                const mbDet = await fetchMovieBoxDetail(card.path);
                if (mbDet && mbDet.episodes.length > 0) {
                  storeDetailInCaches(card.path, mbDet, Date.now() + 3600_000);
                }
              } else {
                const { html, finalOrigin } = await fetchFromMirrors(card.path, warmNodeId);
                const det = parseMovieDetail(html, card.path, finalOrigin);
                if (det.episodes.length > 0) {
                  storeDetailInCaches(card.path, det, Date.now() + 3600_000);
                }
              }
            } catch {
              // ignore
            }
          }
        })();
      }
      return prefetchedDetails;
    };

    const cacheKey = `${rawPath}::page=${page}::q=${search}::node=${nodeId || 'auto'}`;
    const cached = catalogCache.get(cacheKey);
    if (!forceRefresh && cached && cached.expiresAt > Date.now()) {
      const normalized = normalizeMovieCardList(cached.data.items);
      res.json({
        ok: true,
        cached: true,
        path: rawPath,
        page,
        maxPage: cached.data.maxPage,
        activeNodeId: cached.data.activeNodeId,
        items: normalized,
        prefetchedDetails: collectPrefetchedDetails(normalized, cached.data.activeNodeId),
      });
      return;
    }

    try {
      const mfTargetPath = mapCategoryToMyFlixPath(upstreamBasePath, page, search);
      const mbTargetPath = isNewReleasesView
        ? '/new-releases'
        : isNewUploadsView
          ? '/new-uploads'
          : upstreamBasePath;
      const shouldFetchExtraArchivePage =
        !search &&
        page === 1 &&
        (isTrendingHomeView ||
          isHotDhamakaView ||
          isNewUploadsView ||
          isNewReleasesView ||
          upstreamBasePath === '/movies');
      const baseClean = upstreamBasePath === '/' ? '' : upstreamBasePath.replace(/\/+$/, '');
      const extraPrimaryPage2Path = `${baseClean}/page/2`;
      const extraMfPage2Path = mapCategoryToMyFlixPath(upstreamBasePath, 2, '');

      const [mbRes, primaryRes, mfRes, primaryPage2Res, mfPage2Res] = await Promise.allSettled([
        upstreamBasePath === '/adult18plus' && !search
          ? Promise.resolve({ items: [], maxPage: 1 })
          : fetchMovieBoxCatalog(mbTargetPath, page, search),
        fetchFromMirrors(targetPath, nodeId),
        mfTargetPath ? fetchMyFlixHtml(mfTargetPath) : Promise.reject(new Error('No MF path')),
        shouldFetchExtraArchivePage
          ? fetchFromMirrors(extraPrimaryPage2Path, nodeId)
          : Promise.reject(new Error('Skip extra primary page')),
        shouldFetchExtraArchivePage && extraMfPage2Path
          ? fetchMyFlixHtml(extraMfPage2Path)
          : Promise.reject(new Error('Skip extra MF page')),
      ]);

      const mbParsed =
        mbRes.status === 'fulfilled' ? mbRes.value : { items: [], maxPage: 2500 };
      const primaryParsed =
        primaryRes.status === 'fulfilled'
          ? parseMovieCards(primaryRes.value.html)
          : { items: [], maxPage: 520 };
      const primaryPage2Items =
        primaryPage2Res.status === 'fulfilled'
          ? parseMovieCards(primaryPage2Res.value.html).items
          : [];
      const mfParsed =
        mfRes.status === 'fulfilled'
          ? parseMyFlixCards(mfRes.value)
          : { items: [], maxPage: 342 };
      const mfPage2Items =
        mfPage2Res.status === 'fulfilled' ? parseMyFlixCards(mfPage2Res.value).items : [];

      const activeNodeId =
        nodeId === 'node-moviebox'
          ? 'node-moviebox'
          : nodeId === 'node-myflix'
            ? 'node-myflix'
            : primaryRes.status === 'fulfilled'
              ? primaryRes.value.activeNodeId
              : mbParsed.items.length > 0
                ? 'node-moviebox'
                : 'node-myflix';

      const allPrimaryItems = [...primaryParsed.items, ...primaryPage2Items];
      const allMfItems = [...mfParsed.items, ...mfPage2Items];

      let items: MovieCardItem[] = [];
      if (search) {
        // Interleave MovieBox HD, MovieLinkBD, and MyFlixBD search results equally + local cached matches from all 3 sites!
        const lowerSearch = search.toLowerCase();
        const extraSearchMatches: MovieCardItem[] = [];
        for (const [, entry] of catalogCache.entries()) {
          for (const it of entry.data.items) {
            if (it.title.toLowerCase().includes(lowerSearch)) {
              extraSearchMatches.push(it);
            }
          }
        }
        for (const list of Object.values(INITIAL_FALLBACK_MOVIES)) {
          for (const it of list) {
            if (it.title.toLowerCase().includes(lowerSearch)) {
              extraSearchMatches.push(it);
            }
          }
        }
        const mbPool = [
          ...mbParsed.items,
          ...extraSearchMatches.filter((i) => i.path?.startsWith('/mb/')),
        ];
        const mlbdPool = [
          ...allPrimaryItems,
          ...extraSearchMatches.filter(
            (i) => !i.path?.startsWith('/mb/') && !i.path?.startsWith('/mf/')
          ),
        ];
        const mfPool = [
          ...allMfItems,
          ...extraSearchMatches.filter((i) => i.path?.startsWith('/mf/')),
        ];
        const interleavedSearch: MovieCardItem[] = [];
        const maxSearchLen = Math.max(mbPool.length, mlbdPool.length, mfPool.length);
        for (let i = 0; i < maxSearchLen; i++) {
          if (i < mbPool.length) interleavedSearch.push(mbPool[i]);
          if (i < mlbdPool.length) interleavedSearch.push(mlbdPool[i]);
          if (i < mfPool.length) interleavedSearch.push(mfPool[i]);
        }
        items = deduplicateMovieCards(interleavedSearch);
      } else {
        const mbAndPrimary = mergeCatalogItems(mbParsed.items, allPrimaryItems, true);
        items = mergeCatalogItems(
          mbAndPrimary,
          allMfItems,
          nodeId === 'node-myflix'
        );
      }

      // For Trending (/), Hot & Dhamaka (/hot-dhamaka), New Upload (/new-uploads), and New Release (/new-releases) on page 1,
      // also include any brand-new uploads discovered in other cached categories!
      if (!search && (isTrendingHomeView || isHotDhamakaView || isNewUploadsView || isNewReleasesView)) {
        if (page === 1) {
          const extraRecent: MovieCardItem[] = [];
          for (const [k, entry] of catalogCache.entries()) {
            if (k.includes('adult18plus')) continue;
            for (const it of entry.data.items.slice(0, 14)) {
              if (!it.isAdult) extraRecent.push(it);
            }
          }
          items = mergeCatalogItems(items, extraRecent, false);
        }
        if (isHotDhamakaView) {
          items = sortItemsByHotAndHype(items);
        } else if (isNewUploadsView) {
          items = sortItemsByRecentUpload(items);
        } else if (isNewReleasesView) {
          const sortedRecent = sortItemsByRecentUpload(items);
          const release2026And2025 = sortedRecent.filter(
            (i) => i.title.includes('2026') || i.title.includes('2025')
          );
          const releaseOlder = sortedRecent.filter(
            (i) => !i.title.includes('2026') && !i.title.includes('2025')
          );
          items = [...release2026And2025, ...releaseOlder];
        } else {
          items = sortItemsByHotAndHype(items);
        }
      } else {
        items = normalizeMovieCardList(items);
      }

      const maxPage = Math.max(mbParsed.maxPage, primaryParsed.maxPage, mfParsed.maxPage);

      if (items.length > 0) {
        catalogCache.set(cacheKey, {
          data: { items, maxPage, activeNodeId },
          expiresAt: Date.now() + 30_000,
        });
        res.json({
          ok: true,
          cached: false,
          path: rawPath,
          page,
          maxPage,
          activeNodeId,
          items,
          prefetchedDetails: collectPrefetchedDetails(items, activeNodeId),
        });
        return;
      }
    } catch (err) {
      console.error('Catalog fetch error:', err);
    }

    const fallbackItems = sortItemsByRecentUpload(
      INITIAL_FALLBACK_MOVIES[rawPath] || INITIAL_FALLBACK_MOVIES['/'] || []
    );
    res.json({
      ok: true,
      fallback: true,
      path: rawPath,
      page,
      maxPage: 520,
      activeNodeId: 'node-moviebox',
      items: fallbackItems,
    });
  });

  // 5. Live Movie / Anime / Series Decryptor & Detail Extractor (Supports both Primary & MyFlixBD `/mf/...` + Cross-Source Stream Merging!)
  app.get('/api/details', async (req, res) => {
    const rawPath = String(req.query.path || req.query.url || '').trim();
    const fallbackTitle = String(req.query.title || '').trim();
    const nodeId = String(req.query.node || '').trim();

    if (!rawPath && !fallbackTitle) {
      res.status(400).json({ ok: false, error: 'Missing path or title parameter' });
      return;
    }

    const attachFastRelatedSeasons = (detailObj: MovieDetailData): MovieDetailData => {
      if (detailObj.relatedSeasons && detailObj.relatedSeasons.length > 0) return detailObj;
      // Only attach related seasons for SERIES/ANIME/DRAMA, and only when the base series title matches exactly!
      if (detailObj.typeBadge === 'MOVIE' && (detailObj.episodes?.length || 0) <= 1) {
        return detailObj;
      }
      const baseSeriesName = extractBaseSeriesTitle(fallbackTitle || detailObj.title);
      if (baseSeriesName && baseSeriesName.length >= 3) {
        const baseLower = baseSeriesName.toLowerCase();
        const matchingSeasons: MovieCardItem[] = [];
        const seenPaths = new Set<string>();
        for (const entry of catalogCache.values()) {
          for (const item of entry.data.items) {
            if (seenPaths.has(item.path) || item.path === detailObj.url) continue;
            const itemBase = extractBaseSeriesTitle(item.title).toLowerCase();
            if (itemBase === baseLower) {
              seenPaths.add(item.path);
              matchingSeasons.push(item);
            }
          }
        }
        if (matchingSeasons.length > 0) {
          return { ...detailObj, relatedSeasons: matchingSeasons.slice(0, 12) };
        }
      }
      return detailObj;
    };

    const isEnrich = req.query.enrich === '1';

    const ensureDetailDubsAndUploader = (detailObj: MovieDetailData): MovieDetailData => {
      const dubs: MovieDubOption[] = Array.isArray(detailObj.dubs) ? [...detailObj.dubs] : [];
      const seenLabels = new Set(dubs.map((d) => d.label.toLowerCase()));

      const normalizeAudioLabel = (rawAudio: string): string => {
        const a = String(rawAudio || '').trim();
        if (!a) return 'Original Audio';
        if (/hindi/i.test(a) && /bangla|bengali/i.test(a)) return 'Hindi + Bangla dub';
        if (/hindi/i.test(a) && !/dub/i.test(a)) return 'Hindi dub';
        if (/bangla|bengali/i.test(a) && !/dub/i.test(a) && !/sub/i.test(a)) return 'Bangla dub';
        return a;
      };

      if (dubs.length === 0) {
        const primaryLabel = normalizeAudioLabel(detailObj.language || 'Original Audio');
        seenLabels.add(primaryLabel.toLowerCase());
        dubs.push({
          id: `dub-primary-${detailObj.url}`,
          label: primaryLabel,
          path: detailObj.url,
          active: true,
        });
      }

      for (const ep of detailObj.episodes || []) {
        for (const src of ep.sources || []) {
          const candidates = [src.audio, ...(src.audioLanguages || [])].filter(Boolean);
          for (const c of candidates) {
            const lbl = normalizeAudioLabel(c);
            const key = lbl.toLowerCase();
            if (lbl && !seenLabels.has(key)) {
              seenLabels.add(key);
              dubs.push({
                id: `dub-src-${key}`,
                label: lbl,
                path: detailObj.url,
                active: false,
              });
            }
          }
        }
      }

      for (const rel of detailObj.relatedSeasons || []) {
        const relLang = normalizeAudioLabel(rel.language || '');
        const key = relLang.toLowerCase();
        if (relLang && !seenLabels.has(key)) {
          seenLabels.add(key);
          dubs.push({
            id: `dub-rel-${rel.id || rel.path}`,
            label: relLang,
            path: rel.path,
            active: false,
          });
        }
      }

      return {
        ...detailObj,
        dubs,
        uploadedBy: detailObj.uploadedBy || 'MarieNo Ess',
      };
    };

    // 1. Instant 0ms O(1) check by path OR canonical title (including /mb/ and /mf/ cards!)
    const instantHit = findCachedDetailByPathOrTitle(rawPath, !isEnrich ? fallbackTitle : '');
    if (instantHit) {
      if (rawPath && !detailCache.has(rawPath)) {
        detailCache.set(rawPath, { data: instantHit, expiresAt: Date.now() + 3600_000 });
      }
      res.json({
        ok: true,
        cached: true,
        detail: ensureDetailDubsAndUploader(attachFastRelatedSeasons(instantHit)),
      });
      return;
    }

    // 2. Dedicated MovieBox HD `/mb/<subjectId>/<detailSlug>[?se=N]` Direct Ad-Free MP4 Stream & Detail Resolver!
    if (rawPath.startsWith('/mb/')) {
      try {
        let mbDetail = await fetchMovieBoxDetail(rawPath);
        if (mbDetail) {
          const enrichMovieBoxWithBackups = async (baseMb: MovieDetailData): Promise<MovieDetailData> => {
            const enriched: MovieDetailData = {
              ...baseMb,
              episodes: baseMb.episodes.map((e) => ({ ...e, sources: [...e.sources] })),
              downloadButtons: [...baseMb.downloadButtons],
            };
            const wantBase = extractBaseSeriesTitle(enriched.title).toLowerCase();
            const norm = (s: string) => extractBaseSeriesTitle(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
            const wantNorm = norm(enriched.title);
            if (wantBase.length >= 2) {
              const [primarySearchRes, mfSearchRes] = await Promise.allSettled([
                fetchFromMirrors(`/search?q=${encodeURIComponent(wantBase)}`, nodeId),
                fetchMyFlixHtml(`/?s=${encodeURIComponent(wantBase)}`, 2800),
              ]);

              if (primarySearchRes.status === 'fulfilled') {
                try {
                  const { items } = parseMovieCards(primarySearchRes.value.html);
                  const matchedItem = items.find((it) => {
                    const itBase = extractBaseSeriesTitle(it.title).toLowerCase();
                    const itNorm = norm(it.title);
                    return (
                      itBase === wantBase ||
                      (itNorm &&
                        wantNorm &&
                        (itNorm === wantNorm ||
                          (itNorm.length >= 4 && wantNorm.includes(itNorm)) ||
                          (wantNorm.length >= 4 && itNorm.includes(wantNorm))))
                    );
                  });
                  if (matchedItem) {
                    const primaryRes = await fetchFromMirrors(matchedItem.path, nodeId);
                    const primaryDet = parseMovieDetail(primaryRes.html, rawPath, primaryRes.finalOrigin);
                    if (primaryDet.episodes.length > 0) {
                      if (enriched.episodes.length === 0) {
                        enriched.episodes = primaryDet.episodes;
                      } else {
                        enriched.episodes = enriched.episodes.map((mbEp, idx) => {
                          const matchedPEp =
                            primaryDet.episodes.find(
                              (pe) =>
                                pe.number === mbEp.number &&
                                (!mbEp.season || !pe.season || pe.season === mbEp.season)
                            ) ||
                            primaryDet.episodes.find((pe) => pe.number === mbEp.number) ||
                            primaryDet.episodes[idx] ||
                            primaryDet.episodes[0];
                          return {
                            ...mbEp,
                            // Keep movie-box.co Direct H.264 MP4 streams FIRST, followed by MovieLinkBD backup streams!
                            sources: [...mbEp.sources, ...(matchedPEp?.sources || [])],
                          };
                        });
                      }
                      enriched.downloadButtons = [
                        ...enriched.downloadButtons,
                        ...primaryDet.downloadButtons,
                      ];
                    }
                  }
                } catch {
                  // ignore primary mirror enrichment error
                }
              }

              if (mfSearchRes.status === 'fulfilled' && mfSearchRes.value) {
                try {
                  const mfCards = parseMyFlixCards(mfSearchRes.value).items;
                  const matchedMf = mfCards.find((c) => {
                    const cNorm = norm(c.title);
                    return (
                      cNorm &&
                      wantNorm &&
                      (cNorm === wantNorm ||
                        (cNorm.length >= 4 && wantNorm.includes(cNorm)) ||
                        (wantNorm.length >= 4 && cNorm.includes(wantNorm)))
                    );
                  });
                  if (matchedMf) {
                    const mfRealPath = matchedMf.path.replace(/^\/mf\//, '/');
                    const mfDetailHtml = await fetchMyFlixHtml(`${mfRealPath}/`, 3000);
                    const mfDet = parseMyFlixDetail(mfDetailHtml, rawPath);
                    if (mfDet.episodes.length > 0) {
                      if (enriched.episodes.length === 0) {
                        enriched.episodes = mfDet.episodes;
                      } else {
                        enriched.episodes = enriched.episodes.map((mbEp, idx) => {
                          const matchedMfEp =
                            mfDet.episodes.find((me) => me.number === mbEp.number) ||
                            mfDet.episodes[idx] ||
                            mfDet.episodes[0];
                          return {
                            ...mbEp,
                            sources: [...mbEp.sources, ...(matchedMfEp?.sources || [])],
                          };
                        });
                      }
                      enriched.downloadButtons = [
                        ...enriched.downloadButtons,
                        ...mfDet.downloadButtons,
                      ];
                    }
                  }
                } catch {
                  // ignore MyFlix enrichment error
                }
              }
            }
            const finalEnriched = ensureDetailDubsAndUploader(attachFastRelatedSeasons(enriched));
            storeDetailInCaches(rawPath, finalEnriched, Date.now() + 12 * 60_000);
            return finalEnriched;
          };

          if (!isEnrich && mbDetail.episodes.length > 0) {
            mbDetail = ensureDetailDubsAndUploader(attachFastRelatedSeasons(mbDetail));
            storeDetailInCaches(rawPath, mbDetail, Date.now() + 12 * 60_000);
            res.json({ ok: true, detail: mbDetail });
            return;
          }

          mbDetail = await enrichMovieBoxWithBackups(mbDetail);
          res.json({ ok: true, detail: mbDetail });
          return;
        }
      } catch (err) {
        console.error('MovieBox detail fetch error:', err);
      }
    }

    // Helper: Enrich any non-MovieBox detail with MovieBox HD's dubs, seasons, and streams!
    const enrichWithMovieBoxStreams = async (detail: MovieDetailData): Promise<MovieDetailData> => {
      try {
        const cleanQuery = extractBaseSeriesTitle(fallbackTitle || detail.title)
          .split(/\s+/)
          .slice(0, 4)
          .join(' ');
        if (cleanQuery.length < 2) return detail;
        const mbCatalog = await fetchMovieBoxCatalog('/', 1, cleanQuery);
        if (!mbCatalog.items.length) return detail;
        const norm = (s: string) => extractBaseSeriesTitle(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
        const wantNorm = norm(fallbackTitle || detail.title);
        const matchedMb = mbCatalog.items.find((c) => {
          const cNorm = norm(c.title);
          return (
            cNorm &&
            wantNorm &&
            (cNorm === wantNorm ||
              (cNorm.length >= 4 && wantNorm.includes(cNorm)) ||
              (wantNorm.length >= 4 && cNorm.includes(wantNorm)))
          );
        });
        if (!matchedMb) return detail;
        const mbDet = await fetchMovieBoxDetail(matchedMb.path);
        if (!mbDet || mbDet.episodes.length === 0) return detail;
        if (detail.episodes.length === 0) {
          return {
            ...detail,
            dubs: mbDet.dubs || detail.dubs,
            uploadedBy: mbDet.uploadedBy || detail.uploadedBy,
            episodes: mbDet.episodes,
            downloadButtons: [...detail.downloadButtons, ...mbDet.downloadButtons],
          };
        }
        const mergedEpisodes = detail.episodes.map((ep, idx) => {
          const matchedMbEp =
            mbDet.episodes.find(
              (me) => me.number === ep.number && (!ep.season || !me.season || me.season === ep.season)
            ) ||
            mbDet.episodes.find((me) => me.number === ep.number) ||
            mbDet.episodes[idx] ||
            mbDet.episodes[0];
          return {
            ...ep,
            // Put movie-box.co Direct H.264 MP4 streams FIRST, followed by primary streams!
            sources: [...(matchedMbEp?.sources || []), ...ep.sources],
          };
        });
        // Also append any additional episodes or seasons from MovieBox HD that were missing in the primary/MyFlix listing!
        for (const mbEp of mbDet.episodes) {
          const alreadyExists = mergedEpisodes.some(
            (e) =>
              e.number === mbEp.number &&
              ((e.season || 1) === (mbEp.season || 1) || mergedEpisodes.length === 1)
          );
          if (!alreadyExists) {
            mergedEpisodes.push(mbEp);
          }
        }
        return {
          ...detail,
          dubs: mbDet.dubs || detail.dubs,
          uploadedBy: mbDet.uploadedBy || detail.uploadedBy,
          episodes: mergedEpisodes,
          downloadButtons: [...detail.downloadButtons, ...mbDet.downloadButtons],
        };
      } catch {
        return detail;
      }
    };

    // 3. Dedicated MyFlixBD `/mf/...` Detail & Stream Extractor (Prefer direct ad-free MovieBox & primary streams first!)
    if (rawPath.startsWith('/mf/')) {
      try {
        const mfRealPath = rawPath.replace(/^\/mf\//, '/');
        const searchTitle = extractBaseSeriesTitle(fallbackTitle)
          .split(/\s+/)
          .slice(0, 4)
          .join(' ');

        const [mfHtmlRes, primarySearchRes] = await Promise.allSettled([
          fetchMyFlixHtml(`${mfRealPath}/`, 3800),
          searchTitle.length >= 3
            ? fetchFromMirrors(`/search?q=${encodeURIComponent(searchTitle)}`, nodeId)
            : Promise.reject(new Error('No search title')),
        ]);

        if (mfHtmlRes.status !== 'fulfilled') {
          throw new Error('MyFlix unreachable');
        }

        let detail = parseMyFlixDetail(mfHtmlRes.value, rawPath);

        if (primarySearchRes.status === 'fulfilled') {
          try {
            const { items } = parseMovieCards(primarySearchRes.value.html);
            if (items.length > 0) {
              const wantBase = extractBaseSeriesTitle(fallbackTitle || detail.title).toLowerCase();
              const matchedItem = items.find(
                (it) => extractBaseSeriesTitle(it.title).toLowerCase() === wantBase
              );
              if (matchedItem) {
                const cachedPrimary = detailCache.get(matchedItem.path);
                const primaryDetail = cachedPrimary
                  ? cachedPrimary.data
                  : await fetchFromMirrors(matchedItem.path, nodeId).then((r) =>
                      parseMovieDetail(r.html, rawPath, r.finalOrigin)
                    );
                if (primaryDetail.episodes.length > 0) {
                  // Put direct <video> streams first so OS PiP, Auto Landscape, and Quality Selection work natively!
                  if (detail.episodes.length > 0) {
                    detail.episodes = detail.episodes.map((mfEp, idx) => {
                      const matchedPrimaryEp =
                        primaryDetail.episodes.find((pe) => pe.number === mfEp.number) ||
                        primaryDetail.episodes[idx];
                      return {
                        ...mfEp,
                        sources: [
                          ...(matchedPrimaryEp?.sources || []),
                          ...mfEp.sources,
                        ],
                      };
                    });
                  } else {
                    detail.episodes = primaryDetail.episodes;
                  }
                  detail.downloadButtons = [
                    ...primaryDetail.downloadButtons,
                    ...detail.downloadButtons,
                  ];
                }
              }
            }
          } catch {
            // keep MyFlix streams if primary search fails
          }
        }

        detail = await enrichWithMovieBoxStreams(detail);
        detail = ensureDetailDubsAndUploader(attachFastRelatedSeasons(detail));
        if (detail.episodes.length > 0 || detail.downloadButtons.length > 0) {
          detailCache.set(rawPath, {
            data: detail,
            expiresAt: Date.now() + 30 * 60_000,
          });
        }
        res.json({ ok: true, detail });
        return;
      } catch (err) {
        console.error('MyFlix detail fetch error:', err);
      }
    }

    try {
      let { html, finalOrigin } = await fetchFromMirrors(rawPath || '/', nodeId);

      const is404 =
        html.length < 1500 ||
        html.includes('<div class="n">404</div>') ||
        html.includes('Page not found') ||
        !html.includes('mlbdInlinePlayerData');

      if (is404 && fallbackTitle) {
        const cleanQuery = extractBaseSeriesTitle(fallbackTitle)
          .split(/\s+/)
          .slice(0, 4)
          .join(' ');

        if (cleanQuery) {
          const searchRes = await fetchFromMirrors(`/search?q=${encodeURIComponent(cleanQuery)}`, nodeId);
          const { items } = parseMovieCards(searchRes.html);
          if (items.length > 0) {
            const wantSeasonMatch = fallbackTitle.match(/\b(S\d+|Season\s*\d+)/i);
            const wantSeason = wantSeasonMatch ? wantSeasonMatch[1].toLowerCase() : '';
            const bestItem =
              items.find((it) => wantSeason && it.title.toLowerCase().includes(wantSeason)) ||
              items.find((it) => Boolean(it.episodePill)) ||
              items[0];
            const resolved = await fetchFromMirrors(bestItem.path, nodeId);
            html = resolved.html;
            finalOrigin = resolved.finalOrigin;
          }
        }
      }

      let detail = parseMovieDetail(html, rawPath, finalOrigin);

      const enrichPrimaryWithCrossSources = async (baseDet: MovieDetailData): Promise<MovieDetailData> => {
        let enriched = await enrichWithMovieBoxStreams(baseDet);
        try {
          const effectiveQuery = extractBaseSeriesTitle(fallbackTitle || enriched.title)
            .split(/\s+/)
            .slice(0, 4)
            .join(' ');
          const mfSearchHtml =
            effectiveQuery.length >= 2
              ? await fetchMyFlixHtml(`/?s=${encodeURIComponent(effectiveQuery)}`, 2800)
              : '';
          if (mfSearchHtml) {
            const mfCards = parseMyFlixCards(mfSearchHtml).items;
            if (mfCards.length > 0) {
              const norm = (s: string) => extractBaseSeriesTitle(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
              const wantNorm = norm(fallbackTitle || enriched.title);
              const matchedCard = mfCards.find((c) => {
                const cNorm = norm(c.title);
                return (
                  cNorm &&
                  wantNorm &&
                  (cNorm === wantNorm ||
                    (cNorm.length >= 4 && wantNorm.includes(cNorm)) ||
                    (wantNorm.length >= 4 && cNorm.includes(wantNorm)))
                );
              });
              if (matchedCard) {
                const mfRealPath = matchedCard.path.replace(/^\/mf\//, '/');
                const mfDetailHtml = await fetchMyFlixHtml(`${mfRealPath}/`, 3200);
                const mfDetail = parseMyFlixDetail(mfDetailHtml, rawPath);
                if (mfDetail.episodes.length > 0) {
                  if (enriched.episodes.length === 0) {
                    enriched = {
                      ...enriched,
                      episodes: mfDetail.episodes,
                      downloadButtons:
                        enriched.downloadButtons.length > 0
                          ? enriched.downloadButtons
                          : mfDetail.downloadButtons,
                    };
                  } else {
                    enriched.episodes = enriched.episodes.map((ep, idx) => {
                      const matchedMfEp =
                        mfDetail.episodes.find((me) => me.number === ep.number) ||
                        mfDetail.episodes[idx] ||
                        mfDetail.episodes[0];
                      const mfSources = matchedMfEp?.sources || [];
                      return {
                        ...ep,
                        sources: [...ep.sources, ...mfSources],
                      };
                    });
                  }
                }
              }
            }
          }
        } catch {
          // ignore MyFlix enrichment error
        }
        enriched = ensureDetailDubsAndUploader(attachFastRelatedSeasons(enriched));
        if (enriched.episodes.length > 0 || enriched.downloadButtons.length > 0 || enriched.storyline) {
          storeDetailInCaches(rawPath, enriched, Date.now() + 25 * 60_000);
        }
        return enriched;
      };

      if (!isEnrich && detail.episodes.length > 0) {
        detail = ensureDetailDubsAndUploader(attachFastRelatedSeasons(detail));
        storeDetailInCaches(rawPath, detail, Date.now() + 25 * 60_000);
        res.json({ ok: true, detail });
        return;
      }

      detail = await enrichPrimaryWithCrossSources(detail);
      res.json({ ok: true, detail });
    } catch (err) {
      console.error('Detail fetch error:', err);
      res.status(500).json({
        ok: false,
        error: 'ক্লাউড সার্ভার থেকে মুভির বিস্তারিত তথ্য লোড করা যায়নি। অনুগ্রহ করে অন্য Server Node সিলেক্ট করে চেষ্টা করুন।',
      });
    }
  });

  // 6. Opaque Anonymized Download & Stream Redirect Gateway (Automatically bypasses fifadekho landing gate!)
  app.get('/api/go', async (req, res) => {
    const token = String(req.query.t || '').trim();
    let target = decodeGatewayToken(token);
    if (!target || !target.startsWith('http')) {
      res.status(400).send('Invalid gateway link');
      return;
    }

    // If the link is a fifadekho.com gateway URL, automatically resolve `?view=links` to extract direct cloud download URL!
    if (/fifadekho\.com\/[a-z0-9]+/i.test(target) && !target.includes('view=links')) {
      try {
        const linksUrl = `${target.replace(/\/+$/, '')}?view=links`;
        const gwRes = await fetch(linksUrl, {
          headers: { 'User-Agent': 'Mozilla/5.0' },
        });
        if (gwRes.ok) {
          const gwHtml = await gwRes.text();
          const directCloudMatch = gwHtml.match(
            /<a\s+href=["'](https?:\/\/(?:hubcloud|new\d*\.xcloud|gdflix)[^"']+)["'][^>]*class=["'][^"']*nl-link-btn/i
          );
          if (directCloudMatch && directCloudMatch[1]) {
            target = directCloudMatch[1].trim();
          } else {
            target = linksUrl;
          }
        }
      } catch {
        target = `${target.replace(/\/+$/, '')}?view=links`;
      }
    }

    res.setHeader('Referrer-Policy', 'no-referrer');
    res.redirect(302, target);
  });

  // In-Memory Micro-Chunk Startup Buffer Cache (Caches initial 1.5MB startup chunk of active streams for 0ms instant start & zero socket hold!)
  const mbStartupChunkCache = new Map<
    string,
    {
      buf: Buffer;
      totalSize: number;
      contentType: string;
      expiresAt: number;
    }
  >();

  // 6a-1. MovieBox HD Micro-Chunked Turbo MP4 Stream & Download Proxy (1.5MB Startup Chunk + 2.5MB Playback Micro-Chunks + RAM Cache!)
  app.get(['/api/mb-stream', '/api/mb-stream.mp4'], async (req, res) => {
    const token = String(req.query.t || '').trim();
    const fbToken = String(req.query.fb || '').trim();
    const isDownload = String(req.query.dl || '0') === '1';
    const rawFilename = String(req.query.name || req.query.fn || 'CinePulse-MovieBox-HD.mp4')
      .replace(/[^a-zA-Z0-9._-]+/g, '-')
      .replace(/^-+|-+$/g, '');
    const targetUrl = decodeGatewayToken(token);
    const fallbackUrl = fbToken ? decodeGatewayToken(fbToken) : '';
    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid MovieBox stream token');
      return;
    }

    const INITIAL_STARTUP_CHUNK_BYTES = Math.floor(1.5 * 1024 * 1024); // 1.5MB micro-chunk for <80ms instant moov + keyframe start
    const PLAYBACK_MICRO_CHUNK_BYTES = Math.floor(2.5 * 1024 * 1024); // 2.5MB micro-chunk so sockets free up immediately between chunks

    let requestedStart = 0;
    let requestedEnd = NaN;
    if (req.headers.range) {
      const m = String(req.headers.range).match(/bytes=(\d+)-(\d*)/i);
      if (m) {
        requestedStart = parseInt(m[1], 10) || 0;
        requestedEnd = m[2] ? parseInt(m[2], 10) : NaN;
      }
    }

    // 0ms RAM Hit if the client is requesting bytes inside our cached 1.5MB startup micro-chunk!
    if (!isDownload && req.method !== 'HEAD' && requestedStart < INITIAL_STARTUP_CHUNK_BYTES) {
      const ramHit = mbStartupChunkCache.get(targetUrl);
      if (ramHit && ramHit.expiresAt > Date.now() && requestedStart < ramHit.buf.length) {
        const sliceEnd = !Number.isNaN(requestedEnd)
          ? Math.min(requestedEnd, ramHit.buf.length - 1)
          : ramHit.buf.length - 1;
        if (sliceEnd >= requestedStart) {
          const chunk = ramHit.buf.subarray(requestedStart, sliceEnd + 1);
          res.status(206);
          res.setHeader('Content-Type', ramHit.contentType || 'video/mp4');
          res.setHeader('Accept-Ranges', 'bytes');
          res.setHeader('Cache-Control', 'public, max-age=3600');
          res.setHeader('Content-Length', String(chunk.length));
          res.setHeader(
            'Content-Range',
            `bytes ${requestedStart}-${sliceEnd}/${ramHit.totalSize}`
          );
          res.end(chunk);
          return;
        }
      }
    }

    const abortController = new AbortController();
    res.on('close', () => {
      if (!res.writableEnded) {
        abortController.abort();
      }
    });

    const forwardHeaders: Record<string, string> = {
      'User-Agent':
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36',
      Referer: 'https://movie-box.co/',
      Origin: 'https://movie-box.co',
      Accept: '*/*',
    };

    const chunkCap =
      requestedStart === 0 ? INITIAL_STARTUP_CHUNK_BYTES : PLAYBACK_MICRO_CHUNK_BYTES;

    if (req.headers.range && !isDownload) {
      const cappedEnd =
        !Number.isNaN(requestedEnd) && requestedEnd >= requestedStart
          ? Math.min(requestedEnd, requestedStart + chunkCap - 1)
          : requestedStart + chunkCap - 1;
      forwardHeaders.Range = `bytes=${requestedStart}-${cappedEnd}`;
    } else if (!req.headers.range && !isDownload && req.method !== 'HEAD') {
      forwardHeaders.Range = `bytes=0-${INITIAL_STARTUP_CHUNK_BYTES - 1}`;
    } else if (req.headers.range) {
      forwardHeaders.Range = String(req.headers.range);
    }

    try {
      let upstream: Response | null = null;
      const refererCandidates = [
        { Referer: 'https://movie-box.co/', Origin: 'https://movie-box.co' },
        { Referer: 'https://movieboxhd.net/', Origin: 'https://movieboxhd.net' },
      ];
      for (let attempt = 0; attempt < refererCandidates.length; attempt++) {
        try {
          upstream = await fetch(targetUrl, {
            method: req.method === 'HEAD' ? 'HEAD' : 'GET',
            headers: { ...forwardHeaders, ...refererCandidates[attempt] },
            signal: abortController.signal,
          });
          if (upstream.ok || upstream.status === 206) {
            break;
          }
        } catch (fetchErr) {
          if (abortController.signal.aborted || attempt === refererCandidates.length - 1) throw fetchErr;
        }
      }

      // If primary regional CDN returns 426/429/403 on US Cloud Run IP and global macdn fallback URL is available, stream global MP4 seamlessly!
      if (
        (!upstream || (!upstream.ok && upstream.status !== 206)) &&
        fallbackUrl &&
        fallbackUrl.startsWith('http')
      ) {
        try {
          const fbHeaders: Record<string, string> = {
            'User-Agent': forwardHeaders['User-Agent'],
            Accept: '*/*',
          };
          if (forwardHeaders.Range) fbHeaders.Range = forwardHeaders.Range;
          const fbRes = await fetch(fallbackUrl, {
            method: req.method === 'HEAD' ? 'HEAD' : 'GET',
            headers: fbHeaders,
            signal: abortController.signal,
          });
          if (fbRes.ok || fbRes.status === 206) {
            upstream = fbRes;
          }
        } catch {
          // ignore fallback error
        }
      }

      if (!upstream || (!upstream.ok && upstream.status !== 206)) {
        res.status(upstream?.status || 502).send(`MovieBox CDN upstream returned ${upstream?.status || 502}`);
        return;
      }

      const contentType = upstream.headers.get('content-type') || 'video/mp4';
      const contentRange = upstream.headers.get('content-range') || '';
      const contentLength = upstream.headers.get('content-length');

      res.status(upstream.status);
      res.setHeader('Content-Type', contentType);
      res.setHeader('Accept-Ranges', upstream.headers.get('accept-ranges') || 'bytes');
      res.setHeader('Cache-Control', 'public, max-age=3600');
      if (contentLength) {
        res.setHeader('Content-Length', contentLength);
      }
      if (contentRange) {
        res.setHeader('Content-Range', contentRange);
      }
      if (isDownload) {
        res.setHeader(
          'Content-Disposition',
          `attachment; filename="${rawFilename.endsWith('.mp4') ? rawFilename : `${rawFilename}.mp4`}"`
        );
      }

      if (!upstream.body || req.method === 'HEAD') {
        res.end();
        return;
      }

      // Cache initial 0..1.5MB startup chunk in RAM while streaming it to the client!
      const shouldCacheStartupChunk =
        !isDownload &&
        requestedStart === 0 &&
        upstream.status === 206 &&
        !mbStartupChunkCache.has(targetUrl);
      const totalMatch = contentRange.match(/\/(\d+)$/);
      const parsedTotalSize = totalMatch ? parseInt(totalMatch[1], 10) : 0;
      const collectedChunks: Buffer[] = [];
      let collectedLen = 0;

      const nodeStream = Readable.fromWeb(upstream.body as any);
      if (shouldCacheStartupChunk && parsedTotalSize > 0) {
        nodeStream.on('data', (chunk: Buffer) => {
          if (collectedLen <= INITIAL_STARTUP_CHUNK_BYTES) {
            const b = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
            collectedChunks.push(b);
            collectedLen += b.length;
          }
        });
        nodeStream.on('end', () => {
          if (collectedLen > 32768 && collectedLen <= INITIAL_STARTUP_CHUNK_BYTES + 65536) {
            if (mbStartupChunkCache.size >= 24) {
              const oldestKey = mbStartupChunkCache.keys().next().value;
              if (oldestKey) mbStartupChunkCache.delete(oldestKey);
            }
            mbStartupChunkCache.set(targetUrl, {
              buf: Buffer.concat(collectedChunks),
              totalSize: parsedTotalSize,
              contentType,
              expiresAt: Date.now() + 10 * 60_000,
            });
          }
        });
      }
      nodeStream.on('error', () => {
        if (!res.headersSent) res.status(502).end();
        else res.end();
      });
      nodeStream.pipe(res);
    } catch {
      if (!res.headersSent) {
        res.status(502).send('MovieBox stream connection interrupted');
      } else {
        res.end();
      }
    }
  });

  // 6a-2. MovieBox HD On-Demand Episode Resolver (Resolves any Season/Episode direct MP4 stream on the fly and redirects to /api/mb-stream.mp4!)
  app.get(['/api/mb-ep-stream', '/api/mb-ep-stream.mp4'], async (req, res) => {
    const subjectId = String(req.query.subjectId || '').trim();
    const detailPath = String(req.query.detailPath || '').trim();
    const se = Math.max(0, parseInt(String(req.query.se || '1'), 10) || 1);
    const ep = Math.max(0, parseInt(String(req.query.ep || '1'), 10) || 1);
    const preferredQuality = parseInt(String(req.query.q || '720'), 10) || 720;
    const isDownload = String(req.query.dl || '0') === '1';
    const fbToken = String(req.query.fb || '').trim();
    const fallbackUrl = fbToken ? decodeGatewayToken(fbToken) : '';

    if (!subjectId || !detailPath) {
      res.status(400).send('Missing subjectId or detailPath');
      return;
    }

    try {
      let { sources } = await fetchMovieBoxPlayStreams(
        subjectId,
        detailPath,
        se,
        ep,
        detailPath,
        'English / Original',
        fallbackUrl
      );
      if (!sources.length) {
        // Fallback if episode numbering starts at 2 or uses movie (se=0, ep=0) indexing
        const fbNext = await fetchMovieBoxPlayStreams(
          subjectId,
          detailPath,
          se,
          ep + 1,
          detailPath,
          'English',
          fallbackUrl
        );
        if (fbNext.sources.length) sources = fbNext.sources;
      }
      if (!sources.length) {
        const fbMovie = await fetchMovieBoxPlayStreams(
          subjectId,
          detailPath,
          0,
          0,
          detailPath,
          'English',
          fallbackUrl
        );
        if (fbMovie.sources.length) sources = fbMovie.sources;
      }
      if (!sources.length) {
        if (fbToken) {
          res.redirect(302, `/api/mb-stream.mp4?t=${encodeURIComponent(fbToken)}`);
          return;
        }
        res.status(404).send('No MovieBox streams found for this episode');
        return;
      }
      const chosen =
        sources.find((s) => s.quality === preferredQuality) ||
        sources.find((s) => s.quality === 720) ||
        sources[0];
      const targetUrl = isDownload && chosen.downloadUrl ? chosen.downloadUrl : chosen.url;
      res.redirect(302, targetUrl);
    } catch {
      if (fbToken) {
        res.redirect(302, `/api/mb-stream.mp4?t=${encodeURIComponent(fbToken)}`);
        return;
      }
      res.status(502).send('Failed to resolve MovieBox episode stream');
    }
  });

  // 6b. Ultra-Fast Sequential MKV-to-HLS Live Streamer for iPhone / iPad (iOS Safari)
  interface IosHlsSession {
    hash: string;
    dir: string;
    targetUrl: string;
    proc: ChildProcess | null;
    abortController: AbortController;
    lastAccess: number;
    finished: boolean;
  }

  const iosHlsSessions = new Map<string, IosHlsSession>();

  const cleanupIosHlsSession = (hash: string) => {
    const sess = iosHlsSessions.get(hash);
    if (!sess) return;
    iosHlsSessions.delete(hash);
    try {
      sess.abortController.abort();
    } catch {
      // ignore
    }
    try {
      if (sess.proc && !sess.proc.killed) {
        sess.proc.kill('SIGKILL');
      }
    } catch {
      // ignore
    }
    try {
      fs.rmSync(sess.dir, { recursive: true, force: true });
    } catch {
      // ignore
    }
  };

  setInterval(() => {
    const now = Date.now();
    for (const [hash, sess] of iosHlsSessions.entries()) {
      if (now - sess.lastAccess > 120_000) {
        cleanupIosHlsSession(hash);
      }
    }
  }, 30_000).unref();

  const ensureIosHlsSession = async (targetUrl: string): Promise<IosHlsSession> => {
    const hash = crypto.createHash('sha1').update(targetUrl).digest('hex').slice(0, 16);
    const existing = iosHlsSessions.get(hash);
    if (existing && fs.existsSync(path.join(existing.dir, 'index.m3u8'))) {
      existing.lastAccess = Date.now();
      return existing;
    }

    if (existing) {
      cleanupIosHlsSession(hash);
    }

    // Keep at most 2 concurrent HLS remux sessions so /tmp stays lightweight
    if (iosHlsSessions.size >= 2) {
      const oldest = Array.from(iosHlsSessions.values()).sort(
        (a, b) => a.lastAccess - b.lastAccess
      )[0];
      if (oldest) cleanupIosHlsSession(oldest.hash);
    }

    const dir = path.join('/tmp', `cp-hls-${hash}`);
    fs.rmSync(dir, { recursive: true, force: true });
    fs.mkdirSync(dir, { recursive: true });

    const abortController = new AbortController();
    const session: IosHlsSession = {
      hash,
      dir,
      targetUrl,
      proc: null,
      abortController,
      lastAccess: Date.now(),
      finished: false,
    };
    iosHlsSessions.set(hash, session);

    const upstreamRes = await fetch(targetUrl, {
      signal: abortController.signal,
      headers: {
        'User-Agent':
          'Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1',
      },
    });

    if (!upstreamRes.ok || !upstreamRes.body) {
      cleanupIosHlsSession(hash);
      throw new Error(`Upstream stream HTTP ${upstreamRes.status}`);
    }

    const ff = spawn(FFMPEG_BIN, [
      '-hide_banner',
      '-loglevel',
      'error',
      '-fflags',
      '+nobuffer+genpts',
      '-probesize',
      '131072',
      '-analyzeduration',
      '100000',
      '-f',
      'matroska',
      '-i',
      'pipe:0',
      '-map',
      '0:v:0',
      '-map',
      '0:a:0?',
      '-c:v',
      'copy',
      '-c:a',
      'aac',
      '-ac',
      '2',
      '-b:a',
      '128k',
      '-af',
      "volume=enable='between(t,0,13.5)':volume=0",
      '-bsf:v',
      'h264_mp4toannexb',
      '-f',
      'hls',
      '-hls_playlist_type',
      'event',
      '-hls_time',
      '2',
      '-hls_list_size',
      '0',
      '-hls_flags',
      'independent_segments+temp_file',
      '-hls_segment_filename',
      path.join(dir, 'seg_%04d.ts'),
      path.join(dir, 'index.m3u8'),
    ]);

    session.proc = ff;
    ff.on('exit', () => {
      session.finished = true;
    });
    ff.stdin.on('error', () => {});

    const reader = upstreamRes.body.getReader();
    (async () => {
      let bytesTransferred = 0;
      const BURST_BYTES = 24 * 1024 * 1024; // 24MB instant high-speed burst (~3 mins of video)
      try {
        while (true) {
          if (Date.now() - session.lastAccess > 120_000) {
            cleanupIosHlsSession(hash);
            break;
          }
          const { done, value } = await reader.read();
          if (done) {
            ff.stdin.end();
            break;
          }
          bytesTransferred += value.byteLength;
          if (!ff.stdin.write(Buffer.from(value))) {
            await new Promise<void>((resolve) => ff.stdin.once('drain', () => resolve()));
          }
          // After initial 24MB burst, lightly pace download so /tmp is never flooded
          if (bytesTransferred > BURST_BYTES) {
            await new Promise((r) => setTimeout(r, 25));
          }
        }
      } catch {
        try {
          ff.stdin.end();
        } catch {
          // ignore
        }
      }
    })();

    // Wait up to 4.5s for index.m3u8 + first segments (seg_0001.ts or seg_0000.ts) to appear
    const startWait = Date.now();
    while (Date.now() - startWait < 4500) {
      const m3u8Path = path.join(dir, 'index.m3u8');
      const seg1Path = path.join(dir, 'seg_0001.ts');
      const seg0Path = path.join(dir, 'seg_0000.ts');
      if (
        fs.existsSync(m3u8Path) &&
        (fs.existsSync(seg1Path) || (fs.existsSync(seg0Path) && Date.now() - startWait > 1400))
      ) {
        return session;
      }
      await new Promise((r) => setTimeout(r, 45));
    }

    return session;
  };

  app.options('/api/ios-hls/:token/:file', (_req, res) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, HEAD, OPTIONS');
    res.status(204).end();
  });

  app.get('/api/ios-hls/:token/:file', async (req, res) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, HEAD, OPTIONS');

    const token = String(req.params.token || '').trim();
    const file = String(req.params.file || '').trim();
    const targetUrl = decodeGatewayToken(token);

    if (!targetUrl || !targetUrl.startsWith('http')) {
      res.status(400).send('Invalid stream token');
      return;
    }

    try {
      if (file === 'index.m3u8') {
        const session = await ensureIosHlsSession(targetUrl);
        session.lastAccess = Date.now();
        const m3u8Path = path.join(session.dir, 'index.m3u8');
        if (!fs.existsSync(m3u8Path)) {
          res.status(503).send('HLS playlist initializing');
          return;
        }
        res.setHeader('Content-Type', 'application/vnd.apple.mpegurl');
        res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
        res.send(fs.readFileSync(m3u8Path, 'utf8'));
        return;
      }

      if (/^seg_\d+\.ts$/.test(file)) {
        const hash = crypto.createHash('sha1').update(targetUrl).digest('hex').slice(0, 16);
        let session = iosHlsSessions.get(hash);
        if (!session) {
          session = await ensureIosHlsSession(targetUrl);
        }
        session.lastAccess = Date.now();
        const segPath = path.join(session.dir, file);

        // Wait briefly if segment is currently being finalized by ffmpeg
        const waitStart = Date.now();
        while (!fs.existsSync(segPath) && Date.now() - waitStart < 3500) {
          await new Promise((r) => setTimeout(r, 50));
        }

        if (!fs.existsSync(segPath)) {
          res.status(404).send('Segment not ready');
          return;
        }

        res.setHeader('Content-Type', 'video/mp2t');
        res.setHeader('Cache-Control', 'public, max-age=600');
        fs.createReadStream(segPath).pipe(res);
        return;
      }

      res.status(404).send('Not found');
    } catch (err) {
      console.error('iOS HLS stream error:', err);
      res.status(502).send('Stream transcode failed');
    }
  });

  // 6c. Embedded MKV Subtitle & Exact Audio-Visual Sync Extractor (/api/subtitles/extract)
  const mkvSubExtractCache = new Map<string, { srt: string; expiresAt: number }>();

  app.get('/api/subtitles/extract', async (req, res) => {
    const streamUrl = String(req.query.url || '').trim();
    const startSec = Math.max(0, Number(req.query.startSec || 0) || 0);
    const windowMode = String(req.query.mode || 'probe').trim(); // 'probe' (fast 6MB header+opening) or 'window' (15-min seek window)

    if (!streamUrl || !streamUrl.startsWith('http')) {
      res.json({ ok: false, srt: '' });
      return;
    }

    const cacheKey = `${streamUrl}::${windowMode}::${Math.floor(startSec / 300)}`;
    const cached = mkvSubExtractCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json({ ok: true, srt: cached.srt, cached: true });
      return;
    }

    try {
      let extractedSrt = '';

      if (windowMode === 'window' && startSec > 0) {
        // Seek directly over HTTP to startSec and demux 12 minutes of embedded subtitle packets (-vn -an = zero video/audio decode overhead)
        extractedSrt = await new Promise<string>((resolve) => {
          const chunks: Buffer[] = [];
          const ff = spawn(FFMPEG_BIN, [
            '-hide_banner',
            '-loglevel',
            'error',
            '-ss',
            String(startSec),
            '-t',
            '720',
            '-i',
            streamUrl,
            '-vn',
            '-an',
            '-map',
            '0:s:0?',
            '-c:s',
            'srt',
            '-f',
            'srt',
            'pipe:1',
          ]);
          const killTimer = setTimeout(() => {
            try {
              ff.kill('SIGKILL');
            } catch {}
            resolve(Buffer.concat(chunks).toString('utf8'));
          }, 5200);

          ff.stdout.on('data', (chunk: Buffer) => chunks.push(chunk));
          ff.on('close', () => {
            clearTimeout(killTimer);
            resolve(Buffer.concat(chunks).toString('utf8'));
          });
          ff.on('error', () => {
            clearTimeout(killTimer);
            resolve('');
          });
        });
      } else {
        // Fast 5.5MB Range probe from byte 0: downloads in ~350ms and gives exact opening embedded subtitle cues for auto-sync!
        const controller = new AbortController();
        const fetchTimer = setTimeout(() => controller.abort(), 4200);
        const upstream = await fetch(streamUrl, {
          signal: controller.signal,
          headers: {
            Range: 'bytes=0-5767167',
            'User-Agent': 'Mozilla/5.0',
          },
        }).finally(() => clearTimeout(fetchTimer));

        if (upstream.ok && upstream.body) {
          const arrayBuf = await upstream.arrayBuffer();
          const inputBuf = Buffer.from(arrayBuf);
          extractedSrt = await new Promise<string>((resolve) => {
            const outChunks: Buffer[] = [];
            const ff = spawn(FFMPEG_BIN, [
              '-hide_banner',
              '-loglevel',
              'error',
              '-i',
              'pipe:0',
              '-vn',
              '-an',
              '-map',
              '0:s:0?',
              '-c:s',
              'srt',
              '-f',
              'srt',
              'pipe:1',
            ]);
            const killTimer = setTimeout(() => {
              try {
                ff.kill('SIGKILL');
              } catch {}
              resolve(Buffer.concat(outChunks).toString('utf8'));
            }, 2500);

            ff.stdout.on('data', (chunk: Buffer) => outChunks.push(chunk));
            ff.stdin.on('error', () => {});
            ff.on('close', () => {
              clearTimeout(killTimer);
              resolve(Buffer.concat(outChunks).toString('utf8'));
            });
            ff.on('error', () => {
              clearTimeout(killTimer);
              resolve('');
            });

            ff.stdin.end(inputBuf);
          });
        }
      }

      if (extractedSrt && extractedSrt.includes('-->')) {
        pruneCacheMap(mkvSubExtractCache, 80);
        mkvSubExtractCache.set(cacheKey, {
          srt: extractedSrt,
          expiresAt: Date.now() + 30 * 60_000,
        });
        res.json({ ok: true, srt: extractedSrt });
        return;
      }
    } catch {
      // ignore probe failure
    }

    res.json({ ok: false, srt: '' });
  });

  // 7. User Movie Requests & Broken Link Reports API
  app.get('/api/requests', (_req, res) => {
    res.json({ ok: true, requests: movieRequestsStore });
  });

  app.post('/api/requests', (req, res) => {
    const title = sanitizeBrandText(String(req.body?.title || '').trim());
    const type = String(req.body?.type || 'MOVIE').toUpperCase() as UserMovieRequest['type'];
    const language = sanitizeBrandText(String(req.body?.language || 'Bangla / Dual Audio').trim());
    const notes = sanitizeBrandText(String(req.body?.notes || '').trim());

    if (!title) {
      res.status(400).json({ ok: false, error: 'অনুগ্রহ করে মুভি বা সিরিজের নাম লিখুন' });
      return;
    }

    const item: UserMovieRequest = {
      id: `req-${Date.now()}`,
      title,
      type: ['MOVIE', 'SERIES', 'ANIME', 'BROKEN_LINK'].includes(type) ? type : 'MOVIE',
      language,
      notes,
      status: 'Queued',
      createdAt: Date.now(),
    };
    movieRequestsStore.unshift(item);
    if (movieRequestsStore.length > 30) movieRequestsStore.pop();

    res.json({ ok: true, request: item, requests: movieRequestsStore });
  });

  // 7a. MyFlixBD Cloud HLS Stream, TMDB Cast & Screenshot Enrichment API
  const myflixCache = new Map<string, { data: any; expiresAt: number }>();
  app.get('/api/myflix', async (req, res) => {
    const rawTitle = String(req.query.title || '').trim();
    const cleanQuery = rawTitle
      .replace(/\[.*?\]|\(.*?\)/g, ' ')
      .replace(/\b(?:20\d{2}|19\d{2}|S\d+|Season\s*\d+|Ep(?:isode)?\s*\d+|Complete|WEB-?DL|WEBRip|BluRay|HDTC|1080p|720p|480p|Dual\s*Audio|Multi\s*Audio|Hindi|Bangla|Bengali|English|Dubbed)\b/gi, ' ')
      .replace(/\s{2,}/g, ' ')
      .trim();

    if (!cleanQuery || cleanQuery.length < 2) {
      res.json({ ok: false });
      return;
    }

    const cacheKey = cleanQuery.toLowerCase();
    const cached = myflixCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json({ ok: true, ...cached.data });
      return;
    }

    try {
      const baseTitle = extractBaseSeriesTitle(rawTitle);
      const shortWords = baseTitle.split(/\s+/).filter(Boolean).slice(0, 3).join(' ');
      const queriesToTry = Array.from(new Set([cleanQuery, baseTitle, shortWords].filter((q) => q.length >= 2)));

      let matchedUrl = '';
      const norm = (s: string) => extractBaseSeriesTitle(s).toLowerCase().replace(/[^a-z0-9]+/g, '');
      const targetNorm = norm(rawTitle) || cleanQuery.toLowerCase().replace(/[^a-z0-9]+/g, '');

      for (const q of queriesToTry) {
        const searchUrl = `https://myflixbd.to/wp-json/wp/v2/search?search=${encodeURIComponent(q)}&per_page=6`;
        const sRes = await fetch(searchUrl, {
          headers: {
            'User-Agent':
              'Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36',
          },
          signal: AbortSignal.timeout(4000),
        }).catch(() => null);
        if (!sRes || !sRes.ok) continue;
        const results = (await sRes.json().catch(() => [])) as Array<{ title?: string; url?: string }>;
        if (!Array.isArray(results) || results.length === 0) continue;

        const exactOrClose = results.find((r) => {
          const rNorm = norm(String(r.title || ''));
          return (
            rNorm &&
            targetNorm &&
            (rNorm === targetNorm ||
              (rNorm.length >= 4 && targetNorm.includes(rNorm)) ||
              (targetNorm.length >= 4 && rNorm.includes(targetNorm)))
          );
        });
        if (exactOrClose?.url) {
          matchedUrl = exactOrClose.url;
          break;
        }
      }

      if (!matchedUrl) {
        res.json({ ok: false });
        return;
      }

      const pageRes = await fetch(matchedUrl, {
        headers: {
          'User-Agent':
            'Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36',
        },
        signal: AbortSignal.timeout(5500),
      });
      if (!pageRes.ok) {
        res.json({ ok: false });
        return;
      }
      const html = await pageRes.text();

      const embedServers: Array<{ label: string; url: string }> = [];
      const seenUrls = new Set<string>();
      for (const m of html.matchAll(/data-url=["'](https?:\/\/[^"']+)["']/gi)) {
        const u = m[1].trim();
        if (u && !seenUrls.has(u)) {
          seenUrls.add(u);
          embedServers.push({ label: `MyFlix Server ${embedServers.length + 1}`, url: u });
        }
      }
      for (const m of html.matchAll(/(?:data-litespeed-src|src)=["'](https?:\/\/(?:player\.|abysscdn\.com|abyssplayer\.com)[^"']+)["']/gi)) {
        const u = m[1].trim();
        if (u && !seenUrls.has(u)) {
          seenUrls.add(u);
          embedServers.push({ label: `MyFlix Server ${embedServers.length + 1}`, url: u });
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

      const extractMeta = (label: string) => {
        const re = new RegExp(
          `<span[^>]*class=["']meta-label["'][^>]*>\\s*${label}\\s*<\\/span>\\s*<span[^>]*class=["']meta-value[^"']*["'][^>]*>([\\s\\S]*?)<\\/span>`,
          'i'
        );
        const m = html.match(re);
        return m ? decodeHtmlEntities(m[1]) : '';
      };

      const year = extractMeta('Year');
      const genre = extractMeta('Genre');
      const runtime = extractMeta('Runtime');
      const director = extractMeta('Director');
      const release = extractMeta('Release');
      const ratingMatch = html.match(/class=["']rating-score["'][^>]*>([\d.]+)<\/span>/i);
      const rating = ratingMatch ? ratingMatch[1].trim() : '';

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

      const payload = {
        embedServers,
        seasonsData,
        year,
        genre,
        runtime,
        director,
        release,
        rating,
        screenshots,
        cast,
        downloads,
      };
      pruneCacheMap(myflixCache, 100);
      myflixCache.set(cacheKey, { data: payload, expiresAt: Date.now() + 30 * 60_000 });
      res.json({ ok: true, ...payload });
    } catch {
      res.json({ ok: false });
    }
  });

  // 7b. Global Live Notifications API (New Movie Uploads + Popular High-Rating Movies Broadcast for Everyone)
  app.get('/api/notifications', (_req, res) => {
    const notifications = buildGlobalNotifications();
    res.json({
      ok: true,
      serverTime: Date.now(),
      notifications,
    });
  });

  app.post('/api/notifications/broadcast', (req, res) => {
    const rawMovie = req.body?.movie as MovieCardItem | undefined;
    const category =
      req.body?.category === 'TOP_RATED_POPULAR' ? 'TOP_RATED_POPULAR' : 'NEW_UPLOAD';

    if (!rawMovie || !rawMovie.title || !rawMovie.path) {
      res.status(400).json({ ok: false, error: 'Invalid movie payload for broadcast' });
      return;
    }

    const normMovie = normalizeMovieCardItem(rawMovie, Date.now());
    const ratingNum = parseFloat(normMovie.rating || '9.2') || 9.2;
    const broadcastItem: GlobalMovieNotification = {
      id: `notif-live-${Date.now()}-${normMovie.id}`,
      category,
      badgeText:
        category === 'TOP_RATED_POPULAR'
          ? `জনপ্রিয় ধামাকা • ★ ${ratingNum.toFixed(1)}`
          : 'মাত্র আপলোড হলো 🔥',
      headlineBn:
        category === 'TOP_RATED_POPULAR'
          ? `সবার জন্য হাই-রেটিং জনপ্রিয় মুভি অ্যালার্ট: ${normMovie.title}`
          : `নতুন মুভি আপলোড অ্যালার্ট (সবার জন্য): ${normMovie.title}`,
      subtitleBn: `${normMovie.language || 'Multi Audio'} • ${normMovie.quality || '1080p Full HD'} • রেটিং ★ ${ratingNum.toFixed(1)}`,
      movie: normMovie,
      createdAt: Date.now(),
      ratingScore: ratingNum,
    };

    customBroadcastNotifications.unshift(broadcastItem);
    if (customBroadcastNotifications.length > 12) {
      customBroadcastNotifications.pop();
    }

    res.json({
      ok: true,
      broadcast: broadcastItem,
      notifications: buildGlobalNotifications(),
    });
  });

  // 8. Ultra-Stealth White-Label Proxy Mode (Hides all upstream logos, links, sidebars & intro sounds)
  app.get('/api/proxy-page', async (req, res) => {
    const rawPath = String(req.query.path || '/').trim();
    const nodeId = String(req.query.node || '').trim();

    try {
      const { html, finalOrigin } = await fetchFromMirrors(rawPath, nodeId);
      let processed = html;

      // Remove iOS redirect & ad scripts
      processed = processed
        .replace(/<script>\(function\(\)\{try\{var ua=navigator\.userAgent[\s\S]*?<\/script>/i, '')
        .replace(/<script[^>]*id=["']mlbd-display-ads[^"']*["'][^>]*>[\s\S]*?<\/script>/gi, '')
        .replace(/<script[^>]*id=["']mlbd-click-ads[^"']*["'][^>]*>[\s\S]*?<\/script>/gi, '')
        .replace(/\/mlbd-adopen\.php/g, '/api/noop')
        .replace(/MovieLinkBD/gi, 'CinePulse HD')
        .replace(/movielinkbd\.[a-z]+/gi, 'CinePulse');

      const stealthBridge = `
        <base href="${finalOrigin}/" />
        <style>
          #mlbd-adfree, .mlbd-ad-slot, [data-mlbd-ad], #mlbd-install,
          header .logo, .site-logo, .telegram-join, .tg-banner, .social-links,
          a[href*="t.me"], a[href*="telegram"], .footer, footer {
            display: none !important;
          }
        </style>
        <script>
          // Mute any automatic intro sound or page audio synth
          try {
            window.Audio = function() {
              return { play: function(){ return Promise.resolve(); }, pause: function(){}, addEventListener: function(){} };
            };
            if (window.speechSynthesis) {
              window.speechSynthesis.speak = function() {};
            }
          } catch (_) {}

          document.addEventListener('click', function(e) {
            var a = e.target && e.target.closest ? e.target.closest('a[href]') : null;
            if (!a) return;
            var href = a.getAttribute('href') || '';
            if (!href || href.startsWith('#') || href.startsWith('javascript:')) return;
            try {
              var u = new URL(href, '${finalOrigin}');
              if (u.hostname.includes('movielinkbd')) {
                e.preventDefault();
                e.stopPropagation();
                window.location.href = '/api/proxy-page?path=' + encodeURIComponent(u.pathname + u.search);
              }
            } catch (_) {}
          }, true);
        </script>
      `;

      processed = processed.replace(/<head[^>]*>/i, (match) => `${match}${stealthBridge}`);

      res.setHeader('Content-Type', 'text/html; charset=utf-8');
      res.send(processed);
    } catch {
      res.status(502).send(`
        <!doctype html>
        <html>
          <body style="background:#090b10;color:#f1f5f9;font-family:sans-serif;padding:2rem;text-align:center;">
            <h3>সার্ভারের সাথে সংযোগ করা যাচ্ছে না</h3>
            <p>অনুগ্রহ করে অ্যাপের মেইন ভিউ ব্যবহার করুন অথবা অন্য Server Node নির্বাচন করুন।</p>
          </body>
        </html>
      `);
    }
  });

  app.get('/api/health', (_req, res) => {
    res.status(200).json({
      ok: true,
      service: 'CinePulse HD',
      uptimeSeconds: Math.round(process.uptime()),
      timestamp: Date.now(),
    });
  });

  app.all('/api/noop', (_req, res) => {
    res.status(204).end();
  });

  // Never serve expired static db-shards (HTTP 410 Gone URLs) — force clients to use live /api/details
  app.get('/db-shards/:file', (_req, res) => {
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate');
    res.json({ details: {} });
  });

  // Self-healing Service Worker endpoint: immediately wipes any stale Workbox precaches on Render and reloads clients
  app.get(['/sw.js', '/dev-sw.js'], (_req, res) => {
    res.setHeader('Content-Type', 'application/javascript; charset=utf-8');
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
    res.send(`
      self.addEventListener('install', () => {
        self.skipWaiting();
      });
      self.addEventListener('activate', (event) => {
        event.waitUntil(
          (async () => {
            try {
              const keys = await caches.keys();
              await Promise.all(keys.map((k) => caches.delete(k)));
            } catch (_) {}
            try {
              await self.registration.unregister();
            } catch (_) {}
            try {
              await self.clients.claim();
              const windowClients = await self.clients.matchAll({ type: 'window' });
              for (const client of windowClients) {
                client.navigate(client.url);
              }
            } catch (_) {}
          })()
        );
      });
    `);
  });

  if (process.env.NODE_ENV !== 'production') {
    const vite = await createViteServer({
      server: { middlewareMode: true, hmr: false },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(__dirname, 'dist');
    app.use(
      express.static(distPath, {
        setHeaders: (res, filePath) => {
          if (
            filePath.endsWith('.html') ||
            filePath.endsWith('.json') ||
            filePath.endsWith('.webmanifest') ||
            filePath.endsWith('sw.js') ||
            filePath.endsWith('registerSW.js')
          ) {
            res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
          } else {
            res.setHeader('Cache-Control', 'public, max-age=31536000, immutable');
          }
        },
      })
    );
    app.get('*', (_req, res) => {
      res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
      res.sendFile(path.join(distPath, 'index.html'));
    });
  }

  app.listen(PORT, '0.0.0.0', () => {
    console.log(`CinePulse HD Cinema Server running on http://0.0.0.0:${PORT}`);

    // Defer background category warmup by 15s so initial server boot & container pre-warming are instantaneous
    setTimeout(syncLiveCategories, 15_000).unref();
    setInterval(syncLiveCategories, 180_000).unref();

    // Automatic Render Free-Tier Keep-Alive Self-Ping (prevents 15-min idle sleep)
    const externalUrl = (process.env.RENDER_EXTERNAL_URL || process.env.APP_URL || '').replace(/\/+$/, '');
    if (externalUrl && externalUrl.startsWith('http')) {
      setInterval(() => {
        fetch(`${externalUrl}/api/health`, {
          headers: { 'User-Agent': 'CinePulse-KeepAlive/1.0' },
          signal: AbortSignal.timeout(8000),
        }).catch(() => {});
      }, 10 * 60 * 1000).unref();
    }
  });
}

startServer();

