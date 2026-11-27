// png-squeeze-01: lossless PNG re-encoder.
//
// One program answers 8 screenshots (1280x720 RGBA) as the smallest valid PNGs
// it can, inside one deterministic 60 s budget. Method (three-stage tournament):
//   1. Decode the input PNG to RGBA with a small own decoder (native inflate).
//      The decoder tolerates ancillary input chunks; the encoder only ever
//      emits IHDR/PLTE/tRNS/IDAT/IEND.
//   2. Analyse the image (opaque? grey? distinct colours?) and generate every
//      economically sensible representation as a candidate: palette (type 3) in
//      three orderings (frequency, luminance, spatial adjacency; non-opaque
//      entries first so tRNS stays short), plus the direct-colour form (grey /
//      grey+alpha, RGB (+ tRNS key) or RGBA) even for palette-eligible images.
//      A palette is only used at 256 colours or fewer; a tRNS key only when
//      every alpha is 0 or 255, all transparent pixels share one colour, and no
//      opaque pixel uses that colour. Invisible pixels keep their RGB.
//   3. For each representation, build eight filtered streams: the five fixed
//      PNG filters, plus three per-row adaptive choices (minimum sum of
//      absolute signed residuals, lowest byte entropy, fewest distinct byte
//      bigrams). Identical streams are de-duplicated; identical forms too.
//   4. Screen every stream with zlib level 3, re-screen the best few at
//      level 6, then try several zlib level-8/9 configurations (plus RLE on
//      the best stream) and keep the smallest complete PNG seen at any stage.
//      The finished PNG is decoded again and compared byte for byte with the
//      source; on any failure a fixed-Paeth baseline encoder answers instead.
// All budgets are counts, never wall-clock time, so two runs write identical
// bytes. No network, no files outside /input, /output and /bot, no clock reads.
//
// Written fresh in session for png-squeeze-01-run-20261127 by Muse (the fish),
// from the competition rules and GPT-6.2 design guidance (advisor only);
// reviewed once by GPT-6.2 and fixed per that review (see gpt-review file).

import { deflateSync, inflateSync, constants } from 'node:zlib';
import { copyFileSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// ---------------------------------------------------------------- tuning ---
const SCREEN_LEVEL = 3;          // fast screening compression (stage 1)
const SCREEN2_LEVEL = 6;         // accurate re-screening (stage 2)
const SHORTLIST1 = 8;            // streams kept per image after stage 1
const SHORTLIST = 4;             // streams kept per image after stage 2
const INTENSIVE = [              // zlib configs tried on the shortlist
  { level: 9, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY },
  { level: 9, memLevel: 9, strategy: constants.Z_DEFAULT_STRATEGY },
  { level: 9, memLevel: 8, strategy: constants.Z_FILTERED },
  { level: 9, memLevel: 9, strategy: constants.Z_FILTERED },
];
const RLE_CONFIG = { level: 9, memLevel: 8, strategy: constants.Z_RLE };
// ---------------------------------------------------------------- CRC-32 ---
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  new DataView(d.buffer).setUint32(0, width);
  new DataView(d.buffer).setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ------------------------------------------------------------- PNG decode --
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
// Decode a bit-depth-8 non-interlaced PNG of colour type 0/2/3/4/6 to RGBA.
// Input rules are deliberately looser than the output allowlist: unknown
// ancillary chunks are skipped, unknown critical chunks are rejected.
const ALLOWED_CHUNKS = ['IHDR', 'PLTE', 'tRNS', 'IDAT', 'IEND'];
function decodePng(bytes) {
  const sig = [137, 80, 78, 71, 13, 10, 26, 10];
  if (bytes.length < 8) throw new Error('file too short');
  for (let i = 0; i < 8; i++) if (bytes[i] !== sig[i]) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let idatDone = false;
  let ended = false;
  let first = true;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('chunk header cut short');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk claims bytes the file does not hold');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (!/^[A-Za-z]{4}$/.test(type)) throw new Error('chunk type is not four letters');
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(`${type} CRC`);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (first && type !== 'IHDR') throw new Error('first chunk is not IHDR');
    first = false;
    if (type !== 'IDAT' && idat.length > 0) idatDone = true;
    if (type === 'IHDR') {
      if (header !== null) throw new Error('IHDR twice');
      if (len !== 13) throw new Error('IHDR is not 13 bytes');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], compression: data[10], filter: data[11], interlace: data[12] };
      if (header.width === 0 || header.height === 0) throw new Error('zero dimension');
      if (header.depth !== 8) throw new Error('bit depth is not 8');
      if (!Object.hasOwn(CHANNELS, header.colourType)) throw new Error('unsupported colour type');
      if (header.compression !== 0 || header.filter !== 0) throw new Error('compression or filter method is not 0');
      if (header.interlace !== 0) throw new Error('interlaced');
    } else if (type === 'PLTE') {
      if (palette !== null) throw new Error('PLTE twice');
      if (header.colourType !== 3) throw new Error('PLTE with a non-palette colour type');
      if (idat.length > 0) throw new Error('PLTE follows IDAT');
      if (len === 0 || len % 3 !== 0 || len > 768) throw new Error('PLTE is not 1 to 256 entries');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) throw new Error('tRNS twice');
      if (idat.length > 0) throw new Error('tRNS follows IDAT');
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null) throw new Error('tRNS comes before PLTE');
        if (len > palette.length / 3) throw new Error('tRNS holds more entries than the palette');
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) throw new Error('tRNS has the wrong length for its colour type');
        for (let i = 0; i < len; i += 2) if (data[i] !== 0) throw new Error('tRNS names a sample over 255');
      } else throw new Error('tRNS with colour type 4 or 6');
      trns = data;
    } else if (type === 'IDAT') {
      if (idatDone) throw new Error('IDAT chunks are not in a row');
      if (header.colourType === 3 && palette === null) throw new Error('IDAT comes before PLTE');
      idat.push(data);
    } else if (type === 'IEND') {
      if (len !== 0) throw new Error('IEND is not empty');
      ended = true;
    } else if (!ALLOWED_CHUNKS.includes(type)) {
      // Unknown chunk: skip it when ancillary (lowercase first letter),
      // reject it when critical.
      if ((type.charCodeAt(0) & 32) === 0) throw new Error(`unknown critical chunk ${type}`);
    }
  }
  if (!header) throw new Error('no IHDR');
  if (!ended) throw new Error('no IEND');
  if (idat.length === 0) throw new Error('no IDAT');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected });
  if (raw.length !== expected) throw new Error('IDAT length mismatch');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    else if (ft === 2) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    else if (ft === 3) for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    else if (ft === 4) for (let i = 0; i < stride; i++) {
      const a = i >= bpp ? samples[o + i - bpp] : 0;
      const b = y > 0 ? samples[p + i] : 0;
      const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
      samples[o + i] = raw[src + i] + paeth(a, b, c);
    } else throw new Error(`filter ${ft}`);
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error('palette index out of range');
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// --------------------------------------------------------------- analysis --
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.entries()].map(([word, count]) => {
      const b = new Uint8Array(Uint32Array.of(word).buffer);
      return { word, count, r: b[0], g: b[1], b: b[2], a: b[3] };
    });
  }
  return { opaque, grey, colours };
}
// The one fully transparent value the image may key by tRNS (type 0/2):
// every alpha 0 or 255, one transparent value, no opaque pixel of that value.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

// ------------------------------------------------------- palette ordering --
const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
// Greedy spatial-adjacency ordering: colours that sit next to each other in
// the image get nearby palette indices, so Sub/Paeth residuals stay small.
function spatialOrder(rgba, width, height, colours, indexOf) {
  const k = colours.length;
  if (k === 0) return [];
  if (k === 1) return [0];
  const w = new Int32Array(k * k);
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, rgba.length >>> 2);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = y * width + x;
      const a = indexOf.get(u32[i]);
      if (a === undefined) continue;
      if (x + 1 < width) {
        const b = indexOf.get(u32[i + 1]);
        if (b !== undefined && a !== b) { w[a * k + b]++; w[b * k + a]++; }
      }
      if (y + 1 < height) {
        const b = indexOf.get(u32[i + width]);
        if (b !== undefined && a !== b) { w[a * k + b]++; w[b * k + a]++; }
      }
    }
  }
  const placed = new Uint8Array(k);
  const score = new Float64Array(k);
  const order = [];
  let first = 0;
  for (let i = 1; i < k; i++) if (colours[i].count > colours[first].count || (colours[i].count === colours[first].count && colours[i].word < colours[first].word)) first = i;
  order.push(first);
  placed[first] = 1;
  for (let i = 0; i < k; i++) score[i] = w[first * k + i];
  for (let step = 1; step < k; step++) {
    let best = -1;
    for (let i = 0; i < k; i++) {
      if (placed[i]) continue;
      if (best === -1 || score[i] > score[best] || (score[i] === score[best] && (colours[i].count > colours[best].count || (colours[i].count === colours[best].count && colours[i].word < colours[best].word)))) best = i;
    }
    order.push(best);
    placed[best] = 1;
    for (let i = 0; i < k; i++) if (!placed[i]) score[i] += w[best * k + i];
  }
  return order;
}
function paletteForm(rgba, width, height, colours, mode) {
  // Non-opaque entries first (short tRNS), ordered by the mode's policy
  // within their group, just like the opaque entries.
  const nonOpaque = colours.filter((c) => c.a !== 255);
  const opaque = colours.filter((c) => c.a === 255);
  const byWord = (a, b) => a.word - b.word;
  const byCount = (a, b) => b.count - a.count || byWord(a, b);
  const byLum = (a, b) => lum(a) - lum(b) || byWord(a, b);
  let orderedNonOpaque;
  let orderedOpaque;
  if (mode === 'count') {
    orderedNonOpaque = [...nonOpaque].sort(byCount);
    orderedOpaque = [...opaque].sort(byCount);
  } else if (mode === 'luminance') {
    orderedNonOpaque = [...nonOpaque].sort(byLum);
    orderedOpaque = [...opaque].sort(byLum);
  } else {
    // Spatial: order the opaque entries by adjacency; keep the non-opaque
    // entries first, sorted by alpha then frequency (their count is small and
    // their spatial pattern is dominated by the transparent region's shape).
    orderedNonOpaque = [...nonOpaque].sort((a, b) => a.a - b.a || byCount(a, b));
    if (opaque.length < 2) orderedOpaque = [...opaque].sort(byCount);
    else {
      const indexOf = new Map(opaque.map((c, i) => [c.word, i]));
      orderedOpaque = spatialOrder(rgba, width, height, opaque, indexOf).map((i) => opaque[i]);
    }
  }
  const entries = [...nonOpaque, ...orderedOpaque];
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r; plte[i * 3 + 1] = c.g; plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const u32 = new Uint32Array(rgba.buffer, rgba.byteOffset, n);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { colourType: 3, bpp: 1, samples: indices, plte, trns, name: `pal-${mode}` };
}
function formsOf(rgba, width, height) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const mode of ['count', 'luminance', 'spatial']) forms.push(paletteForm(rgba, width, height, colours, mode));
  }
  // The direct-colour form is always a candidate too, even for palette
  // eligible images: fewer uncompressed bytes do not always mean fewer
  // compressed bytes, and palette metadata can outweigh the IDAT saving.
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  forms.push({ colourType: ct, bpp: { 0: 1, 2: 3, 4: 2, 6: 4 }[ct], samples: samplesOf(rgba, ct), plte: null, trns, name: `ct${ct}` });
  // Drop identical forms (same colour type, palette, tRNS and samples):
  // two orderings can produce the same palette, and filtering and
  // compressing it twice buys nothing.
  const seen = [];
  return forms.filter((f) => {
    for (const g of seen) {
      if (g.colourType !== f.colourType) continue;
      const sameBytes = (a, b) => (a === null && b === null) || (a !== null && b !== null && a.length === b.length && Buffer.from(a).equals(Buffer.from(b)));
      if (sameBytes(g.plte, f.plte) && sameBytes(g.trns, f.trns) && g.samples.length === f.samples.length && Buffer.from(g.samples).equals(Buffer.from(f.samples))) return false;
    }
    seen.push(f);
    return true;
  });
}

// ---------------------------------------------------------------- filters --
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  else if (type === 2) for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  else if (type === 3) for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  else for (let i = 0; i < n; i++) {
    const a = i >= bpp ? cur[i - bpp] : 0;
    const b = prev === null ? 0 : prev[i];
    const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
    out[i] = cur[i] - paeth(a, b, c);
  }
}
// c*log2(c) table for entropy scoring (stride <= 5120 here).
const CLOG = (() => {
  const t = new Float64Array(8192);
  for (let c = 1; c < t.length; c++) t[c] = c * Math.log2(c);
  return t;
})();
const BIGRAM_SEEN = new Int32Array(65536);
let bigramStamp = 0;
// Metrics of one filtered row: [minsum, entropy, distinct bigrams].
const HIST = new Uint32Array(256);
function rowMetrics(row, filterByte) {
  let minsum = 0;
  HIST.fill(0);
  let pairs = 0;
  const stamp = ++bigramStamp;
  let prev = filterByte;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    minsum += v < 128 ? v : 256 - v;
    HIST[v]++;
    const pair = (prev << 8) | v;
    if (BIGRAM_SEEN[pair] !== stamp) { BIGRAM_SEEN[pair] = stamp; pairs++; }
    prev = v;
  }
  const n = row.length;
  let ent = Math.log2(n);
  for (let b = 0; b < 256; b++) if (HIST[b] !== 0) ent -= CLOG[HIST[b]] / n;
  return [minsum, ent, pairs];
}
function fnv(data) {
  let h = 0x811c9dc5;
  for (let i = 0; i < data.length; i++) { h ^= data[i]; h = Math.imul(h, 0x01000193); }
  return h >>> 0;
}
// The eight filtered streams of one form, de-duplicated (fixed 0-4, adaptive
// minsum / entropy / bigrams). Returns [{form, data, overhead}].
function streamsOf(form, width, height) {
  const stride = width * form.bpp;
  const size = height * (stride + 1);
  const streams = [];
  for (let s = 0; s < 8; s++) streams.push(Buffer.alloc(size));
  const trial = [];
  for (let t = 0; t < 5; t++) trial.push(new Uint8Array(stride));
  const overhead = 57 + (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
  for (let y = 0; y < height; y++) {
    const cur = form.samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : form.samples.subarray((y - 1) * stride, y * stride);
    const metrics = [];
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, form.bpp, trial[t]);
      metrics.push(rowMetrics(trial[t], t));
    }
    // Per-metric argmin, lowest filter type on ties.
    const pick = [0, 0, 0];
    for (let m = 0; m < 3; m++) {
      let best = 0;
      for (let t = 1; t < 5; t++) if (metrics[t][m] < metrics[best][m]) best = t;
      pick[m] = best;
    }
    const at = y * (stride + 1);
    for (let s = 0; s < 8; s++) {
      const t = s < 5 ? s : pick[s - 5];
      streams[s][at] = t;
      streams[s].set(trial[t], at + 1);
    }
  }
  const out = [];
  const seen = new Map();
  const names = ['f0', 'f1', 'f2', 'f3', 'f4', 'minsum', 'entropy', 'bigrams'];
  for (let s = 0; s < streams.length; s++) {
    const data = streams[s];
    const h = fnv(data);
    const prev = seen.get(h);
    if (prev !== undefined && prev.length === data.length && prev.equals(data)) continue;
    seen.set(h, data);
    out.push({ form, data, overhead, name: `${form.name}/${names[s]}` });
  }
  return out;
}

// Verify a finished PNG decodes back to exactly this RGBA image.
function verifyPng(png, rgba, width, height) {
  try {
    const back = decodePng(png);
    return back.width === width && back.height === height && Buffer.from(back.rgba).equals(Buffer.from(rgba));
  } catch {
    return false;
  }
}
// The safe fallback encoder: RGBA, every row Paeth-filtered, zlib level 9.
// Simple enough to trust when the tournament itself has failed.
function baselinePng(rgba, width, height) {
  const stride = width * 4;
  const raw = Buffer.alloc(height * (stride + 1));
  const trial = new Uint8Array(stride);
  for (let y = 0; y < height; y++) {
    const cur = rgba.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : rgba.subarray((y - 1) * stride, y * stride);
    filterRow(4, cur, prev, 4, trial);
    raw[y * (stride + 1)] = 4;
    raw.set(trial, y * (stride + 1) + 1);
  }
  const zlib = deflateSync(raw, { level: 9, memLevel: 8 });
  const png = pngOf([['IHDR', ihdrOf(width, height, 6)], ['IDAT', zlib], ['IEND', new Uint8Array(0)]]);
  if (!verifyPng(png, rgba, width, height)) throw new Error('baseline verification failed');
  return png;
}
const formOverhead = (form) => 57 + (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// ------------------------------------------------------------- one image ---
function encodeImage(rgba, width, height) {
  const forms = formsOf(rgba, width, height);
  // The best complete PNG seen at any stage, whatever produced it: a
  // level-3 result can beat every later result, so nothing is thrown away.
  let best = null;
  const consider = (form, z) => {
    const total = formOverhead(form) + z.length;
    if (best === null || total < best.total) best = { form, zlib: z, total };
  };
  const shortlist = [];
  for (const form of forms) {
    for (const cand of streamsOf(form, width, height)) {
      const z = deflateSync(cand.data, { level: SCREEN_LEVEL, memLevel: 8 });
      consider(cand.form, z);
      shortlist.push({ form: cand.form, data: cand.data, screen: z.length + cand.overhead, name: cand.name });
    }
  }
  shortlist.sort((a, b) => a.screen - b.screen);
  // Stage 2: re-screen the survivors at level 6, the level the scale
  // compressor ranks by; level 3 alone mis-ranks streams whose patterns need
  // a deeper match search. Each stage-2 result is a candidate in its own right.
  const survivors = shortlist.slice(0, SHORTLIST1);
  for (const cand of survivors) {
    const z = deflateSync(cand.data, { level: SCREEN2_LEVEL, memLevel: 8 });
    consider(cand.form, z);
    cand.screen = z.length + formOverhead(cand.form);
  }
  survivors.sort((a, b) => a.screen - b.screen);
  const kept = survivors.slice(0, SHORTLIST);
  for (const cand of kept) {
    for (const cfg of INTENSIVE) consider(cand.form, deflateSync(cand.data, cfg));
  }
  // RLE is cheap to test and occasionally wins on long repeated residuals
  // (identical rows under Up, flat areas under Sub); try it on the best stream.
  if (kept.length > 0) consider(kept[0].form, deflateSync(kept[0].data, RLE_CONFIG));
  const chunks = [['IHDR', ihdrOf(width, height, best.form.colourType)]];
  if (best.form.plte !== null) chunks.push(['PLTE', best.form.plte]);
  if (best.form.trns !== null) chunks.push(['tRNS', best.form.trns]);
  chunks.push(['IDAT', best.zlib]);
  chunks.push(['IEND', new Uint8Array(0)]);
  const png = pngOf(chunks);
  if (!verifyPng(png, rgba, width, height)) throw new Error('output verification failed');
  return png;
}

// ------------------------------------------------------------------- main --
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const inPath = join(I, id, 'image.png');
  const outDir = join(O, id);
  const outPath = join(outDir, 'image.png');
  try {
    mkdirSync(outDir, { recursive: true });
    const image = decodePng(new Uint8Array(readFileSync(inPath)));
    let png;
    try {
      png = encodeImage(image.rgba, image.width, image.height);
    } catch (err) {
      console.error(`png-squeeze: ${id} tournament failed (${err.message}); using baseline encoder`);
      png = baselinePng(image.rgba, image.width, image.height);
    }
    writeFileSync(outPath, png);
  } catch (err) {
    // Last resort: the input file itself is a valid stored PNG of the image.
    console.error(`png-squeeze: ${id} failed (${err.message}); copying input`);
    try {
      mkdirSync(outDir, { recursive: true });
      copyFileSync(inPath, outPath);
    } catch {
      // Nothing more can be done for this instance.
    }
  }
}
