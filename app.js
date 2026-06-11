/* UK & Ireland Railway Map — accessible static viewer (session 4).
   Plain JS, no dependencies, no build step. Boots from ./overview.json;
   full detail streams in as static world-grid tiles (./tiles/0/X_Y.json)
   exactly like the classic viewer's bundle format.

   Design notes
   ------------
   * Rendering: canvas 2D, devicePixelRatio-aware. Interactive frames draw
     straight segments and REPLAY the last full frame's label list
     (world-anchored record-and-replay — labels never vanish mid-drag);
     a full-quality frame (Catmull-Rom curves + fresh label placement)
     lands ~140 ms after input settles.
   * Culling: every feature class lives in a uniform spatial grid keyed by
     world bbox; only grid hits are considered per frame.
   * Label placement: occupancy grid (soft) + station-footprint interiors
     (hard) — stations always place via a min-overlap last resort, never
     on a footprint polygon (ports the r3 placer).
   * Accessibility: all controls are native elements; the canvas is
     role=application with keyboard pan/zoom; a polite live region
     announces search results, flights and feature selection; search is a
     WAI-ARIA combobox; prefers-reduced-motion disables flights.
   * State: the URL hash mirrors x/y/zoom/layers (debounced replaceState)
     so any view is a shareable deep link. */
(function () {
"use strict";

/* ---------------- DOM ---------------- */
const $ = (id) => document.getElementById(id);
const cv = $("map"), ctx = cv.getContext("2d");
const announce = $("announce");
const REDUCED = matchMedia("(prefers-reduced-motion: reduce)").matches;

/* ---------------- state ---------------- */
let S = null;                 // overview scene
let BM = null;                // bundle manifest
let P = {};                   // palette
let SW = 0, SH = 0, DPR = 1;  // css size, pixel ratio
let k = 0.1, ox = 0, oy = 0;  // world->screen: sx = x*k + ox
let kmin = 0.01, KMAX = 14;
let LQ = false, lqTimer = 0;  // interaction fast-path flag
let raf = 0;
let _unused_sel = null;
let flightId = 0;

const flags = {
  rail_none: 1, rail_dc: 1, rail_ac: 1, ng: 1, metro: 1, constr: 1,
  tunnel: 1, lc: 1, stn: 1, plat: 1, signals: 0,
  former: 1, places: 1, urban: 1, industry: 1, junctions: 1,
};
const FLAGKEYS = Object.keys(flags);
/* Yards CROSSFADE between a shaded footprint and their real tracks (was a
   hard switch at k=2.2). Over k = YARD_K1..YARD_K2 the wash alpha eases
   1->0 while yard-track ink eases 0->1; the dashed survey outline fades in
   with the tracks and persists. shade/tracks modes pin either end. */
let yardMode = "auto";              // auto | shade | tracks | none
const YARD_K1 = 1.8, YARD_K2 = 2.6; // auto crossfade band
const YARD_HATCH_S = 4;             // atlas-hatch spacing, screen px (perp.)
let yShadeNow = true, yTracksNow = false, yOutlineNow = false;
let yWashA = 1, yTrackA = 0;        // band alphas
function yardFrame() {
  const t = Math.min(1, Math.max(0, (k - YARD_K1) / (YARD_K2 - YARD_K1)));
  const s = t * t * (3 - 2 * t);    // smoothstep
  yWashA = yardMode === "shade" ? 1 : yardMode === "auto" ? 1 - s : 0;
  yTrackA = yardMode === "tracks" ? 1 : yardMode === "auto" ? s : 0;
  yShadeNow = yWashA > 0.004;
  yTracksNow = yTrackA > 0.004;
  yOutlineNow = yardMode === "auto" && yTrackA > 0.004;  // outline + name persist
}

const sx = (x) => x * k + ox, sy = (y) => y * k + oy;
const wx = (x) => (x - ox) / k, wy = (y) => (y - oy) / k;

/* ---------------- tiny spatial grid ---------------- */
function Grid(cell) {
  const m = new Map(), c = cell || 220;
  return {
    add(bb, i) {
      for (let gx = (bb[0] / c) | 0; gx <= (bb[2] / c) | 0; gx++)
        for (let gy = (bb[1] / c) | 0; gy <= (bb[3] / c) | 0; gy++) {
          const kk = gx + ":" + gy;
          let a = m.get(kk); if (!a) m.set(kk, a = []);
          a.push(i);
        }
    },
    query(x0, y0, x1, y1, out) {
      out = out || new Set();
      for (let gx = (x0 / c) | 0; gx <= (x1 / c) | 0; gx++)
        for (let gy = (y0 / c) | 0; gy <= (y1 / c) | 0; gy++) {
          const a = m.get(gx + ":" + gy);
          if (a) for (const i of a) out.add(i);
        }
      return out;
    },
  };
}
const bboxOf = (pts) => {
  let x0 = 1e18, y0 = 1e18, x1 = -1e18, y1 = -1e18;
  for (const p of pts) {
    if (p[0] < x0) x0 = p[0]; if (p[0] > x1) x1 = p[0];
    if (p[1] < y0) y0 = p[1]; if (p[1] > y1) y1 = p[1];
  }
  return [x0, y0, x1, y1];
};
const ringsBB = (rings) => {
  const b = bboxOf(rings[0]).slice();
  for (let r = 1; r < rings.length; r++) {
    const q = bboxOf(rings[r]);
    b[0] = Math.min(b[0], q[0]); b[1] = Math.min(b[1], q[1]);
    b[2] = Math.max(b[2], q[2]); b[3] = Math.max(b[3], q[3]);
  }
  return b;
};

/* world-space layer store: overview + merged tile detail */
function Layer() { return { arr: [], g: Grid() }; }
const L = {};   // tracks, water, urban, former, station_polys, yard_polys, sea, sea_land
function rebuildLayer(name, arr, bbOf) {
  const l = L[name] = Layer();
  l.arr = arr;
  arr.forEach((f, i) => { f._bb = f._bb || bbOf(f); l.g.add(f._bb, i); });
}

/* ---------------- tiles ---------------- */
const tileCache = new Map();   // key -> {st:0|1|2, data}
let inflight = 0, FMAX = 6, CACHE_MAX = 60;
let DET = null, BMODE = false, allLoaded = true;
const fq = [];
function newDET() {
  const d = { m: new Map(), cats: {} };
  for (const c of ["tracks", "water", "platforms", "station_polys",
    "yard_polys", "crossings", "signals", "abutments", "portals", "tunnels",
    "bridges_named", "industry", "places", "former", "sea_land",
    "junctions"]) d.cats[c] = [];
  return d;
}
function detAdd(d, td) {
  for (const c in d.cats) {
    const fs = td[c]; if (!fs) continue;
    for (const f of fs) {
      const key = c + ":" + f.id;
      if (d.m.has(key)) continue;
      d.m.set(key, 1); d.cats[c].push(f);
    }
  }
}
function tilesInView(m) {
  if (!BM) return [];
  const T = BM.tile_px, X0 = BM.origin[0], Y0 = BM.origin[1];
  const a = Math.max(0, Math.floor((wx(0) - X0) / T) - m),
        b = Math.max(0, Math.floor((wy(0) - Y0) / T) - m),
        c = Math.min(BM.grid[0] - 1, Math.floor((wx(SW) - X0) / T) + m),
        d = Math.min(BM.grid[1] - 1, Math.floor((wy(SH) - Y0) / T) + m);
  const out = [];
  for (let ty = b; ty <= d; ty++) for (let tx = a; tx <= c; tx++) {
    const kk = tx + "_" + ty;
    if (BM.tiles[kk] !== undefined) out.push(kk);
  }
  return out;
}
function pump() {
  while (inflight < FMAX && fq.length) {
    const kk = fq.shift(), e = tileCache.get(kk);
    if (!e || e.st !== 0 || e.req) continue;
    e.req = 1; inflight++;
    fetch("tiles/0/" + kk + ".json")
      .then((r) => { if (!r.ok) throw 0; return r.json(); })
      .then((d) => { if (tileCache.get(kk) === e) { e.st = 1; e.data = d; detDirty = true; schedule(); } })
      .catch(() => { if (tileCache.get(kk) === e) {
        e.st = 2; e.terr = performance.now(); e.req = 0; } })
      .finally(() => { inflight--; pump(); tileSpin(); });
  }
  tileSpin();
}
let detDirty = false, detLast = 0, detTimer = 0;
function rebuildDET() {
  DET = newDET();
  for (const e of tileCache.values()) if (e.st === 1) detAdd(DET, e.data);
  // detail layers replace overview layers wholesale (classic semantics)
  rebuildLayer("tracks", DET.cats.tracks, (f) => bboxOf(f.pts));
  rebuildLayer("water", DET.cats.water, (f) => bboxOf(f.pts));
  rebuildLayer("former", DET.cats.former, (f) => bboxOf(f.pts));
  rebuildLayer("station_polys", DET.cats.station_polys, (f) => ringsBB(f.rings));
  rebuildLayer("yard_polys", DET.cats.yard_polys, (f) => ringsBB(f.rings));
  rebuildLayer("platforms", DET.cats.platforms,
    (f) => [f.x - f.len - 2, f.y - f.len - 2, f.x + f.len + 2, f.y + f.len + 2]);
  rebuildLayer("sea_land_det", DET.cats.sea_land, (f) => bboxOf(f.pts));
  POINTS.crossings = DET.cats.crossings;
  POINTS.signals = DET.cats.signals;
  POINTS.junctions = DET.cats.junctions;
  POINTS.tunnels = DET.cats.tunnels;
  POINTS.bridges = DET.cats.bridges_named;
  POINTS.industry = DET.cats.industry;
  POINTS.abutments = DET.cats.abutments;
  POINTS.portals = DET.cats.portals;
  PLACES = S.places.concat(DET.cats.places);
}
function useOverview() {
  rebuildLayer("tracks", S.tracks, (f) => bboxOf(f.pts));
  rebuildLayer("water", [], () => [0, 0, 0, 0]);
  rebuildLayer("former", [], () => [0, 0, 0, 0]);
  rebuildLayer("station_polys", [], () => [0, 0, 0, 0]);
  rebuildLayer("yard_polys", [], () => [0, 0, 0, 0]);
  rebuildLayer("platforms", [], () => [0, 0, 0, 0]);
  rebuildLayer("sea_land_det", [], () => [0, 0, 0, 0]);
  POINTS = { crossings: [], signals: [], junctions: [], tunnels: [],
    bridges: [], industry: [], abutments: [], portals: [] };
  PLACES = S.places;
}
let POINTS = {}, PLACES = [], LOVT = null;
function bundleSync() {
  if (!BM) return;
  const want = k >= (BM.k_detail || 0.25);
  if (want) {
    const need = tilesInView(1);
    const now = performance.now();
    allLoaded = true;
    for (const kk of need) {
      let e = tileCache.get(kk);
      if (!e) { tileCache.set(kk, e = { st: 0, req: 0 }); fq.push(kk); }
      else if (e.st === 2 && !e.req && now - (e.terr || 0) > 4000) {
        e.st = 0; fq.push(kk);                            // retry failures
      }
      if (e.st !== 1) allLoaded = false;
      else e.t = now;
    }
    pump();
    if (tileCache.size > CACHE_MAX) {                       // LRU eviction
      const needSet = new Set(need);
      const ev = [...tileCache.entries()]
        .filter(([kk, e]) => e.st === 1 && !needSet.has(kk))
        .sort((a, b) => (a[1].t || 0) - (b[1].t || 0));
      while (tileCache.size > CACHE_MAX && ev.length) {
        tileCache.delete(ev.shift()[0]); detDirty = true;
      }
    }
    if (!BMODE) { BMODE = true; rebuildDET(); detDirty = false; detLast = now; }
    else if (detDirty && (allLoaded || now - detLast > 150)) {
      rebuildDET(); detDirty = false; detLast = now;      // batch arrivals:
    } else if (detDirty && !detTimer) {                   // <=1 rebuild/150ms
      detTimer = setTimeout(() => { detTimer = 0; schedule(); }, 160);
    }
  } else if (BMODE) {
    BMODE = false; useOverview();
  }
  tileSpin();
}
function tileSpin() {
  let el = $("tilespin");
  const pend = [...tileCache.values()].filter((e) => e.st === 0).length + inflight;
  if (pend > 0 && BMODE !== false && k >= (BM ? BM.k_detail : 1)) {
    if (!el) {
      el = document.createElement("div"); el.id = "tilespin";
      el.setAttribute("role", "status");
      $("stage").appendChild(el);
    }
    el.textContent = "loading detail…";
  } else if (el) el.remove();
}

/* ---------------- style helpers ---------------- */
function mix(hex, hex2, t) {
  const a = parseInt(hex.slice(1), 16), b = parseInt(hex2.slice(1), 16);
  const r = ((a >> 16) + (((b >> 16) & 255) - (a >> 16)) * t) | 0,
        g = (((a >> 8) & 255) + (((b >> 8) & 255) - ((a >> 8) & 255)) * t) | 0,
        bl = ((a & 255) + ((b & 255) - (a & 255)) * t) | 0;
  return "rgb(" + r + "," + g + "," + bl + ")";
}
const shadeCache = new Map();
function railInk(el, spd) {
  const base = P["rail_" + (el || "none")] || P.ink || "#2e2a22";
  if (!spd) return base;
  const key = base + ":" + (spd / 15 | 0);
  let v = shadeCache.get(key);
  if (!v) {
    const t = Math.max(0, Math.min(1, (spd - 15) / 95));
    v = t < 0.001 ? mix(base, P.land || "#f1e9d4", 0.14)
      : mix(base, "#000000", 0.10 * t) ;
    if (spd <= 15) v = mix(base, P.land || "#f1e9d4", 0.14);
    else v = mix(base, "#000000", 0.10 * t);
    shadeCache.set(key, v);
  }
  return v;
}
const ORD = { subway: -4, funicular: -3, miniature: -3, tram: -2,
  construction: -1, yard: 0, siding: 1, crossover: 2, branch: 3,
  light_rail: 3, narrow_gauge: 4, diesel: 4, elec: 5, rail: 5, tunnel: 6 };
const WID = { rail: 1.25, elec: 1.25, diesel: 1.25, branch: 1.05,
  tunnel: 1.2, crossover: 0.85, siding: 0.65, yard: 0.55, light_rail: 1.0,
  narrow_gauge: 0.94, subway: 0.8, tram: 0.8, funicular: 0.5,
  miniature: 0.5, construction: 0.9 };
function clsInk(t) {
  const c = t.cls;
  if (c === "rail" || c === "elec" || c === "diesel")
    return railInk(t.el, t.spd);
  if (c === "tunnel") return P.tunnel || "#7d745f";
  return P[c] || P.ink || "#2e2a22";
}
function flagOf(t) {
  const c = t.cls;
  if (c === "rail" || c === "elec" || c === "diesel")
    return flags["rail_" + (t.el || "none")];
  if (c === "subway" || c === "light_rail" || c === "tram") return flags.metro;
  if (c === "narrow_gauge") return flags.ng;
  if (c === "construction") return flags.constr;
  if (c === "tunnel") return flags.tunnel;
  if (c === "yard") return yTracksNow ? 1 : 0;
  return flags[c] === undefined ? 1 : flags[c];
}

/* ---------------- drawing ---------------- */
function pathStraight(pts) {
  ctx.moveTo(sx(pts[0][0]), sy(pts[0][1]));
  for (let i = 1; i < pts.length; i++) ctx.lineTo(sx(pts[i][0]), sy(pts[i][1]));
}
function pathCurve(pts) {                      // Catmull-Rom through points
  const n = pts.length;
  if (n < 3 || LQ) return pathStraight(pts);
  ctx.moveTo(sx(pts[0][0]), sy(pts[0][1]));
  for (let i = 0; i < n - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)], p1 = pts[i], p2 = pts[i + 1],
          p3 = pts[Math.min(n - 1, i + 2)];
    ctx.bezierCurveTo(
      sx(p1[0] + (p2[0] - p0[0]) / 6), sy(p1[1] + (p2[1] - p0[1]) / 6),
      sx(p2[0] - (p3[0] - p1[0]) / 6), sy(p2[1] - (p3[1] - p1[1]) / 6),
      sx(p2[0]), sy(p2[1]));
  }
}
function fillRings(rings) {
  ctx.beginPath();
  for (const ring of rings) {
    ctx.moveTo(sx(ring[0][0]), sy(ring[0][1]));
    for (let q = 1; q < ring.length; q++) ctx.lineTo(sx(ring[q][0]), sy(ring[q][1]));
    ctx.closePath();
  }
}
const visible = (bb) =>
  sx(bb[0]) < SW + 80 && sx(bb[2]) > -80 && sy(bb[1]) < SH + 80 && sy(bb[3]) > -80;

/* label placer (r3 port: soft occupancy + HARD station-poly interiors) */
const CG = 6;
let OCC, HOCC, BOXES;
function markSeg(x0, y0, x1, y1, T) {
  T = T || OCC;
  const n = Math.max(1, Math.ceil(Math.hypot(x1 - x0, y1 - y0) / CG));
  for (let i = 0; i <= n; i++) {
    const t = i / n;
    T.add(((x0 + (x1 - x0) * t) / CG | 0) + "," + ((y0 + (y1 - y0) * t) / CG | 0));
  }
}
function markRings(rings) {
  let yl = 1e18, yh = -1e18;
  for (const ring of rings) for (const q of ring) {
    const Y = sy(q[1]); if (Y < yl) yl = Y; if (Y > yh) yh = Y;
  }
  if (yh < -40 || yl > SH + 40) return;
  for (let gy = Math.floor(Math.max(yl, -40) / CG);
       gy <= Math.floor(Math.min(yh, SH + 40) / CG); gy++) {
    const Y = (gy + 0.5) * CG, xs = [];
    for (const ring of rings) {
      const n = ring.length;
      for (let i = 0; i < n; i++) {
        const y1 = sy(ring[i][1]), y2 = sy(ring[(i + 1) % n][1]);
        if ((y1 <= Y && Y < y2) || (y2 <= Y && Y < y1)) {
          const x1 = sx(ring[i][0]), x2 = sx(ring[(i + 1) % n][0]);
          xs.push(x1 + (Y - y1) / (y2 - y1) * (x2 - x1));
        }
      }
    }
    xs.sort((a, b) => a - b);
    for (let i = 0; i + 1 < xs.length; i += 2)
      for (let gx = Math.floor(xs[i] / CG); gx <= Math.floor(xs[i + 1] / CG); gx++)
        HOCC.add(gx + "," + gy);
  }
  for (const ring of rings) for (let i = 0; i < ring.length; i++) {
    const a = ring[i], b = ring[(i + 1) % ring.length];
    markSeg(sx(a[0]), sy(a[1]), sx(b[0]), sy(b[1]), HOCC);
  }
}
function clearR(x0, y0, x1, y1) {
  if (x1 < 0 || y1 < 0 || x0 > SW || y0 > SH) return false;
  for (let gx = Math.floor(x0 / CG); gx <= Math.floor(x1 / CG); gx++)
    for (let gy = Math.floor(y0 / CG); gy <= Math.floor(y1 / CG); gy++) {
      const kk = gx + "," + gy;
      if (OCC.has(kk) || HOCC.has(kk)) return false;
    }
  return true;
}
function fillBox(x0, y0, x1, y1) {
  BOXES.push([x0, y0, x1, y1]);
  for (let gx = Math.floor(x0 / CG); gx <= Math.floor(x1 / CG); gx++)
    for (let gy = Math.floor(y0 / CG); gy <= Math.floor(y1 / CG); gy++)
      OCC.add(gx + "," + gy);
}
function cands(w, h, dists) {
  const out = [];
  for (const d of dists) out.push(
    [d, -h / 2], [-w - d, -h / 2], [-w / 2, d], [-w / 2, -h - d],
    [d, -h - d], [-w - d, -h - d], [d, d], [-w - d, d]);
  return out;
}
function place(ax, ay, w, h, cc, must) {
  for (const c of cc) {
    const x0 = ax + c[0], y0 = ay + c[1];
    if (clearR(x0, y0, x0 + w, y0 + h)) { fillBox(x0, y0, x0 + w, y0 + h); return [x0, y0]; }
  }
  if (!must) return null;
  let best = null, bc = 1e9;
  for (const c of cc) {
    const x0 = ax + c[0], y0 = ay + c[1], x1 = x0 + w, y1 = y0 + h;
    if (x1 < 0 || y1 < 0 || x0 > SW || y0 > SH) continue;
    let cost = 0, bad = false;
    for (let gx = Math.floor(x0 / CG); gx <= Math.floor(x1 / CG) && !bad; gx++)
      for (let gy = Math.floor(y0 / CG); gy <= Math.floor(y1 / CG); gy++) {
        const kk = gx + "," + gy;
        if (HOCC.has(kk)) { bad = true; break; }
        if (OCC.has(kk)) cost++;
      }
    if (bad) continue;
    if (cost < bc) { bc = cost; best = [x0, y0]; if (!cost) break; }
  }
  if (best) fillBox(best[0], best[1], best[0] + w, best[1] + h);
  return best;
}

/* record-and-replay label cache (obs #58): full frames record world-anchored
   text/leader ops; LQ frames replay them re-projected. */
let LBC = [];
function recText(font, fill, halo, text, wxp, wyp, dx, dy, align) {
  LBC.push([0, font, fill, halo, text, wxp, wyp, dx, dy, align || "left"]);
  drawTextOp(font, fill, halo, text, sx(wxp) + dx, sy(wyp) + dy, align);
}
function recLeader(stroke, w1, wxa, wya, dxa, dya, wxb, wyb, dxb, dyb) {
  LBC.push([1, stroke, w1, wxa, wya, dxa, dya, wxb, wyb, dxb, dyb]);
  drawLeaderOp(stroke, w1, sx(wxa) + dxa, sy(wya) + dya, sx(wxb) + dxb, sy(wyb) + dyb);
}
function drawTextOp(font, fill, halo, text, X, Y, align) {
  ctx.font = font; ctx.textAlign = align || "left";
  if (halo) { ctx.lineWidth = 2.4; ctx.strokeStyle = halo; ctx.strokeText(text, X, Y); }
  ctx.fillStyle = fill; ctx.fillText(text, X, Y);
  ctx.textAlign = "left";
}
function drawLeaderOp(stroke, w1, x1, y1, x2, y2) {
  ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2);
  ctx.strokeStyle = stroke; ctx.lineWidth = w1; ctx.stroke();
}
function replayLabels() {
  for (const op of LBC) {
    if (op[0] === 0) drawTextOp(op[1], op[2], op[3], op[4], sx(op[5]) + op[7], sy(op[6]) + op[8], op[9]);
    else if (op[0] === 2) drawYardNameOp(op[1], op[2], op[3], op[4], sx(op[5]), sy(op[6]));
    else drawLeaderOp(op[1], op[2], sx(op[3]) + op[5], sy(op[4]) + op[6], sx(op[7]) + op[9], sy(op[8]) + op[10]);
  }
}

/*YARDX-TYPE-START*/
/* ---------------- yard-name typography (vintage small caps) ----------
   Letterspaced SMALL CAPS drawn per glyph: canvas letterSpacing /
   fontVariantCaps are not portable (no Firefox support), so glyphs are
   laid out manually — which also gives true two-pass halos (all strokes
   first, then all fills) so one glyph's halo never eats its neighbour. */
const YN_TRK = 0.16, YN_SC = 0.78, YN_MIN = 7.5, YN_MAX = 13, YN_LEAD = 1.3;
const YN_ABBR = [[/Sidings/, "Sdgs"], [/Siding/, "Sdg"],
                 [/Carriage/, "Cge"], [/Junction/, "Jn"]];
function ynChars(text, fs) {
  const out = [];
  for (const ch of text) {
    const lc = ch !== ch.toUpperCase();
    out.push([lc ? ch.toUpperCase() : ch, lc ? fs * YN_SC : fs]);
  }
  return out;
}
function ynWidth(text, fs) {
  let w = 0;
  for (const g of ynChars(text, fs)) {
    ctx.font = "400 " + g[1] + "px Georgia,serif";
    w += ctx.measureText(g[0]).width + YN_TRK * fs;
  }
  return w - YN_TRK * fs;
}
function drawYardNameOp(fs, fill, halo, lines, X, Y) {
  ctx.textAlign = "left"; ctx.lineJoin = "round";
  for (const haloPass of [1, 0]) for (let li = 0; li < lines.length; li++) {
    const y = Y + (li - (lines.length - 1) / 2) * YN_LEAD * fs + fs * 0.35;
    let x = X - ynWidth(lines[li], fs) / 2;
    for (const g of ynChars(lines[li], fs)) {
      ctx.font = "400 " + g[1] + "px Georgia,serif";
      if (haloPass) { ctx.lineWidth = 3; ctx.strokeStyle = halo; ctx.strokeText(g[0], x, y); }
      else { ctx.fillStyle = fill; ctx.fillText(g[0], x, y); }
      x += ctx.measureText(g[0]).width + YN_TRK * fs;
    }
  }
}
function recYardName(fs, fill, halo, lines, wxp, wyp) {
  LBC.push([2, fs, fill, halo, lines, wxp, wyp]);
  drawYardNameOp(fs, fill, halo, lines, sx(wxp), sy(wyp));
}
function ynChordAt(ring, Yw) {           // widest interior chord at world y
  const xs = [];
  for (let i = 0; i < ring.length; i++) {
    const a = ring[i], b = ring[(i + 1) % ring.length];
    if ((a[1] <= Yw && Yw < b[1]) || (b[1] <= Yw && Yw < a[1]))
      xs.push(a[0] + (Yw - a[1]) / (b[1] - a[1]) * (b[0] - a[0]));
  }
  xs.sort((p, q) => p - q);
  let w = 0, cx2 = 0;
  for (let i = 0; i + 1 < xs.length; i += 2)
    if (xs[i + 1] - xs[i] > w) { w = xs[i + 1] - xs[i]; cx2 = (xs[i] + xs[i + 1]) / 2; }
  return w > 0 ? [w, cx2] : null;
}
function ynSplit(name) {                 // 2-line split minimizing the wider line
  const words = name.split(" ");
  if (words.length < 2) return null;
  let best = null, bw = 1e18;
  for (let i = 1; i < words.length; i++) {
    const a = words.slice(0, i).join(" "), b = words.slice(i).join(" ");
    const w = Math.max(ynWidth(a, 10), ynWidth(b, 10));
    if (w < bw) { bw = w; best = [a, b]; }
  }
  return best;
}
function ringAreaYN(ring) {
  let a = 0;
  for (let i = 0; i < ring.length; i++) {
    const p = ring[i], q = ring[(i + 1) % ring.length];
    a += p[0] * q[1] - q[0] * p[1];
  }
  return Math.abs(a) / 2;
}
function yardNameLayout(f) {
  // best inset layout: scan 9 horizontal chords through the poly, fit a
  // single line (1.15 score bonus) or a two-line wrap; abbreviate last.
  const ring = f.rings.reduce((a, b) => (b.length > a.length ? b : a), f.rings[0]);
  const y0w = f._bb[1], bhw = f._bb[3] - f._bb[1];
  const attempt = (name) => {
    const u1 = ynWidth(name, 10) / 10;
    const sp = ynSplit(name);
    const u2 = sp ? Math.max(ynWidth(sp[0], 10), ynWidth(sp[1], 10)) / 10 : 0;
    let best = null;
    for (let i = 0; i < 9; i++) {
      const Yw = y0w + bhw * (0.22 + 0.56 * i / 8);
      const ch = ynChordAt(ring, Yw);
      if (!ch) continue;
      const cw = ch[0] * k;
      const fs = Math.min(YN_MAX, cw * 0.88 / u1);
      if (fs >= YN_MIN && (!best || fs * 1.15 > best.sc))
        best = { sc: fs * 1.15, lines: [name], fs, X: sx(ch[1]), Y: sy(Yw) };
      if (sp) {
        let fs2 = Math.min(YN_MAX, cw * 0.88 / u2);
        if (fs2 >= YN_MIN && (1 + YN_LEAD) * fs2 <= bhw * k * 0.9) {
          const ca = ynChordAt(ring, Yw - YN_LEAD * fs2 / 2 / k),
                cb = ynChordAt(ring, Yw + YN_LEAD * fs2 / 2 / k);
          if (ca && cb) fs2 = Math.min(fs2, Math.min(ca[0], cb[0]) * k * 0.88 / u2);
          if (fs2 >= YN_MIN && (!best || fs2 > best.sc))
            best = { sc: fs2, lines: sp, fs: fs2, X: sx(ch[1]), Y: sy(Yw) };
        }
      }
    }
    return best;
  };
  let got = attempt(f.name);
  if (!got) {
    let t = f.name;
    for (const ab of YN_ABBR) t = t.replace(ab[0], ab[1]);
    if (t !== f.name) got = attempt(t);
  }
  return got;
}
/*YARDX-TYPE-END*/

/* ---------------- the frame ---------------- */
function draw() {
  raf = 0;
  if (!S) return;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, SW, SH);
  ctx.fillStyle = P.land || "#f1e9d4";
  ctx.fillRect(0, 0, SW, SH);
  bundleSync();
  yardFrame();
  const wsc = Math.max(1, Math.min(3.2, Math.pow(k, 0.45)));
  const vx0 = wx(0), vy0 = wy(0), vx1 = wx(SW), vy1 = wy(SH);

  // sea + land patches
  if (S.sea) {
    ctx.fillStyle = P.sea || "#c9d9d5";
    for (const q of S.sea.polys) { ctx.beginPath(); pathStraight(q); ctx.closePath(); ctx.fill(); }
    ctx.fillStyle = P.land || "#f1e9d4";
    for (const q of S.sea.land) { ctx.beginPath(); pathStraight(q); ctx.closePath(); ctx.fill(); }
    if (L.sea_land_det) for (const i of L.sea_land_det.g.query(vx0, vy0, vx1, vy1)) {
      const f = L.sea_land_det.arr[i]; if (!visible(f._bb)) continue;
      ctx.beginPath(); pathStraight(f.pts); ctx.closePath(); ctx.fill();
    }
  }
  // urban tint
  if (flags.urban && S.urban) {
    ctx.fillStyle = P.urban || "#e6d9ba";
    for (const u of S.urban) {
      if (!u._bb) u._bb = bboxOf(u.pts);
      if (!visible(u._bb)) continue;
      ctx.beginPath(); pathStraight(u.pts); ctx.closePath(); ctx.fill();
    }
  }
  // inland water
  ctx.fillStyle = P.water || "#aecbd0";
  for (const i of L.water.g.query(vx0, vy0, vx1, vy1)) {
    const f = L.water.arr[i]; if (!visible(f._bb)) continue;
    ctx.beginPath(); pathStraight(f.pts); ctx.closePath(); ctx.fill();
  }
  // yard footprints (YARDX compose 2026-06-10): atlas hatch + ghost fan
  // riding the crossfade band. Per poly, bottom-to-top:
  //   1. whisper wash underlay (0.22 of the old flat fill)        x yWashA
  //   2. GHOSTROADS: member yard lanes, siding ink at 0.18        x yWashA
  //   3. 45-deg "/" hatch, world-phase-locked, clipped to poly    x yWashA
  //   4. solid edge ink                                           x yWashA
  // so the whole shade package fades OUT over the band, while the dashed
  // survey outline fades IN with yTrackA and persists in tracks mode.
  if (yShadeNow || yOutlineNow) {
    const ghostSeen = new Set();   // GHOSTROADS: draw each lane once
    for (const i of L.yard_polys.g.query(vx0, vy0, vx1, vy1)) {
      const f = L.yard_polys.arr[i]; if (!visible(f._bb)) continue;
      ctx.strokeStyle = P.yard_poly_edge || "#a89a6e";
      if (yShadeNow) {
        // 1. whisper underlay
        fillRings(f.rings);
        ctx.fillStyle = P.yard_poly || "#d5cfa6";
        ctx.globalAlpha = 0.22 * yWashA; ctx.fill("evenodd");
        // 2. the hidden fan whispers through the wash: every member yard
        // lane in siding ink, above the wash, below the hatch and all
        // live ink. Members: yard-class tracks whose mid vertex lies
        // inside the poly bbox (+2 px pad); cached until tiles change.
        if (k >= 0.35) {
          if (!f._ghost || f._ghostN !== L.tracks.arr.length) {
            f._ghostN = L.tracks.arr.length;
            f._ghost = [];
            const bb = f._bb, pad = 2;
            for (const j of L.tracks.g.query(bb[0], bb[1], bb[2], bb[3])) {
              const t = L.tracks.arr[j];
              if (t.cls !== "yard" || t.pts.length < 2) continue;
              if (t._bb[2] < bb[0] || t._bb[0] > bb[2] ||
                  t._bb[3] < bb[1] || t._bb[1] > bb[3]) continue;
              const m = t.pts[t.pts.length >> 1];
              if (m[0] < bb[0] - pad || m[0] > bb[2] + pad ||
                  m[1] < bb[1] - pad || m[1] > bb[3] + pad) continue;
              f._ghost.push(t);
            }
          }
          if (f._ghost.length) {
            ctx.strokeStyle = P.siding || "#5e5743";
            ctx.lineWidth = (WID.yard || 0.55) * wsc;
            ctx.globalAlpha = 0.18 * yWashA;
            for (const t of f._ghost) {
              if (ghostSeen.has(t)) continue;
              ghostSeen.add(t);
              ctx.beginPath(); pathCurve(t.pts); ctx.stroke();
            }
            ctx.strokeStyle = P.yard_poly_edge || "#a89a6e";
          }
        }
        // 3. atlas hatch: lines x+y=c clipped to the poly, spaced
        // YARD_HATCH_S px (perp.) in screen space, phase-locked to the
        // world origin via (ox+oy) so the texture pins while panning.
        ctx.save();
        fillRings(f.rings); ctx.clip("evenodd");
        const s = YARD_HATCH_S * Math.SQRT2;   // c-step for "/" lines x+y=c
        const hx0 = sx(f._bb[0]) - 1, hy0 = sy(f._bb[1]) - 1,
              hx1 = sx(f._bb[2]) + 1, hy1 = sy(f._bb[3]) + 1;
        const ph = (ox + oy) % s;
        ctx.beginPath();
        for (let c = Math.floor((hx0 + hy0 - ph) / s) * s + ph;
             c <= hx1 + hy1; c += s) {
          const ax = Math.max(hx0, c - hy1), bx = Math.min(hx1, c - hy0);
          if (ax > bx) continue;
          ctx.moveTo(ax, c - ax); ctx.lineTo(bx, c - bx);
        }
        ctx.globalAlpha = yWashA;
        ctx.lineWidth = 0.6 * wsc;
        ctx.stroke();
        ctx.restore();
        // 4. solid edge (clip consumed the screen path -- rebuild)
        fillRings(f.rings);
        ctx.globalAlpha = yWashA;
        ctx.lineWidth = 0.6 * wsc; ctx.stroke();
      }
      if (yOutlineNow) {
        if (!yShadeNow) fillRings(f.rings);
        ctx.globalAlpha = yTrackA;
        ctx.lineWidth = 0.9 * wsc;
        ctx.setLineDash([4, 3]); ctx.stroke(); ctx.setLineDash([]);
      }
      ctx.globalAlpha = 1;
    }
  }
  // station footprints
  if (flags.plat) for (const i of L.station_polys.g.query(vx0, vy0, vx1, vy1)) {
    const f = L.station_polys.arr[i]; if (!visible(f._bb)) continue;
    fillRings(f.rings);
    ctx.fillStyle = P.station_poly || "#d8c89e"; ctx.fill("evenodd");
    ctx.strokeStyle = P.platform_edge || "#5f5130"; ctx.lineWidth = 0.7; ctx.stroke();
  }
  // platforms
  if (flags.plat && k > 0.3) {
    ctx.lineCap = "round";
    for (const i of L.platforms.g.query(vx0, vy0, vx1, vy1)) {
      const p = L.platforms.arr[i];
      const X = sx(p.x), Y = sy(p.y);
      if (X < -40 || X > SW + 40 || Y < -40 || Y > SH + 40) continue;
      const tx = p.dir[0], ty = p.dir[1], Lp = p.len * k;
      ctx.beginPath();
      ctx.moveTo(X - tx * Lp, Y - ty * Lp); ctx.lineTo(X + tx * Lp, Y + ty * Lp);
      ctx.strokeStyle = P.platform || "#bfa468";
      ctx.lineWidth = Math.max(2.2, (p.w || 1.4) * k); ctx.stroke();
    }
  }
  // former (ghost) lines — under live ink
  if (flags.former) {
    ctx.strokeStyle = P.former || "#9a8f7d";
    ctx.lineWidth = 1.0 * wsc;
    ctx.setLineDash([2 * wsc, 2.6 * wsc]);
    ctx.globalAlpha = k >= 0.5 ? 0.75 : 0.35;
    for (const i of L.former.g.query(vx0, vy0, vx1, vy1)) {
      const f = L.former.arr[i]; if (!visible(f._bb)) continue;
      ctx.beginPath(); pathCurve(f.pts); ctx.stroke();
    }
    ctx.setLineDash([]); ctx.globalAlpha = 1;
  }
  // overview running lines kept underneath while detail tiles stream in
  if (BMODE && !allLoaded) {
    if (!LOVT) {
      LOVT = Layer(); LOVT.arr = S.tracks;
      S.tracks.forEach((f, i) => { f._bb = f._bb || bboxOf(f.pts); LOVT.g.add(f._bb, i); });
    }
    ctx.lineCap = "round"; ctx.lineJoin = "round";
    for (const i of LOVT.g.query(vx0, vy0, vx1, vy1)) {
      const t = LOVT.arr[i];
      if (!visible(t._bb) || !flagOf(t)) continue;
      ctx.lineWidth = (WID[t.cls] !== undefined ? WID[t.cls] : 1.0) * wsc;
      ctx.strokeStyle = clsInk(t);
      ctx.beginPath(); pathStraight(t.pts); ctx.stroke();
    }
  }
  // tracks, class-ordered
  {
    const tt = [...L.tracks.g.query(vx0, vy0, vx1, vy1)]
      .map((i) => L.tracks.arr[i])
      .filter((t) => visible(t._bb) && flagOf(t));
    tt.sort((a, b) => (ORD[a.cls] !== undefined ? ORD[a.cls] : 5) -
                      (ORD[b.cls] !== undefined ? ORD[b.cls] : 5));
    ctx.lineCap = "round"; ctx.lineJoin = "round";
    for (const t of tt) {
      const w = (WID[t.cls] !== undefined ? WID[t.cls] : 1.0) *
                (t.br ? 0.84 : 1) * wsc;
      ctx.lineWidth = w;
      ctx.strokeStyle = clsInk(t);
      let dash = null, alpha = 1;
      if (t.cls === "narrow_gauge") dash = [6 * wsc, 1.5 * wsc];
      else if (t.cls === "construction") { dash = [3 * wsc, 3 * wsc]; alpha = 0.45; }
      else if (t.cls === "tunnel") dash = [3.2 * wsc, 2.4 * wsc];
      if (t.cls === "yard") alpha *= yTrackA;   // fade in across the band
      if (dash) ctx.setLineDash(dash);
      ctx.globalAlpha = alpha;
      // tunnel runs inside a normal track dash in the SAME ink
      const tun = t.tun && t.tun.length ? t.tun : null;
      if (!tun) { ctx.beginPath(); pathCurve(t.pts); ctx.stroke(); }
      else {
        // tun = [[idx, 0|1] ...] run-length toggles
        let runs = [], cur = 0, on = tun[0][0] === 0 ? tun[0][1] : 0, ti = 0;
        for (let i2 = 0; i2 < t.pts.length; i2++) {
          while (ti < tun.length && tun[ti][0] === i2) { on = tun[ti][1]; ti++; }
          runs.push(on);
        }
        for (let i2 = 0; i2 < t.pts.length - 1;) {
          let j = i2;
          while (j < t.pts.length - 1 && runs[j] === runs[i2]) j++;
          ctx.setLineDash(runs[i2] ? [3.2 * wsc, 2.4 * wsc] : (dash || []));
          ctx.beginPath(); pathCurve(t.pts.slice(i2, j + 1)); ctx.stroke();
          i2 = j;
        }
      }
      ctx.setLineDash([]); ctx.globalAlpha = 1;
    }
  }
  // level-crossing bars
  if (flags.lc && k > 0.4) {
    ctx.strokeStyle = P.red || "#a02818"; ctx.lineWidth = 1.6;
    for (const c of POINTS.crossings || []) {
      if (!c.bar) continue;
      const X = sx(c.x), Y = sy(c.y);
      if (X < -20 || X > SW + 20 || Y < -20 || Y > SH + 20) continue;
      ctx.beginPath();
      ctx.moveTo(sx(c.bar[0][0]), sy(c.bar[0][1]));
      ctx.lineTo(sx(c.bar[1][0]), sy(c.bar[1][1]));
      ctx.stroke();
    }
  }
  // station ticks
  if (flags.stn && k > 0.14) {
    ctx.strokeStyle = P.ink || "#2e2a22"; ctx.lineWidth = 1.5;
    for (const s of S.stations) {
      const X = sx(s.x), Y = sy(s.y);
      if (X < -10 || X > SW + 10 || Y < -10 || Y > SH + 10) continue;
      ctx.beginPath(); ctx.arc(X, Y, s.halt ? 2 : 2.8, 0, 7);
      ctx.fillStyle = P.land || "#f1e9d4"; ctx.fill(); ctx.stroke();
    }
  }
  // labels: full placement on HQ frames, replay on LQ frames
  if (LQ) replayLabels();
  else drawLabels();

  scaleBar();
  urlSync();
}
function schedule() { if (!raf) raf = requestAnimationFrame(draw); }

/* ---------------- labels (HQ frames) ---------------- */
function drawLabels() {
  OCC = new Set(); HOCC = new Set(); BOXES = []; LBC = [];
  const vx0 = wx(0), vy0 = wy(0), vx1 = wx(SW), vy1 = wy(SH);
  // seed occupancy: visible track ink + crossing bars; HARD: station polys
  for (const i of L.tracks.g.query(vx0, vy0, vx1, vy1)) {
    const t = L.tracks.arr[i];
    if (!visible(t._bb) || !flagOf(t)) continue;
    const step = Math.max(1, Math.floor(t.pts.length / Math.max(2, t.pts.length * Math.min(1, k))));
    for (let j = 0; j + 1 < t.pts.length; j += step)
      markSeg(sx(t.pts[j][0]), sy(t.pts[j][1]),
              sx(t.pts[Math.min(j + step, t.pts.length - 1)][0]),
              sy(t.pts[Math.min(j + step, t.pts.length - 1)][1]));
  }
  if (flags.plat) for (const i of L.station_polys.g.query(vx0, vy0, vx1, vy1)) {
    const f = L.station_polys.arr[i];
    if (visible(f._bb)) markRings(f.rings);
  }
  // yard names — vintage letterspaced SMALL CAPS (before stations so the
  // big names sit inside their wash). One label per name (largest visible
  // poly), anchored on the widest interior chord; two-line wrap, then
  // abbreviation, before giving up. While the wash fades (k < YARD_K2) the
  // name stays inset; once yard tracks are fully on it becomes a
  // placer-managed label with a leader.
  if ((yShadeNow || yOutlineNow) && k > 0.45) {
    const ynSeen = new Map();
    for (const i of L.yard_polys.g.query(vx0, vy0, vx1, vy1)) {
      const f = L.yard_polys.arr[i];
      if (!f.name || !visible(f._bb)) continue;
      const ring = f.rings.reduce((a, b) => (b.length > a.length ? b : a), f.rings[0]);
      const ar = ringAreaYN(ring);
      const cur = ynSeen.get(f.name);
      if (!cur || ar > cur.ar) ynSeen.set(f.name, { f, ar });
    }
    const ynInk = P.label_sub || "#6b6353";
    for (const { f } of ynSeen.values()) {
      if (yTrackA < 1) {                       // inset on the wash
        const lay = yardNameLayout(f);
        if (!lay) continue;
        // YARDX-HATCH merge: halo in land cream (flat wash is gone and the
        // hatch is busier; cream reads cleanly over hatch + ghosts)
        recYardName(lay.fs, ynInk, P.land || "#f1e9d4",
          lay.lines, wx(lay.X), wy(lay.Y));
        for (let li = 0; li < lay.lines.length; li++) {
          const w2 = ynWidth(lay.lines[li], lay.fs);
          const yy = lay.Y + (li - (lay.lines.length - 1) / 2) * YN_LEAD * lay.fs;
          markSeg(lay.X - w2 / 2, yy, lay.X + w2 / 2, yy);
        }
      } else {                                 // tracks fully on: placer + leader
        const X = sx((f._bb[0] + f._bb[2]) / 2), Y = sy((f._bb[1] + f._bb[3]) / 2);
        if (X < -80 || X > SW + 80 || Y < -80 || Y > SH + 80) continue;
        const fs = Math.max(9, Math.min(11.5, (f._bb[2] - f._bb[0]) * k * 0.05));
        const w = ynWidth(f.name, fs), h = fs + 4;
        const box = place(X, Y, w, h, cands(w, h, [10, 16, 24, 34, 46, 60]));
        if (!box) continue;
        const nx = Math.max(box[0], Math.min(X, box[0] + w)),
              ny = Math.max(box[1], Math.min(Y, box[1] + h));
        if (Math.hypot(nx - X, ny - Y) > 13)
          recLeader(ynInk, 0.7, wx(X), wy(Y), 0, 0, wx(nx), wy(ny), 0, 0);
        recYardName(fs, ynInk, P.land || "#f1e9d4",
          [f.name], wx(box[0] + w / 2), wy(box[1] + h / 2));
      }
    }
  }
  // station labels — ranked by ORR ridership (SPEC orr_usage 2026-06-10):
  // use-DESC placement order keeps the important ones when space runs out;
  // zoom-banded eligibility unclutters London; must-place only when close.
  if (flags.stn && k > 0.42) {
    const USE_DEFAULT = 100000;
    const USE_BANDS = [[0.55, 10000000], [0.95, 2000000], [1.35, 250000]];
    const MUST_K = 1.6;
    const useOf = (s) => (s.use > 0 ? s.use : USE_DEFAULT);
    const useShow = (s) => {
      const u = useOf(s);
      for (const [kb, mu] of USE_BANDS) if (k < kb) return u >= mu;
      return true;
    };
    if (!S._stByUse) S._stByUse = [...S.stations].sort((a, b) =>
      (useOf(b) - useOf(a)) || ((a.halt ? 1 : 0) - (b.halt ? 1 : 0)) ||
      ((b.crs ? 1 : 0) - (a.crs ? 1 : 0)));
    const fs = 11;
    const font = "600 " + fs + "px Georgia,serif";
    ctx.font = font;
    for (const s of S._stByUse) {
      const X = sx(s.x), Y = sy(s.y);
      if (X < -80 || X > SW + 80 || Y < -80 || Y > SH + 80) continue;
      if (useShow(s)) {
        const w = ctx.measureText(s.name).width, h = fs + 3;
        const box = place(X, Y, w, h,
          cands(w, h, [9, 15, 23, 33, 45, 60, 78, 98, 120]), k >= MUST_K);
        if (!box) continue;
        const nx = Math.max(box[0], Math.min(X, box[0] + w)),
              ny = Math.max(box[1], Math.min(Y, box[1] + h));
        const ld = Math.hypot(nx - X, ny - Y);
        if (ld > 13) recLeader(P.label_sub || "#6b6353", 0.8,
          wx(X), wy(Y), 0, 0, wx(nx), wy(ny), 0, 0);
        recText(font, P.station_label || "#274b66", P.land || "#f1e9d4",
          s.name, wx(box[0]), wy(box[1]), 0, fs);
      }
    }
  }
  // place labels. DENSITY RULE (Tyler 2026-06-10): at close zoom every
  // OSM hamlet otherwise labels — keep small places only if population
  // >= 2000 or they sit within ~500 m of a railway (memoised per place).
  if (flags.places) {
    const nrPx = 500 / (S.mpp || 30);          // 500 real m in world px
    const nearRail = (p) => {
      if (p._nr !== undefined) return p._nr;
      let hit = false;
      for (const i of L.tracks.g.query(p.x - nrPx, p.y - nrPx, p.x + nrPx, p.y + nrPx)) {
        const t = L.tracks.arr[i];
        const c = t.cls;
        if (c !== "rail" && c !== "elec" && c !== "diesel" &&
            c !== "branch" && c !== "light_rail" && c !== "narrow_gauge") continue;
        for (let j = 0; j + 1 < t.pts.length && !hit; j++)
          if (segDist(p.x, p.y, t.pts[j][0], t.pts[j][1],
                      t.pts[j + 1][0], t.pts[j + 1][1]) <= nrPx) hit = true;
        if (hit) break;
      }
      return (p._nr = hit);
    };
    for (const p of PLACES) {
      if (p.dupst && flags.stn) continue;
      const minK = p.rank >= 4 ? 0 : p.rank >= 3 ? 0.10 : 0.45;
      if (k < minK) continue;
      if ((p.rank || 0) < 3 && !((p.pop || 0) >= 2000 || nearRail(p)))
        continue;
      const X = sx(p.x), Y = sy(p.y);
      if (X < -60 || X > SW + 60 || Y < -60 || Y > SH + 60) continue;
      const fs = 9 + (p.rank || 1) * 1.6;
      const font = (p.rank >= 4 ? "700 " : "500 ") + fs + "px Georgia,serif";
      ctx.font = font;
      const w = ctx.measureText(p.name).width, h = fs + 3;
      const box = place(X, Y, w, h, cands(w, h, [6, 11, 18, 27]));
      if (!box) continue;
      recText(font, P.label_sub || "#6b6353", P.land || "#f1e9d4",
        p.name, wx(box[0]), wy(box[1]), 0, fs);
    }
  }
  // junction names
  if (flags.junctions && k > 0.9) {
    const fs = 9, font = "italic 500 " + fs + "px Georgia,serif";
    ctx.font = font;
    for (const jn of POINTS.junctions || []) {
      const X = sx(jn.x), Y = sy(jn.y);
      if (X < -60 || X > SW + 60 || Y < -60 || Y > SH + 60) continue;
      const w = ctx.measureText(jn.name).width, h = fs + 2;
      const box = place(X, Y, w, h, cands(w, h, [8, 13, 19, 27, 36]));
      if (!box) continue;
      const nx = Math.max(box[0], Math.min(X, box[0] + w)),
            ny = Math.max(box[1], Math.min(Y, box[1] + h));
      if (Math.hypot(nx - X, ny - Y) > 11)
        recLeader(P.label_sub || "#6b6353", 0.6, wx(X), wy(Y), 0, 0, wx(nx), wy(ny), 0, 0);
      recText(font, P.label_sub || "#6b6353", P.land || "#f1e9d4",
        jn.name, wx(box[0]), wy(box[1]), 0, fs);
    }
  }
  // LC labels (k gate raised 0.55→0.95: red LC marks were London noise)
  if (flags.lc && k > 0.95) {
    for (const c of POINTS.crossings || []) {
      if (c.x == null) continue;
      const X = sx(c.x), Y = sy(c.y);
      if (X < 0 || X > SW || Y < 0 || Y > SH) continue;
      const lab = c.name && k > 1.05 ? c.name : "LC";
      const font = lab === "LC" ? "700 9px Helvetica,Arial,sans-serif"
                                : "italic 600 9.5px Georgia,serif";
      ctx.font = font;
      const w = ctx.measureText(lab).width, h = 11;
      const box = place(X, Y, w, h, cands(w, h, [7, 12, 18, 26]));
      if (!box) continue;
      recText(font, P.red || "#a02818", P.land || "#f1e9d4",
        lab, wx(box[0]), wy(box[1]), 0, h - 2);
    }
  }
  // named tunnels / bridges + industry
  const namedPts = [
    [POINTS.tunnels, P.tunnel || "#7d745f", flags.tunnel],
    [POINTS.bridges, P.label_sub || "#6b6353", 1],
    [POINTS.industry, P.label_sub || "#6b6353", flags.industry],
  ];
  if (k > 0.55) for (const [arr, col, on] of namedPts) {
    if (!on) continue;
    for (const f of arr || []) {
      const X = sx(f.x), Y = sy(f.y);
      if (X < -60 || X > SW + 60 || Y < -60 || Y > SH + 60) continue;
      const fs = 10.5, font = "italic 500 " + fs + "px Georgia,serif";
      ctx.font = font;
      const txt = f.name + (f.ft ? "" : "");
      const w = ctx.measureText(txt).width, h = fs + 3;
      const box = place(X, Y, w, h, cands(w, h, [10, 17, 26, 38]));
      if (!box) continue;
      const nx = Math.max(box[0], Math.min(X, box[0] + w)),
            ny = Math.max(box[1], Math.min(Y, box[1] + h));
      if (Math.hypot(nx - X, ny - Y) > 11)
        recLeader(P.label_sub || "#6b6353", 0.7, wx(X), wy(Y), 0, 0, wx(nx), wy(ny), 0, 0);
      recText(font, col, P.land || "#f1e9d4", txt, wx(box[0]), wy(box[1]), 0, fs);
      if (f.ft) {
        const f2 = "500 " + fs * 0.85 + "px Georgia,serif";
        recText(f2, P.label_sub || "#6b6353", P.land || "#f1e9d4",
          f.ft.toLocaleString() + " ft", wx(box[0]), wy(box[1]), 0, fs * 2 + 1);
      }
    }
  }
}

/* ---------------- scale bar (imperial) ---------------- */
function scaleBar() {
  const mpp = (S.mpp || 30) / k;                 // metres per screen px
  const ftpp = mpp * 3.28084;
  const targets = [100, 250, 500, 1000, 2640, 5280, 2 * 5280, 5 * 5280,
    10 * 5280, 20 * 5280, 50 * 5280, 100 * 5280];
  let bestFt = targets[0];
  for (const t of targets) if (t / ftpp <= 180) bestFt = t;
  const wpx = bestFt / ftpp;
  $("scalerule").style.width = wpx.toFixed(0) + "px";
  $("scalelabel").textContent =
    bestFt >= 5280 ? (bestFt / 5280) + (bestFt === 5280 ? " mile" : " miles")
                   : bestFt.toLocaleString() + " ft";
}

/* ---------------- view control ---------------- */
function fit() {
  const v = S.view;
  k = Math.min(SW / v[2], SH / v[3]) * 0.98;
  kmin = k * 0.9;
  ox = (SW - v[2] * k) / 2 - v[0] * k;
  oy = (SH - v[3] * k) / 2 - v[1] * k;
}
function zoomAt(X, Y, f) {
  const nk = Math.max(kmin, Math.min(KMAX, k * f));
  ox = X - (X - ox) * (nk / k); oy = Y - (Y - oy) * (nk / k);
  k = nk; interact(); schedule();
}
function interact() {
  LQ = true; clearTimeout(lqTimer);
  lqTimer = setTimeout(() => { LQ = false; schedule(); }, 140);
}
function flyTo(x, y, tk, label) {
  flightId++;
  const id = flightId;
  if (REDUCED) {
    k = tk; ox = SW / 2 - x * k; oy = SH / 2 - y * k;
    LQ = false; schedule();
    if (label) say("Showing " + label);
    return;
  }
  const t0 = performance.now(), k0 = k, ox0 = ox, oy0 = oy, dur = 650;
  const tx = SW / 2 - x * tk, ty = SH / 2 - y * tk;
  (function step(t) {
    if (id !== flightId) return;
    let u = Math.min(1, (t - t0) / dur);
    u = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2;
    k = k0 + (tk - k0) * u; ox = ox0 + (tx - ox0) * u; oy = oy0 + (ty - oy0) * u;
    LQ = u < 1; draw();
    if (u < 1) requestAnimationFrame(step);
    else if (label) say("Showing " + label);
  })(t0);
}
function say(msg) { announce.textContent = msg; }

/* ---------------- URL state ---------------- */
let urlTimer = 0, urlApplying = false;
function urlSync() {
  if (urlApplying) return;
  clearTimeout(urlTimer);
  urlTimer = setTimeout(() => {
    if (!isFinite(k) || !isFinite(ox) || !isFinite(oy)) return;
    const cx = wx(SW / 2).toFixed(0), cy = wy(SH / 2).toFixed(0);
    const off = FLAGKEYS.filter((f) =>
      (flags[f] ? 0 : 1) !== (DEFAULTS[f] ? 0 : 1));
    let h = "#x=" + cx + "&y=" + cy + "&k=" + k.toFixed(3);
    if (off.length) h += "&t=" + off.join(".");
    if (yardMode !== "auto") h += "&yd=" + yardMode;
    history.replaceState(null, "", h);
  }, 250);
}
const DEFAULTS = Object.assign({}, flags);
function urlApply() {
  const m = {};
  for (const part of location.hash.slice(1).split("&")) {
    const [a, b] = part.split("=");
    if (a) m[a] = b;
  }
  const px = parseFloat(m.x), py = parseFloat(m.y), pk = parseFloat(m.k);
  if (isFinite(px) && isFinite(py) && isFinite(pk)) {
    urlApplying = true;
    k = Math.max(kmin, Math.min(KMAX, pk > 0 ? pk : k));
    ox = SW / 2 - px * k;
    oy = SH / 2 - py * k;
    urlApplying = false;
  }
  if (m.t) for (const f of m.t.split("."))
    if (flags[f] !== undefined) flags[f] = DEFAULTS[f] ? 0 : 1;
  if (m.yd && ["auto", "shade", "tracks", "none"].indexOf(m.yd) >= 0)
    yardMode = m.yd;
}

/* ---------------- input ---------------- */
function inputInit() {
  let dragging = false, lx = 0, ly = 0;
  const ptrs = new Map();
  let pinch0 = 0, pinchK = 1;
  cv.addEventListener("pointerdown", (e) => {
    cv.setPointerCapture(e.pointerId);
    ptrs.set(e.pointerId, [e.clientX, e.clientY]);
    if (ptrs.size === 1) { dragging = true; lx = e.clientX; ly = e.clientY; cv.classList.add("drag"); }
    else if (ptrs.size === 2) {
      const a = [...ptrs.values()];
      pinch0 = Math.hypot(a[0][0] - a[1][0], a[0][1] - a[1][1]); pinchK = k;
    }
  });
  let hoverT = 0;
  cv.addEventListener("pointermove", (e) => {
    if (!ptrs.has(e.pointerId)) {                  // no buttons down: hover
      const now = performance.now();
      if (now - hoverT > 70 && !tipPinned) {
        hoverT = now;
        const r = cv.getBoundingClientRect();
        const X = e.clientX - r.left, Y = e.clientY - r.top;
        showTip(inspect(X, Y), X, Y, false);
      }
      return;
    }
    ptrs.set(e.pointerId, [e.clientX, e.clientY]);
    if (ptrs.size === 2) {
      const a = [...ptrs.values()];
      const d = Math.hypot(a[0][0] - a[1][0], a[0][1] - a[1][1]);
      const mx = (a[0][0] + a[1][0]) / 2, my = (a[0][1] + a[1][1]) / 2;
      const r = cv.getBoundingClientRect();
      const f = (pinchK * (d / Math.max(1, pinch0))) / k;
      zoomAt(mx - r.left, my - r.top, f);
    } else if (dragging) {
      ox += e.clientX - lx; oy += e.clientY - ly;
      lx = e.clientX; ly = e.clientY;
      interact(); schedule();
    }
  });
  const up = (e) => {
    ptrs.delete(e.pointerId);
    if (!ptrs.size) { dragging = false; cv.classList.remove("drag"); }
    else if (ptrs.size === 1) {                  // pinch -> drag handoff
      const a = [...ptrs.values()][0]; lx = a[0]; ly = a[1];
    }
  };
  cv.addEventListener("pointerup", up);
  cv.addEventListener("pointercancel", up);
  cv.addEventListener("wheel", (e) => {
    e.preventDefault();
    const r = cv.getBoundingClientRect();
    const u = e.deltaMode === 1 ? 33 : e.deltaMode === 2 ? SH : 1;
    zoomAt(e.clientX - r.left, e.clientY - r.top,
           Math.exp(-e.deltaY * u * 0.0016));
  }, { passive: false });
  let downAt = null;
  cv.addEventListener("pointerdown", (e) => { downAt = [e.clientX, e.clientY, performance.now()]; });
  cv.addEventListener("pointerup", (e) => {
    if (!downAt) return;
    if (ptrs.size) { downAt = null; return; }    // still mid-pinch: not a tap
    const moved = Math.hypot(e.clientX - downAt[0], e.clientY - downAt[1]);
    if (moved < 5 && performance.now() - downAt[2] < 500) {
      const r = cv.getBoundingClientRect();
      const X = e.clientX - r.left, Y = e.clientY - r.top;
      tipPinned = false;                       // a new click may re-pin
      const b = inspect(X, Y);
      if (b) showTip(b, X, Y, true); else cardClose();
    }
    downAt = null;
  });
  cv.addEventListener("pointerleave", () => { if (!tipPinned) cardClose(); });
  cv.addEventListener("keydown", (e) => {
    const pan = e.shiftKey ? 220 : 70;
    if (e.key === "ArrowLeft") { ox += pan; interact(); schedule(); }
    else if (e.key === "ArrowRight") { ox -= pan; interact(); schedule(); }
    else if (e.key === "ArrowUp") { oy += pan; interact(); schedule(); }
    else if (e.key === "ArrowDown") { oy -= pan; interact(); schedule(); }
    else if (e.key === "+" || e.key === "=") zoomAt(SW / 2, SH / 2, 1.35);
    else if (e.key === "-") zoomAt(SW / 2, SH / 2, 1 / 1.35);
    else if (e.key === "0") { fit(); LQ = false; schedule(); say("Whole map"); }
    else if (e.key === "Enter") {
      tipPinned = false;
      const b = inspect(SW / 2, SH / 2);
      if (b) showTip(b, SW / 2, SH / 2, true);
      else { cardClose(); say("No feature at the map centre"); }
    }
    else return;
    e.preventDefault();
  });
  document.addEventListener("keydown", (e) => {
    if (e.defaultPrevented) return;   // canvas handler already acted (+/-/0)
    if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA") {
      if (e.target.id === "search") {
        if (e.key === "Escape") { closeResults(); $("search").blur(); }
        return;
      }
      if (e.key !== "Escape") return; // Esc falls through: close panels even
    }                                 // when focus is on a layer checkbox
    if (e.key === "/") { e.preventDefault(); $("search").focus(); }
    else if (e.key.toLowerCase() === "l") togglePanel(true);
    else if (e.key === "?") helpOpen();
    else if (e.key === "Escape") { togglePanel(false, true); cardClose(); }
    else if (e.key === "+" || e.key === "=") zoomAt(SW / 2, SH / 2, 1.35);
    else if (e.key === "-") zoomAt(SW / 2, SH / 2, 1 / 1.35);
    else if (e.key === "0") { fit(); LQ = false; schedule(); }
  });
  $("zoomin").onclick = () => zoomAt(SW / 2, SH / 2, 1.5);
  $("zoomout").onclick = () => zoomAt(SW / 2, SH / 2, 1 / 1.5);
  $("fit").onclick = () => { fit(); LQ = false; schedule(); say("Whole map"); };
  $("layersbtn").onclick = () => togglePanel();
  $("layersclose").onclick = () => togglePanel(false);
  $("helpbtn").onclick = helpOpen;
  $("helpclose").onclick = () => $("help").close();
  $("cardclose").onclick = cardClose;
}

/* ---------------- inspect (click) ---------------- */
function segDist(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy || 1e-9;
  let t = ((px - ax) * dx + (py - ay) * dy) / L2;
  t = t < 0 ? 0 : t > 1 ? 1 : t;
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
}
const CLSNAME = { rail: "Railway", siding: "Siding", yard: "Yard track",
  crossover: "Crossover", tunnel: "Tunnel", subway: "Underground",
  light_rail: "Light rail", tram: "Tramway", narrow_gauge: "Narrow gauge",
  funicular: "Funicular", miniature: "Miniature railway",
  construction: "Under construction", branch: "Branch line" };
const ELNAME = { dc: "DC electrified", ac: "AC electrified (overhead)",
  none: "Not electrified" };
function inspect(X, Y) {
  const wxp = wx(X), wyp = wy(Y);
  // stations first (generous radius)
  let best = null, bd = 14 / k;
  for (const s of S.stations) {
    const d = Math.hypot(s.x - wxp, s.y - wyp);
    if (d < bd) {
      bd = d;
      const rows = [["CRS code", s.crs || "—"],
                    ["Type", s.halt ? "Halt" : "Station"]];
      if (s.use > 0) rows.push(["Annual usage",
        s.use >= 1e6 ? (s.use / 1e6).toFixed(1) + " M" : s.use.toLocaleString()]);
      best = { kind: "Station", name: s.name, x: s.x, y: s.y, rows };
    }
  }
  if (!best) {
    bd = 12 / k;
    for (const jn of POINTS.junctions || []) {
      const d = Math.hypot(jn.x - wxp, jn.y - wyp);
      if (d < bd) { bd = d; best = { kind: "Junction", name: jn.name, x: jn.x, y: jn.y, rows: [] }; }
    }
  }
  if (!best) {
    bd = 12 / k;
    for (const c of POINTS.crossings || []) {
      if (c.x == null) continue;
      const d = Math.hypot(c.x - wxp, c.y - wyp);
      if (d < bd) { bd = d; best = { kind: "Level crossing",
        name: c.name || "Level crossing", x: c.x, y: c.y,
        rows: c.barrier ? [["Barrier", c.barrier]] : [] }; }
    }
  }
  if (!best && (yShadeNow || yOutlineNow)) {
    for (const i of L.yard_polys.g.query(wxp, wyp, wxp, wyp)) {
      const f = L.yard_polys.arr[i];
      if (wxp >= f._bb[0] && wxp <= f._bb[2] && wyp >= f._bb[1] && wyp <= f._bb[3] && f.name) {
        best = { kind: "Yard", name: f.name, rows: [] };
        break;
      }
    }
  }
  if (!best) {
    bd = 12 / k;
    let bt = null;
    for (const i of L.tracks.g.query(wxp - bd, wyp - bd, wxp + bd, wyp + bd)) {
      const t = L.tracks.arr[i];
      if (!flagOf(t)) continue;
      for (let j = 0; j + 1 < t.pts.length; j++) {
        const d = segDist(wxp, wyp, t.pts[j][0], t.pts[j][1], t.pts[j + 1][0], t.pts[j + 1][1]);
        if (d < bd) { bd = d; bt = t; }
      }
    }
    if (bt) {
      const rows = [];
      if (bt.el) rows.push(["Power", ELNAME[bt.el] || bt.el]);
      if (bt.spd) rows.push(["Line speed", bt.spd + " mph"]);
      if (bt.ref) rows.push(["Line ref", bt.ref]);
      best = { kind: CLSNAME[bt.cls] || bt.cls,
        name: bt.name || (CLSNAME[bt.cls] || "Railway"), rows };
    }
  }
  return best;
}
let tipPinned = false;
function showTip(best, X, Y, pin) {
  const card = $("card");
  if (!best) {
    if (!tipPinned || pin) { card.hidden = true; tipPinned = false; }
    return;
  }
  if (tipPinned && !pin) return;          // hover never replaces a pin
  tipPinned = !!pin;
  card.classList.toggle("pin", tipPinned);
  const dl = best.rows.map(([a, b]) =>
    "<dt>" + esc(a) + "</dt><dd>" + esc(b) + "</dd>").join("");
  $("cardbody").innerHTML =
    "<h2>" + esc(best.name) + "</h2><p class='kind'>" + esc(best.kind) + "</p>" +
    (dl ? "<dl>" + dl + "</dl>" : "");
  card.hidden = false;
  // anchor NEAR the cursor, flipping sides at the viewport edges
  const w = card.offsetWidth, h = card.offsetHeight;
  let lx = X + 16, ly = Y + 14;
  if (lx + w > SW - 8) lx = X - w - 12;
  if (ly + h > SH - 8) ly = Y - h - 12;
  card.style.left = Math.max(6, lx) + "px";
  card.style.top = Math.max(6, ly) + "px";
  if (pin) say(best.kind + ": " + best.name);
}
function cardClose() { $("card").hidden = true; tipPinned = false; }
const esc = (s) => String(s).replace(/[&<>"]/g,
  (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

/* ---------------- search ---------------- */
let IDX = [], resSel = -1, resItems = [];
function buildIndex() {
  IDX = [];
  for (const s of S.stations)
    IDX.push({ n: s.name, l: s.name.toLowerCase(), kind: s.halt ? "halt" : "station",
      x: s.x, y: s.y, zk: 2.2 });
  for (const p of S.places)
    IDX.push({ n: p.name, l: p.name.toLowerCase(), kind: "place",
      x: p.x, y: p.y, zk: 0.8 });
}
function searchInit() {
  const inp = $("search"), ul = $("results");
  inp.addEventListener("input", () => {
    const q = inp.value.trim().toLowerCase();
    if (q.length < 2) { closeResults(); return; }
    const starts = [], contains = [];
    for (const e of IDX) {
      const i = e.l.indexOf(q);
      if (i === 0) starts.push(e);
      else if (i > 0) contains.push(e);
      if (starts.length > 40) break;
    }
    starts.sort((a, b) => a.n.length - b.n.length);   // exact match first
    resItems = starts.concat(contains).slice(0, 12);
    ul.innerHTML = "";
    resItems.forEach((e, i) => {
      const li = document.createElement("li");
      li.setAttribute("role", "option"); li.id = "res" + i;
      li.setAttribute("aria-selected", "false");
      li.innerHTML = esc(e.n) + "<span class='kind'>" + e.kind + "</span>";
      li.addEventListener("mousedown", (ev) => ev.preventDefault());
      li.addEventListener("click", () => go(e));
      ul.appendChild(li);
    });
    resSel = -1;
    inp.removeAttribute("aria-activedescendant");
    ul.hidden = !resItems.length;
    inp.setAttribute("aria-expanded", resItems.length ? "true" : "false");
    say(resItems.length ? resItems.length + " results" : "No results");
  });
  inp.addEventListener("keydown", (e) => {
    if (e.key === "ArrowDown") { resSel = Math.min(resItems.length - 1, resSel + 1); mark(); e.preventDefault(); }
    else if (e.key === "ArrowUp") { resSel = Math.max(0, resSel - 1); mark(); e.preventDefault(); }
    else if (e.key === "Enter") { go(resItems[Math.max(0, resSel)] || resItems[0]); e.preventDefault(); }
  });
  inp.addEventListener("blur", () => setTimeout(closeResults, 150));
  function mark() {
    [...$("results").children].forEach((c, i) => {
      c.setAttribute("aria-selected", i === resSel ? "true" : "false");
      if (i === resSel) {
        c.scrollIntoView({ block: "nearest" });
        inp.setAttribute("aria-activedescendant", c.id);
      }
    });
  }
}
function closeResults() {
  $("results").hidden = true;
  $("search").setAttribute("aria-expanded", "false");
  $("search").removeAttribute("aria-activedescendant");
  resItems = []; resSel = -1;
}
function go(e) {
  if (!e) return;
  closeResults();
  $("search").value = e.n;
  flyTo(e.x, e.y, e.zk, e.n);
}

/* ---------------- panels ---------------- */
const GROUPS = [
  ["Railways", [
    ["rail_none", "Not electrified", () => P.rail_none],
    ["rail_dc", "DC electrified", () => P.rail_dc],
    ["rail_ac", "AC electrified", () => P.rail_ac],
    ["ng", "Narrow gauge", () => P.narrow_gauge, true],
    ["metro", "Metro & tram", () => P.light_rail],
    ["constr", "Construction (HS2)", () => P.construction, true],
    ["tunnel", "Tunnels", () => P.tunnel, true],
    ["former", "Former lines", () => P.former, true],
  ]],
  ["Features", [
    ["stn", "Stations & names", () => P.station_label || P.ink],
    ["plat", "Platforms & footprints", () => P.platform],
    ["lc", "Level crossings", () => P.red],
    ["junctions", "Junction names", () => P.label_sub],
    ["places", "Place names", () => P.label_sub],
    ["urban", "Urban areas", () => P.urban],
    ["industry", "Industry labels", () => P.label_sub],
  ]],
];
function panelInit() {
  const host = $("layergroups");
  // Yards: a 4-way radio — shaded OR tracks (or auto by zoom), never both
  {
    const h = document.createElement("h3"); h.textContent = "Yards & depots";
    host.appendChild(h);
    const fs = document.createElement("div");
    fs.setAttribute("role", "radiogroup");
    fs.setAttribute("aria-label", "Yard display");
    const modes = [
      ["auto", "Auto — shaded, tracks when close"],
      ["shade", "Shaded outline & name"],
      ["tracks", "Yard tracks"],
      ["none", "Hidden"],
    ];
    for (const [val, lab] of modes) {
      const row = document.createElement("label");
      const rb = document.createElement("input");
      rb.type = "radio"; rb.name = "yardmode"; rb.value = val;
      rb.checked = yardMode === val;
      const tx = document.createElement("span"); tx.textContent = lab;
      row.append(rb, tx); fs.appendChild(row);
      rb.addEventListener("change", () => {
        if (rb.checked) { yardMode = val; LQ = false; schedule(); say("Yards: " + lab); }
      });
    }
    host.appendChild(fs);
  }
  for (const [title, items] of GROUPS) {
    const h = document.createElement("h3"); h.textContent = title;
    host.appendChild(h);
    for (const [key, lab, colf, dash] of items) {
      const row = document.createElement("label");
      const cb = document.createElement("input");
      cb.type = "checkbox"; cb.checked = !!flags[key];
      const sw = document.createElement("span"); sw.className = "sw";
      const col = colf() || "#888";
      sw.style.background = dash
        ? "repeating-linear-gradient(90deg," + col + " 0 5px,transparent 5px 9px)" : col;
      const tx = document.createElement("span"); tx.textContent = lab;
      row.append(cb, sw, tx); host.appendChild(row);
      cb.addEventListener("change", () => {
        flags[key] = cb.checked ? 1 : 0; LQ = false; schedule();
        say(lab + (cb.checked ? " shown" : " hidden"));
      });
    }
  }
}
function togglePanel(force, escOnly) {
  const el = $("layers"), open = el.hidden;
  const want = force === undefined ? open : force;
  if (escOnly && el.hidden) return;
  el.hidden = !want;
  $("layersbtn").setAttribute("aria-expanded", want ? "true" : "false");
  if (want) el.querySelector("input").focus();
  else $("layersbtn").focus();
}
function helpOpen() {
  const hl = $("helplegend");
  if (!hl.children.length) {
    const rows = [
      [P.rail_none, "Railway — not electrified"],
      [P.rail_dc, "DC electrified (third rail)"],
      [P.rail_ac, "AC electrified (overhead)"],
      [P.light_rail, "Metro, light rail & tram"],
      [P.narrow_gauge, "Narrow gauge", "dash"],
      [P.construction, "Under construction (HS2)", "dash"],
      [P.former, "Former (closed) lines", "dash"],
      [P.yard_poly, "Yards & depots", "area"],
      [P.station_poly, "Station footprints", "area"],
    ];
    for (const [col, lab, kind] of rows) {
      const li = document.createElement("li");
      const sw = document.createElement("span");
      sw.className = "sw" + (kind ? " " + kind : "");
      if (kind === "area") sw.style.background = col;
      else sw.style.borderTopColor = col;
      const tx = document.createElement("span"); tx.textContent = lab;
      li.append(sw, tx); hl.appendChild(li);
    }
  }
  $("help").showModal();
}

/* ---------------- legend chips ---------------- */
function legendInit() {
  const bar = $("legendbar");
  const chips = [
    [P.rail_none, "Diesel"], [P.rail_dc, "DC"], [P.rail_ac, "AC overhead"],
    [P.light_rail, "Metro/tram"], [P.former, "Former", true],
  ];
  for (const [col, lab, dash] of chips) {
    const c = document.createElement("span"); c.className = "chip";
    const sw = document.createElement("span");
    sw.className = "sw" + (dash ? " dash" : ""); sw.style.borderTopColor = col;
    const tx = document.createElement("span"); tx.textContent = lab;
    c.append(sw, tx); bar.appendChild(c);
  }
}

/* ---------------- boot ---------------- */
function resize() {
  SW = cv.clientWidth; SH = cv.clientHeight;
  DPR = window.devicePixelRatio || 1;
  cv.width = SW * DPR; cv.height = SH * DPR;
  LQ = false; schedule();
}
window.addEventListener("resize", resize);

fetch("overview.json")
  .then((r) => { if (!r.ok) throw new Error("HTTP " + r.status); return r.json(); })
  .then((data) => {
    S = data; P = S.palette || {}; BM = S.bundle || null;
    if (BM) CACHE_MAX = BM.cache_tiles || 60;
    document.title = "Railway Map — Great Britain & Ireland";
    resize(); fit(); urlApply(); useOverview();
    if (S.sea) { for (const q of S.sea.polys) bboxOf(q); }
    buildIndex(); searchInit(); panelInit(); legendInit(); inputInit();
    $("loading").hidden = true;
    LQ = false; schedule();
    say("Map loaded. " + S.stations.length + " stations. Press slash to search.");
  })
  .catch((err) => {
    const el = $("loading");
    el.classList.add("err");
    el.textContent = location.protocol === "file:"
      ? "This viewer needs to be served over HTTP (try: python3 -m http.server)."
      : "Could not load map data (" + err.message + ").";
  });
window.addEventListener("hashchange", () => { urlApply(); LQ = false; schedule(); });
})();
