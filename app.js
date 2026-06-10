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
/* Yards are EITHER a shaded footprint OR their tracks, never both (Tyler).
   auto = shaded wash zoomed out, real fanned tracks + outline once close. */
let yardMode = "auto";              // auto | shade | tracks | none
const YARD_K = 2.2;                 // auto switchover zoom
let yShadeNow = true, yTracksNow = false, yOutlineNow = false;
function yardFrame() {
  yShadeNow = yardMode === "shade" || (yardMode === "auto" && k < YARD_K);
  yTracksNow = yardMode === "tracks" || (yardMode === "auto" && k >= YARD_K);
  yOutlineNow = yardMode === "auto" && k >= YARD_K;   // keep the outline+name
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
      .catch(() => { if (tileCache.get(kk) === e) { e.st = 2; e.req = 0; } })
      .finally(() => { inflight--; pump(); tileSpin(); });
  }
  tileSpin();
}
let detDirty = false;
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
let POINTS = {}, PLACES = [];
function bundleSync() {
  if (!BM) return;
  const want = k >= (BM.k_detail || 0.25);
  if (want) {
    const need = tilesInView(1);
    allLoaded = true;
    for (const kk of need) {
      let e = tileCache.get(kk);
      if (!e) { tileCache.set(kk, e = { st: 0, req: 0 }); fq.push(kk); }
      if (e.st !== 1) allLoaded = false;
      else e.t = performance.now();
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
    if (!BMODE || detDirty) { rebuildDET(); BMODE = true; detDirty = false; }
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
    else drawLeaderOp(op[1], op[2], sx(op[3]) + op[5], sy(op[4]) + op[6], sx(op[7]) + op[9], sy(op[8]) + op[10]);
  }
}

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
  // yard footprints: filled wash (shade mode) or outline only (auto, zoomed)
  if (yShadeNow || yOutlineNow) for (const i of L.yard_polys.g.query(vx0, vy0, vx1, vy1)) {
    const f = L.yard_polys.arr[i]; if (!visible(f._bb)) continue;
    fillRings(f.rings);
    if (yShadeNow) { ctx.fillStyle = P.yard_poly || "#d5cfa6"; ctx.fill("evenodd"); }
    ctx.strokeStyle = P.yard_poly_edge || "#a89a6e";
    ctx.lineWidth = (yShadeNow ? 0.6 : 0.9) * wsc;
    if (!yShadeNow) ctx.setLineDash([4, 3]);
    ctx.stroke(); ctx.setLineDash([]);
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
  // yard names (before stations so big names sit inside their wash)
  if ((yShadeNow || yOutlineNow) && k > 0.45) {
    for (const i of L.yard_polys.g.query(vx0, vy0, vx1, vy1)) {
      const f = L.yard_polys.arr[i];
      if (!f.name || !visible(f._bb)) continue;
      const bx0 = sx(f._bb[0]), by0 = sy(f._bb[1]), bx1 = sx(f._bb[2]), by1 = sy(f._bb[3]);
      const bw = bx1 - bx0, bh = by1 - by0;
      const fs = Math.max(8, Math.min(12, bw * 0.06, bh * 0.45));
      const font = "italic 600 " + fs + "px Georgia,serif";
      ctx.font = font;
      const w = ctx.measureText(f.name).width;
      if (w > bw * 0.95) continue;
      const cx2 = (bx0 + bx1) / 2, cy2 = (by0 + by1) / 2;
      recText(font, P.label_sub || "#6b6353", P.yard_poly || "#d5cfa6",
        f.name, wx(cx2), wy(cy2 - fs * 0.35), 0, fs * 0.7, "center");
      markSeg(cx2 - w / 2, cy2, cx2 + w / 2, cy2);
    }
  }
  // station labels — ALWAYS place (r3), never on a footprint
  if (flags.stn && k > 0.5) {
    const fs = 11;
    const font = "600 " + fs + "px Georgia,serif";
    ctx.font = font;
    for (const s of S.stations) {
      const X = sx(s.x), Y = sy(s.y);
      if (X < -80 || X > SW + 80 || Y < -80 || Y > SH + 80) continue;
      if (!s.halt || k > 0.8) {
        const w = ctx.measureText(s.name).width, h = fs + 3;
        const box = place(X, Y, w, h,
          cands(w, h, [9, 15, 23, 33, 45, 60, 78, 98, 120]), true);
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
  // LC labels
  if (flags.lc && k > 0.55) {
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
  if (m.x !== undefined && m.y !== undefined && m.k !== undefined) {
    urlApplying = true;
    k = Math.max(kmin, Math.min(KMAX, parseFloat(m.k) || k));
    ox = SW / 2 - parseFloat(m.x) * k;
    oy = SH / 2 - parseFloat(m.y) * k;
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
  };
  cv.addEventListener("pointerup", up);
  cv.addEventListener("pointercancel", up);
  cv.addEventListener("wheel", (e) => {
    e.preventDefault();
    const r = cv.getBoundingClientRect();
    zoomAt(e.clientX - r.left, e.clientY - r.top, Math.exp(-e.deltaY * 0.0016));
  }, { passive: false });
  let downAt = null;
  cv.addEventListener("pointerdown", (e) => { downAt = [e.clientX, e.clientY, performance.now()]; });
  cv.addEventListener("pointerup", (e) => {
    if (!downAt) return;
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
    else return;
    e.preventDefault();
  });
  document.addEventListener("keydown", (e) => {
    if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA") {
      if (e.key === "Escape") { closeResults(); $("search").blur(); }
      return;
    }
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
    if (d < bd) { bd = d; best = { kind: "Station", name: s.name, x: s.x, y: s.y,
      rows: [["CRS code", s.crs || "—"], ["Type", s.halt ? "Halt" : "Station"]] }; }
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
      li.role = "option"; li.id = "res" + i;
      li.innerHTML = esc(e.n) + "<span class='kind'>" + e.kind + "</span>";
      li.addEventListener("mousedown", (ev) => { ev.preventDefault(); go(e); });
      ul.appendChild(li);
    });
    resSel = -1;
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
