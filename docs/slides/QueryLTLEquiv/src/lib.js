// Theme, layouts and drawing helpers for QueryLTLEquiv.pptx.
const pptxgen = require("pptxgenjs");

const THEME = {
  name: "Query LTL",
  headFontFace: "Cambria",
  bodyFontFace: "Calibri",
  colors: {
    dk1: "1B2430", lt1: "FFFFFF", dk2: "2E3B4E", lt2: "EEF2F6",
    accent1: "0F766E", // teal: query side
    accent2: "5B3FA8", // violet: FO-LTL side
    accent3: "C2410C", // orange: the translation / bridge, highlights
    accent4: "64748B", // slate: muted
    accent5: "B42318", // red: wrong / fails
    accent6: "2F855A", // green: right / holds
    hlink: "0F766E", folHlink: "5B3FA8",
  },
};

// Fixed colours for the five parts of a query (parameters, locals, pattern, when,
// except), used wherever those parts are colour-coded. Parameters, locals and the
// pattern reuse accent1–3; when and except get their own hues so that all five
// stay distinct (accent5/accent6 mean wrong/right elsewhere).
const WHEN = "1D4ED8";   // blue
const EXCEPT = "BE185D"; // magenta

const MATH = "Cambria Math";
const CODE = "Consolas";

function make() {
  const pres = new pptxgen();
  pres.layout = "LAYOUT_WIDE"; // 13.333 x 7.5
  pres.theme = { headFontFace: THEME.headFontFace, bodyFontFace: THEME.bodyFontFace };
  pres.title = "Queries and FO-LTL: a semantics-preserving translation";
  pres.author = "Javier de Muller";
  const C = pres.SchemeColor;

  pres.defineSlideMaster({
    title: "Title",
    background: { color: THEME.colors.dk1 },
    objects: [
      { placeholder: { options: { name: "title", type: "title", x: 0.8, y: 2.0, w: 11.7, h: 1.5,
          fontSize: 44, bold: true, color: C.background1, valign: "bottom", align: "left" }, text: "" } },
      { placeholder: { options: { name: "body", type: "body", x: 0.8, y: 3.7, w: 11.7, h: 1.6,
          fontSize: 22, color: C.background2, valign: "top", align: "left" }, text: "" } },
    ],
  });
  pres.defineSlideMaster({
    title: "Section",
    background: { color: THEME.colors.dk2 },
    objects: [
      { placeholder: { options: { name: "title", type: "title", x: 2.2, y: 2.6, w: 10.3, h: 1.2,
          fontSize: 40, bold: true, color: C.background1, valign: "bottom", align: "left" }, text: "" } },
      { placeholder: { options: { name: "body", type: "body", x: 2.2, y: 3.9, w: 10.3, h: 1.2,
          fontSize: 20, color: C.background2, valign: "top", align: "left" }, text: "" } },
    ],
  });
  pres.defineSlideMaster({
    title: "Content",
    background: { color: THEME.colors.lt1 },
    slideNumber: { x: 12.25, y: 7.02, w: 0.7, h: 0.3, fontSize: 10, color: C.accent4, align: "right" },
    objects: [
      { text: { text: "Queries ⇔ FO-LTL  ·  Lean 4 formalisation",
          options: { x: 0.6, y: 7.02, w: 6, h: 0.3, fontSize: 10, color: C.accent4 } } },
      { placeholder: { options: { name: "title", type: "title", x: 0.6, y: 0.3, w: 12.1, h: 0.85,
          fontSize: 34, bold: true, color: C.text1, valign: "middle", align: "left" }, text: "" } },
    ],
  });
  return { pres, C };
}

// ---------------------------------------------------------------------------
// Rough text-fit estimate (no renderer available): warns when the text is
// likely to need more lines than the box can hold.
const warnings = [];
let currentSlide = "";
function setSlideName(n) { currentSlide = n; }
function plain(t) {
  if (typeof t === "string") return t;
  return t.map((r) => (typeof r === "string" ? r : r.text) + (r.options && r.options.breakLine ? "\n" : "")).join("");
}
function checkFit(text, o) {
  const size = o.fontSize || 16;
  const mono = o.fontFace === CODE;
  const charW = (size / 72) * (mono ? 0.6 : 0.5);
  const lineH = (size / 72) * 1.2 * (o.lineSpacingMultiple || 1);
  const pad = o.margin === 0 ? 0 : 0.1;
  const usable = Math.max(0.1, (o.w || 1) - 2 * pad);
  const perLine = Math.max(1, Math.floor(usable / charW));
  let lines = 0;
  for (const para of plain(text).split("\n")) lines += Math.max(1, Math.ceil(para.length / perLine));
  const need = lines * lineH + 2 * pad;
  if (need > (o.h || 1) + 0.05)
    warnings.push(`${currentSlide}: "${plain(text).slice(0, 40).replace(/\n/g, " ")}…" needs ~${need.toFixed(2)}in, box ${o.h}in`);
}

// ---------------------------------------------------------------------------
function tx(s, text, o) {
  const opts = Object.assign({ fontSize: 16, color: o.color, valign: "top", margin: 0.05, isTextBox: true }, o);
  checkFit(text, opts);
  s.addText(text, opts);
}
function bullets(s, items, o) {
  const size = o.fontSize || 16;
  const runs = items.map((it, k) => {
    const last = k === items.length - 1;
    if (typeof it === "string") return { text: it, options: { bullet: true, breakLine: !last, paraSpaceAfter: 6 } };
    // [text runs], with an optional indent level
    return { text: it.text, options: Object.assign({ bullet: it.sub ? { indent: 18 } : true, indentLevel: it.sub ? 1 : 0,
      breakLine: !last, paraSpaceAfter: 6 }, it.options || {}) };
  });
  tx(s, runs, Object.assign({ fontSize: size }, o));
}
function card(s, C, x, y, w, h, o = {}) {
  s.addShape("roundRect", { x, y, w, h, rectRadius: 0.08,
    fill: { color: o.fill || C.background2, transparency: o.transparency || 0 },
    line: o.line ? { color: o.line, width: o.lineWidth || 1.25, dashType: o.dash || "solid" } : { type: "none" },
    objectName: o.name || "card" });
}
function pill(s, C, text, x, y, color, o = {}) {
  const w = o.w || Math.max(0.8, 0.11 * text.length + 0.35);
  s.addShape("roundRect", { x, y, w, h: o.h || 0.32, rectRadius: 0.16, fill: { color }, line: { type: "none" }, objectName: "pill" });
  s.addText(text, { x, y, w, h: o.h || 0.32, fontSize: o.fontSize || 11, bold: true, color: C.background1,
    align: "center", valign: "middle", margin: 0, isTextBox: true });
  return w;
}
// A code block: tinted card, monospace text, a small tag.
function code(s, C, text, x, y, w, h, o = {}) {
  card(s, C, x, y, w, h, { fill: o.fill || C.background2, name: "code" });
  if (o.tag !== false) pill(s, C, o.tag || "Lean", x + w - (o.tagW || 0.85) - 0.12, y + 0.1, o.tagColor || C.accent4, { w: o.tagW || 0.85, h: 0.28, fontSize: 10 });
  // fullWidth: the first line is short enough to sit beside the tag, so the
  // text need not reserve the tag's column on every line.
  tx(s, text, { x: x + 0.15, y: y + 0.12, w: w - 0.3 - (o.tag === false || o.fullWidth ? 0 : 0.9), h: h - 0.2,
    fontFace: CODE, fontSize: o.fontSize || 14, color: C.text1, margin: 0, lineSpacingMultiple: 1.05 });
}
// Formula text (math font).
function math(s, C, text, o) {
  tx(s, text, Object.assign({ fontFace: MATH, fontSize: 18, color: C.text1 }, o));
}
function arrow(s, C, x1, y1, x2, y2, o = {}) {
  const flipH = x2 < x1, flipV = y2 < y1;
  s.addShape("line", { x: Math.min(x1, x2), y: Math.min(y1, y2), w: Math.max(Math.abs(x2 - x1), 0.001), h: Math.max(Math.abs(y2 - y1), 0.001),
    flipH, flipV, line: { color: o.color || C.accent4, width: o.width || 1.75, dashType: o.dash || "solid",
      endArrowType: o.noHead ? undefined : "triangle", beginArrowType: o.both ? "triangle" : undefined }, objectName: "arrow" });
}
function line(s, C, x1, y1, x2, y2, o = {}) { arrow(s, C, x1, y1, x2, y2, Object.assign({ noHead: true }, o)); }

// A titled box: a header line in a colour and body text below.
function box(s, C, x, y, w, h, title, body, o = {}) {
  card(s, C, x, y, w, h, { fill: o.fill || C.background2, transparency: o.transparency, line: o.line });
  tx(s, title, { x: x + 0.2, y: y + 0.12, w: w - 0.4, h: 0.45, fontSize: o.titleSize || 18, bold: true, color: o.titleColor || C.text1 });
  if (body) {
    if (Array.isArray(body) && body.length && typeof body[0] === "string" && o.bullets !== false)
      bullets(s, body, { x: x + 0.2, y: y + 0.6, w: w - 0.4, h: h - 0.7, fontSize: o.fontSize || 15, color: C.text1 });
    else tx(s, body, { x: x + 0.2, y: y + 0.6, w: w - 0.4, h: h - 0.7, fontSize: o.fontSize || 15, color: C.text1,
      fontFace: o.bodyFont });
  }
}

// A trace drawn on boundaries: ticks 0..n, actions between ticks.
// spans: [{from, to, label, color, row}] drawn as brackets below the trace.
function timeline(s, C, x, y, cellW, actions, o = {}) {
  const n = actions.length;
  const boxH = o.boxH || 0.5;
  const fs = o.fontSize || 13;
  for (let k = 0; k < n; k++) {
    const hl = (o.highlight || {})[k];
    s.addShape("roundRect", { x: x + k * cellW + 0.08, y, w: cellW - 0.16, h: boxH, rectRadius: 0.06,
      fill: { color: hl || C.background2 }, line: { color: hl || C.accent4, width: 1 }, objectName: "action" });
    s.addText(actions[k], { x: x + k * cellW + 0.08, y, w: cellW - 0.16, h: boxH, fontFace: CODE, fontSize: fs,
      color: hl ? C.background1 : C.text1, align: "center", valign: "middle", margin: 0.02, isTextBox: true });
  }
  if (o.indices) {
    // List mode: each index sits under its element; no boundary ticks.
    for (let k = 0; k < n; k++)
      s.addText(`t[${k}]`, { x: x + k * cellW, y: y + boxH + 0.08, w: cellW, h: 0.3, fontFace: CODE, fontSize: 12, bold: true,
        color: C.accent4, align: "center", margin: 0, isTextBox: true });
    return;
  }
  for (let k = 0; k <= n; k++) {
    const tickColor = o.sentinel && k === n ? C.accent3 : C.accent4;
    line(s, C, x + k * cellW, y - 0.12, x + k * cellW, y + boxH + 0.12, { color: tickColor, width: 1.5 });
    s.addText(String(k), { x: x + k * cellW - 0.25, y: y + boxH + 0.12, w: 0.5, h: 0.3, fontSize: 12, bold: true,
      color: tickColor, align: "center", margin: 0, isTextBox: true });
  }
  (o.spans || []).forEach((sp) => {
    const yy = y + boxH + 0.55 + (sp.row || 0) * 0.5;
    const x1 = x + sp.from * cellW, x2 = x + sp.to * cellW;
    const col = sp.color || C.accent1;
    if (sp.to > sp.from) {
      line(s, C, x1, yy, x2, yy, { color: col, width: 2.5 });
      line(s, C, x1, yy - 0.1, x1, yy + 0.1, { color: col, width: 2.5 });
      line(s, C, x2, yy - 0.1, x2, yy + 0.1, { color: col, width: 2.5 });
    } else {
      s.addShape("ellipse", { x: x1 - 0.08, y: yy - 0.08, w: 0.16, h: 0.16, fill: { color: col }, line: { type: "none" } });
    }
    if (sp.label) s.addText(sp.label, { x: Math.min(x1, x2) + (sp.labelDx || 0), y: yy + 0.04, w: Math.max(x2 - x1, 2.2) + (sp.labelW || 0), h: 0.36,
      fontSize: 13, color: col, bold: true, align: sp.to > sp.from ? "center" : "left", margin: 0.02, isTextBox: true });
  });
}

// Text runs in which "_x" (an underscore and one letter) becomes a subscripted x,
// for subscripts Unicode has no character for (e.g. the f of l_f). Newlines
// become line breaks.
function sub(text, opts = {}) {
  const runs = [];
  const lines = text.split("\n");
  lines.forEach((ln, li) => {
    const parts = ln.split(/_([A-Za-z])/);
    const start = runs.length;
    parts.forEach((p, i) => {
      if (p === "") return;
      runs.push({ text: p, options: Object.assign({}, opts, i % 2 ? { subscript: true } : {}) });
    });
    if (runs.length === start) runs.push({ text: "", options: Object.assign({}, opts) }); // empty line
    if (li < lines.length - 1) runs[runs.length - 1].options.breakLine = true;
  });
  return runs;
}

module.exports = { sub, WHEN, EXCEPT, THEME, MATH, CODE, make, tx, bullets, card, pill, code, math, arrow, line, box, timeline, warnings, setSlideName };
