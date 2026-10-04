// Builds QueryLTLEquiv.pptx (see ../README.md).  Usage: node src/build.js [output.pptx]
const path = require("path");
const L = require("./lib");
const { applyTheme } = require("./theme");

const out = process.argv[2] || path.join(__dirname, "..", "QueryLTLEquiv.pptx");
const { pres, C } = L.make();

let section = null;
let count = 0;
const D = {
  pres, C, L,
  section(title, number, blurb, notes) {
    section = `${number}. ${title}`;
    pres.addSection({ title: section });
    const s = pres.addSlide({ masterName: "Section", sectionTitle: section });
    L.setSlideName(`divider ${number}`);
    s.addText(String(number), { x: 0.8, y: 2.55, w: 1.2, h: 1.4, fontSize: 80, bold: true, fontFace: "Cambria",
      color: C.accent3, align: "left", valign: "bottom", margin: 0, isTextBox: true });
    s.addText(title, { placeholder: "title" });
    s.addText(blurb, { placeholder: "body" });
    if (notes) s.addNotes(notes);
    count++;
    return s;
  },
  slide(title, notes) {
    const s = pres.addSlide({ masterName: "Content", sectionTitle: section });
    count++;
    L.setSlideName(`slide ${count} (${title})`);
    s.addText(title, { placeholder: "title" });
    if (notes) s.addNotes(notes);
    return s;
  },
  titleSlide(title, sub, notes) {
    section = "Opening";
    pres.addSection({ title: section });
    const s = pres.addSlide({ masterName: "Title", sectionTitle: section });
    count++;
    s.addText(title, { placeholder: "title" });
    s.addText(sub, { placeholder: "body" });
    if (notes) s.addNotes(notes);
    return s;
  },
  setSection(t) { section = t; pres.addSection({ title: t }); },
};

require("./part1")(D);
require("./part2")(D);
require("./part3")(D);
require("./part4")(D);
require("./part5")(D);

(async () => {
  await pres.writeFile({ fileName: out });
  await applyTheme(out, L.THEME);
  console.log(`wrote ${out}: ${count} slides`);
  // Rough, pessimistic text-fit estimate (most hits are single-line labels that fit).
  if (process.env.FIT_CHECK && L.warnings.length) { console.log("FIT WARNINGS:"); L.warnings.forEach((w) => console.log("  " + w)); }
})();
