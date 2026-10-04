// Write the deck's colour scheme into ppt/theme/theme1.xml.
//
// pptxgenjs sets the theme fonts but always writes Office's default palette, so
// the scheme colours used throughout the slides (accent1, text2, …) would
// otherwise render in Office blue and orange.  This replaces the twelve colour
// slots of <a:clrScheme> and the scheme's name, in place.
const fs = require("fs");
const JSZip = require("jszip");

const SLOTS = ["dk1", "lt1", "dk2", "lt2", "accent1", "accent2", "accent3", "accent4",
  "accent5", "accent6", "hlink", "folHlink"];

function escapeXml(s) {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

async function applyTheme(file, theme) {
  for (const k of SLOTS) {
    if (!/^[0-9A-Fa-f]{6}$/.test(theme.colors[k] || ""))
      throw new Error(`theme colour ${k} must be six hex digits, got ${theme.colors[k]}`);
  }
  const zip = await JSZip.loadAsync(fs.readFileSync(file));
  const path = "ppt/theme/theme1.xml";
  let xml = await zip.file(path).async("string");
  for (const k of SLOTS) {
    const re = new RegExp(`<a:${k}>[\\s\\S]*?</a:${k}>`);
    if (!re.test(xml)) throw new Error(`no <a:${k}> slot in ${path}`);
    xml = xml.replace(re, `<a:${k}><a:srgbClr val="${theme.colors[k].toUpperCase()}"/></a:${k}>`);
  }
  xml = xml.replace(/<a:clrScheme name="[^"]*">/, `<a:clrScheme name="${escapeXml(theme.name)}">`);
  zip.file(path, xml);
  fs.writeFileSync(file, await zip.generateAsync({ type: "nodebuffer", compression: "DEFLATE" }));
}

module.exports = { applyTheme };
