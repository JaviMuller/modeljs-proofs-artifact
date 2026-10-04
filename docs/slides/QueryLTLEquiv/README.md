# QueryLTLEquiv — slides

`QueryLTLEquiv.pptx` presents the query language, FO-LTL over finite traces, and
the theorem that the translation from queries into FO-LTL is semantics-preserving
(`analysis/Queries/`, plus the execution records at the end of
`analysis/CoreJS/CoreJsSemantics.lean`). It is aimed at readers who know LTL and
first-order logic and can read Lean, but do not know this codebase. Every slide
carries speaker notes with the full explanation.

The deck is generated; edit the sources and rebuild rather than editing the
`.pptx` by hand.

## Layout

```
QueryLTLEquiv.pptx   the deck (generated, committed)
package.json         dependencies (pptxgenjs, jszip) and npm scripts
src/build.js         entry point: sections, slide order, output, theme
src/lib.js           theme colours, slide layouts, drawing helpers
                     (cards, code blocks, timelines, arrows, …)
src/theme.js         writes the colour scheme into the generated file
src/part1.js         opening; 1. execution records
src/part2.js         2. query syntax
src/part3.js         3. query semantics
src/part4.js         4. FO-LTL; 5. the translation
src/part5.js         6. the proof; 7. wrap-up; appendix
tools/render.sh      renders every slide to render/slide-NN.jpg for checking
```

## Building

```
npm install          # once
npm run build        # writes QueryLTLEquiv.pptx next to this README
FIT_CHECK=1 npm run build   # also prints a rough text-overflow estimate
npm run render       # optional: LibreOffice + pdftoppm preview in render/
```

`npm run render` needs `soffice` and `pdftoppm` (Poppler). The deck uses Calibri,
Cambria, Consolas and Cambria Math; without them LibreOffice substitutes wider
fonts, so line breaks in the preview are only faithful with the metric-compatible
Carlito and Caladea installed (`fonts-crosextra-carlito`,
`fonts-crosextra-caladea`). PowerPoint is the reference renderer.

## Conventions

- **Colour coding**: teal (`accent1`) is the query side, violet (`accent2`) the
  FO-LTL side, orange (`accent3`) the translation and key points; red/green
  (`accent5`/`accent6`) mark wrong/right. Colours are theme slots, set once in
  `THEME` (`src/lib.js`).
- **The five parts of a query** always have the same colours: parameters teal,
  locals violet, pattern orange, `when` blue (`L.WHEN`), `except` magenta
  (`L.EXCEPT`). The last two are outside the theme so that all five stay
  distinct and do not clash with green/red.
- **Fonts**: Cambria for headings, Calibri for text, Consolas for code (`L.CODE`),
  Cambria Math for formulas (`L.MATH`).
- **Code must not wrap**: size code blocks for a monospace font slightly wider
  than Consolas, and break long Lean lines by hand.
- **Diagrams are native shapes** (`timeline`, `card`, `arrow`, … in `src/lib.js`),
  so they stay editable in PowerPoint.
- Formulas shown as `#guard` output are copied from
  `analysis/Queries/FoLtl/CoreJsQueryToLtl.lean`; update both together if the
  translation changes.
