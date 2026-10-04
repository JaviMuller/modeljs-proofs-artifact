// Opening, and section 1: execution records.
module.exports = function (D) {
  const { C, L } = D;
  const { tx, bullets, card, pill, code, math, arrow, line, box, timeline } = L;

  // 1 ── Title
  D.titleSlide("Queries and FO-LTL",
    [{ text: "A semantics-preserving translation, formalised in Lean 4", options: { breakLine: true } },
     { text: "Core JavaScript security queries  ·  analysis/Queries/", options: { fontSize: 16, color: C.accent4 } }],
    "This talk covers the query language for describing vulnerable behaviours of Core JavaScript programs, " +
    "first-order LTL over finite traces, and the theorem that a translation from the first into the second " +
    "preserves meaning exactly. Everything shown is machine-checked in Lean 4, without Mathlib, with no sorry " +
    "and no axioms beyond Lean's standard three.");

  // 2 ── Where this fits
  {
    const s = D.slide("Where this part fits",
      "The project formalises a static analysis of Core JavaScript. A program runs under a big-step semantics and " +
      "produces an execution record: what happened (a trace) and what is true of the locations at the end (an observation). " +
      "Two independent readings sit on top of records: the query language says whether a record matches a query; " +
      "FO-LTL says whether the record, seen as a model, satisfies a formula. This talk is about the arrow between them. " +
      "The automaton-based analysis is a separate chain on top of the same concrete semantics and is not covered here.");
    const y0 = 1.75;
    card(s, C, 0.6, y0 + 0.9, 2.4, 1.2, { fill: C.text2 });
    tx(s, [{ text: "Core JS program", options: { bold: true, breakLine: true } }, { text: "big-step semantics", options: { fontSize: 13 } }],
      { x: 0.7, y: y0 + 1.0, w: 2.2, h: 1.0, color: C.background1, align: "center", valign: "middle" });
    arrow(s, C, 3.0, y0 + 1.5, 3.9, y0 + 1.5, { color: C.text2 });
    tx(s, "BigStep", { x: 3.0, y: y0 + 1.05, w: 0.9, h: 0.35, fontSize: 12, color: C.accent4, align: "center", fontFace: L.CODE });
    card(s, C, 3.9, y0 + 0.7, 2.8, 1.6, { fill: C.background2, line: C.text2 });
    tx(s, [{ text: "Execution record", options: { bold: true, breakLine: true } },
           { text: "⟨ t, σ ⟩", options: { fontFace: L.MATH, fontSize: 22, breakLine: true } },
           { text: "trace + observation", options: { fontSize: 13, color: C.accent4 } }],
      { x: 4.0, y: y0 + 0.8, w: 2.6, h: 1.4, align: "center", valign: "middle", color: C.text1 });
    // two worlds
    card(s, C, 7.9, y0 - 0.2, 4.8, 1.5, { fill: C.accent1, transparency: 88, line: C.accent1 });
    tx(s, [{ text: "Query semantics", options: { bold: true, color: C.accent1, breakLine: true } },
           { text: "Exec.Matches Δ e Q ls", options: { fontFace: L.CODE, fontSize: 15, breakLine: true } },
           { text: "“the record exhibits the behaviour”", options: { fontSize: 13, italic: true } }],
      { x: 8.1, y: y0 - 0.1, w: 4.4, h: 1.3, color: C.text1, valign: "middle" });
    card(s, C, 7.9, y0 + 2.4, 4.8, 1.5, { fill: C.accent2, transparency: 88, line: C.accent2 });
    tx(s, [{ text: "FO-LTL", options: { bold: true, color: C.accent2, breakLine: true } },
           { text: "e.toModel, ξ, 0 ⊨ φ", options: { fontFace: L.MATH, fontSize: 16, breakLine: true } },
           { text: "“the model satisfies the formula”", options: { fontSize: 13, italic: true } }],
      { x: 8.1, y: y0 + 2.5, w: 4.4, h: 1.3, color: C.text1, valign: "middle" });
    arrow(s, C, 6.7, y0 + 1.2, 7.9, y0 + 0.55, { color: C.accent1 });
    arrow(s, C, 6.7, y0 + 1.8, 7.9, y0 + 3.15, { color: C.accent2 });
    // the bridge
    arrow(s, C, 10.3, y0 + 1.3, 10.3, y0 + 2.4, { color: C.accent3, width: 3, both: true });
    pill(s, C, "this talk:  ⇔", 10.5, y0 + 1.68, C.accent3, { w: 1.6 });
    // out of scope
    card(s, C, 0.6, 5.95, 6.1, 0.85, { fill: C.background1, line: C.accent4, dash: "dash" });
    tx(s, [{ text: "Out of scope: ", options: { bold: true } },
           { text: "the call-string automaton analysis (soundness, totality). It sits on the same concrete semantics, independently." }],
      { x: 0.75, y: 5.98, w: 5.8, h: 0.8, fontSize: 14, color: C.accent4, valign: "middle" });
    tx(s, [{ text: "Files: ", options: { bold: true } },
           { text: "CoreJS/CoreJsSemantics.lean (records) · Queries/QueryLanguage/ · Queries/FoLtl/", options: { fontFace: L.CODE, fontSize: 13 } }],
      { x: 7.9, y: 5.95, w: 4.8, h: 0.85, fontSize: 14, color: C.text2, valign: "middle" });
  }

  // 3 ── The result in one slide
  {
    const s = D.slide("The result in one slide",
      "This is the destination. For any well-formed query program with q at its head, any execution record e, " +
      "and any list of argument locations of the right length: q matches e with those arguments exactly when " +
      "the model of e satisfies the translated formula at the start of the trace (position 0), under the valuation that sends q's parameters to the arguments. " +
      "Three things to notice: it covers the whole query language, including the hard parts; it holds for any record, " +
      "not only those produced by real runs; and the translation is computable, so we can print the formulas.");
    card(s, C, 0.6, 1.45, 12.1, 1.95, { fill: C.accent3, transparency: 90, line: C.accent3 });
    tx(s, "For every well-formed program q :: Δ, record e, and arguments ls with |ls| = |q.params|:",
      { x: 0.85, y: 1.55, w: 11.6, h: 0.45, fontSize: 16, color: C.text1 });
    tx(s, [{ text: "Exec.Matches (q :: Δ) e q.name ls", options: { color: C.accent1, bold: true } },
           { text: "   ⇔   ", options: { color: C.accent3, bold: true } },
           { text: "e.toModel, topEnv ls, 0 ⊨ tr(q)", options: { color: C.accent2, bold: true } }],
      { x: 0.85, y: 2.05, w: 11.6, h: 0.6, fontSize: 21, fontFace: L.MATH, align: "center" });
    tx(s, "Lean: Query.tr_correct, Query.exists_tr_correct, Query.tr_computed_correct  (Queries/FoLtl/CoreJsQueryToLtl.lean)",
      { x: 0.85, y: 2.8, w: 11.6, h: 0.4, fontSize: 13, color: C.accent4, align: "center" });
    const cards = [
      ["Full language", "Patterns, invariants, except-guards, local variables and query invocation."],
      ["Any record", "Not only records of real runs: the two semantics agree on every ⟨t, σ⟩."],
      ["Computable", "Query.tr prints the formula; #guard checks pin example outputs."],
    ];
    cards.forEach(([h, b], k) => {
      const x = 0.6 + k * 4.1;
      box(s, C, x, 3.6, 3.9, 1.65, h, b, { titleColor: C.accent3, fontSize: 15 });
    });
    const road = ["Records", "Query syntax", "Query semantics", "FO-LTL", "Translation", "Proof"];
    tx(s, "Roadmap", { x: 0.6, y: 5.45, w: 3, h: 0.4, fontSize: 16, bold: true, color: C.text2 });
    road.forEach((r, k) => {
      const x = 0.6 + k * 2.03;
      s.addShape("ellipse", { x, y: 5.95, w: 0.5, h: 0.5, fill: { color: C.text2 }, line: { type: "none" } });
      s.addText(String(k + 1), { x, y: 5.95, w: 0.5, h: 0.5, fontSize: 16, bold: true, color: C.background1, align: "center", valign: "middle", margin: 0, isTextBox: true });
      tx(s, r, { x: x + 0.58, y: 5.95, w: 1.45, h: 0.5, fontSize: 14, color: C.text1, valign: "middle" });
    });
  }

  // ── Section 1
  D.section("What queries talk about", 1, "Execution records: a trace of actions, and an observation of the locations",
    "Before any query, we need the thing queries are evaluated on. That is the execution record, defined at the end of CoreJsSemantics.lean.");

  // 5 ── Core JS in one slide
  {
    const s = D.slide("Core JS in one slide",
      "Everything in Core JS is a location; Loc is just Nat. Literals live at fixed canonical locations given by litLoc: " +
      "every occurrence of the literal 5 is the same location. Binary operations and object literals allocate fresh locations. " +
      "Only three kinds of statement leave trace actions: property lookups, property updates and calls (a call leaves two, call and ret). " +
      "setTaint and setSink do not appear in the trace; they mark locations in the taint register. " +
      "Note that a call statement emits both call and ret: its trace is call(l_f, ls), then the callee body's trace, then ret(l_f, l). " +
      "return e itself emits nothing; it only ends the body. Two reasons: ret must name the function l_f, which only the call rule knows; " +
      "and a body that falls through without return still gets its ret(l_f, undefined), so every call is closed by exactly one ret.");
    // One statement per row, descriptions in a second column (a table keeps the
    // columns aligned whatever font renders the subscripts).
    card(s, C, 0.6, 1.45, 6.2, 4.2, { fill: C.background2, name: "code" });
    pill(s, C, "Stmt", 5.83, 1.55, C.accent4, { w: 0.85, h: 0.28, fontSize: 10 });
    const stmts = [
      ["x := e", "assignment"],
      ["x := e₁ ⊕ e₂", "binary operation (fresh location)"],
      ["x := { p: e, … }", "object literal (fresh location)"],
      ["x := e.p", "static lookup", "lookup"],
      ["x := e₁[e₂]", "dynamic lookup", "lookup"],
      ["e.p := e", "static update", "update"],
      ["e₁[e₂] := e₃", "dynamic update", "update"],
      ["x := f(e₁, …, eₙ)", "call", "call … ret"],
      ["return e", "return (no action)"],
      ["if (e) {…} else {…}", "conditional"],
      ["while (e) {…}", "loop"],
      ["setTaint e", "mark attacker-controlled"],
      ["setSink e", "mark sink"],
    ];
    s.addTable(stmts.map(([st, d, act]) => [
      { text: st, options: { fontFace: L.CODE, fontSize: 13, color: C.text1 } },
      { text: act ? [{ text: d + "   " }, { text: "→ " + act, options: { color: C.accent1, bold: true } }] : d,
        options: { fontSize: 13, color: C.text1 } },
    ]), { x: 0.75, y: 1.55, w: 5.0, colW: [2.35, 2.65], rowH: 0.3, margin: [0, 0.05, 0, 0.05], valign: "middle",
      border: { type: "none" }, objectName: "statements" });
    const acts = [
      ["lookup(l₁, l₂, l₃)", "l₁ := l₂[l₃]"],
      ["update(l₁, l₂, l₃)", "l₁[l₂] := l₃"],
      ["call(l_f, [l₁, …, lₙ])", "function at l_f called"],
      ["ret(l_f, l)", "function at l_f returns l"],
    ];
    tx(s, "The four trace actions (Act)", { x: 7.2, y: 1.45, w: 5.5, h: 0.45, fontSize: 18, bold: true, color: C.text1 });
    acts.forEach(([a, m], k) => {
      const y = 2.0 + k * 0.92;
      card(s, C, 7.2, y, 5.5, 0.8, { fill: C.accent1, transparency: 88 });
      tx(s, L.sub(a), { x: 7.35, y: y + 0.08, w: 3.0, h: 0.6, fontFace: L.CODE, fontSize: 15, bold: true, color: C.accent1, valign: "middle" });
      tx(s, L.sub(m), { x: 10.3, y: y + 0.08, w: 2.3, h: 0.6, fontSize: 14, color: C.text1, valign: "middle" });
    });
    card(s, C, 0.6, 5.9, 12.1, 0.85, { fill: C.background2 });
    tx(s, [{ text: "Everything is a location ", options: { bold: true } },
           { text: "(Loc = Nat). Literals live at fixed canonical locations (litLoc); ⊕ and object literals allocate fresh ones. " +
                   "setTaint / setSink leave no trace action: they mark locations in a register." }],
      { x: 0.8, y: 5.98, w: 11.7, h: 0.7, fontSize: 15, color: C.text1 });
  }

  // 6 ── Traces
  {
    const s = D.slide("Traces: a tree, flattened once",
      "The semantics builds traces compositionally as a tree: empty, a single action, or a concatenation. " +
      "Queries talk about positions in the trace, so the tree is flattened once into a list, t = e.trc.toList, and all indexing uses that list.");
    code(s, C, "inductive Trc where\n  | emp\n  | act (a : Act)\n  | seq (t₁ t₂ : Trc)\n\ndef Trc.toList : Trc → List Act\n  | .emp       => []\n  | .act a     => [a]\n  | .seq t₁ t₂ => t₁.toList ++ t₂.toList",
      0.6, 1.45, 5.8, 3.05, { fontSize: 14, fullWidth: true });
    // tree diagram
    const nx = (x, y, t, col) => {
      s.addShape("ellipse", { x: x - 0.45, y, w: 0.9, h: 0.55, fill: { color: col }, line: { type: "none" } });
      s.addText(t, { x: x - 0.45, y, w: 0.9, h: 0.55, fontSize: 13, bold: true, color: C.background1, align: "center", valign: "middle", margin: 0, isTextBox: true });
    };
    nx(8.6, 1.6, "seq", C.text2);
    line(s, C, 8.4, 2.15, 7.6, 2.75); line(s, C, 8.8, 2.15, 9.6, 2.75);
    nx(7.5, 2.75, "act a", C.accent1);
    nx(9.7, 2.75, "seq", C.text2);
    line(s, C, 9.5, 3.3, 8.9, 3.9); line(s, C, 9.9, 3.3, 10.5, 3.9);
    nx(8.8, 3.9, "act b", C.accent1);
    nx(10.6, 3.9, "emp", C.accent4);
    arrow(s, C, 9.1, 4.6, 9.1, 5.15, { color: C.accent3, width: 2.5 });
    tx(s, "toList", { x: 9.25, y: 4.65, w: 1.2, h: 0.4, fontFace: L.CODE, fontSize: 14, color: C.accent3 });
    // A plain list: each index sits under its own element (boundaries come later).
    ["a", "b"].forEach((el, k) => {
      const x = 8.35 + k * 1.05;
      s.addShape("roundRect", { x, y: 5.3, w: 0.9, h: 0.5, rectRadius: 0.06, fill: { color: C.background2 },
        line: { color: C.accent4, width: 1 }, objectName: "element" });
      s.addText(el, { x, y: 5.3, w: 0.9, h: 0.5, fontFace: L.CODE, fontSize: 15, color: C.text1, align: "center", valign: "middle", margin: 0, isTextBox: true });
      s.addText(`t[${k}]`, { x, y: 5.85, w: 0.9, h: 0.3, fontFace: L.CODE, fontSize: 12, bold: true, color: C.accent4, align: "center", margin: 0, isTextBox: true });
    });
    s.addText("[", { x: 8.05, y: 5.25, w: 0.3, h: 0.6, fontFace: L.CODE, fontSize: 24, color: C.text2, align: "center", valign: "middle", margin: 0, isTextBox: true });
    s.addText("]", { x: 10.35, y: 5.25, w: 0.3, h: 0.6, fontFace: L.CODE, fontSize: 24, color: C.text2, align: "center", valign: "middle", margin: 0, isTextBox: true });
    tx(s, [{ text: "Queries index positions, so everything works on", options: { breakLine: true } }, { text: "t = e.trc.toList", options: { fontFace: L.CODE, bold: true } }],
      { x: 0.6, y: 5.0, w: 6.3, h: 0.8, fontSize: 16, color: C.text1 });
  }

  // 7 ── Observations
  {
    const s = D.slide("Observations: rigid facts about locations",
      "The second half of a record is the observation σ. It has four fields. val gives the value stored at a location, or none; " +
      "objects hold no value, only properties. dep gives the set of locations a location was computed from. ac and sk are sets: " +
      "attacker-controlled locations and sink locations. The key contrast: the trace is temporal, position p says what happened at step p; " +
      "the observation is rigid, one snapshot that applies at every position. This split runs through the whole development, " +
      "and reappears in FO-LTL as action atoms versus state atoms.");
    const rows = [
      ["val", "Loc → Option Val", "stored value (objects: none)"],
      ["dep", "Loc → LocSet", "locations it was computed from"],
      ["ac", "LocSet", "attacker-controlled locations"],
      ["sk", "LocSet", "sink locations"],
    ];
    rows.forEach(([f, t, m], k) => {
      const y = 1.5 + k * 0.72;
      card(s, C, 0.6, y, 6.6, 0.62, { fill: C.background2 });
      tx(s, f, { x: 0.75, y: y + 0.1, w: 0.7, h: 0.45, fontFace: L.CODE, fontSize: 16, bold: true, color: C.accent1 });
      tx(s, t, { x: 1.45, y: y + 0.1, w: 2.2, h: 0.45, fontFace: L.CODE, fontSize: 13, color: C.text2 });
      tx(s, m, { x: 3.65, y: y + 0.1, w: 3.5, h: 0.45, fontSize: 14, color: C.text1 });
    });
    tx(s, [{ text: "structure Obs where val; dep; ac; sk", options: { breakLine: true } }, { text: "structure Exec where trc : Trc; obs : Obs" }],
      { x: 0.6, y: 4.5, w: 6.6, h: 0.75, fontFace: L.CODE, fontSize: 14, color: C.accent4 });
    // temporal vs rigid diagram
    tx(s, "temporal", { x: 7.6, y: 1.5, w: 2, h: 0.4, fontSize: 15, bold: true, color: C.accent1 });
    timeline(s, C, 7.6, 2.0, 1.25, ["a₀", "a₁", "a₂", "a₃"], { fontSize: 14, indices: true });
    tx(s, "rigid", { x: 7.6, y: 3.25, w: 2, h: 0.4, fontSize: 15, bold: true, color: C.accent2 });
    card(s, C, 7.6, 3.7, 5.0, 0.75, { fill: C.accent2, transparency: 85, line: C.accent2 });
    tx(s, "σ  — one snapshot, valid at every position", { x: 7.75, y: 3.78, w: 4.8, h: 0.6, fontSize: 15, color: C.text1, valign: "middle" });
    card(s, C, 0.6, 5.6, 12.1, 0.95, { fill: C.accent3, transparency: 90 });
    tx(s, [{ text: "Why it matters: ", options: { bold: true, color: C.accent3 } },
           { text: "position p of the trace says what happened at step p; σ says what is true of locations, period. In FO-LTL this becomes the split between " },
           { text: "action atoms", options: { bold: true } }, { text: " (hold at one position) and " },
           { text: "state atoms", options: { bold: true } }, { text: " (hold at every position or none)." }],
      { x: 0.8, y: 5.6, w: 11.7, h: 0.95, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // 8 ── Why one final snapshot is enough
  {
    const s = D.slide("Why one final snapshot is enough",
      "Why can a single end-of-run snapshot stand for the whole run? For val and dep the answer is write-once: they are only written " +
      "at a freshly allocated location (Binary Operation), so a location goes from nothing to its final value exactly once. " +
      "Object initialisation only sets properties, never val. The heap's property map is overwritten destructively and is therefore " +
      "not in σ at all; it is only visible through lookup/update actions. For ac and sk the snapshot is not exact: they only grow, " +
      "so we know that a location was marked, but not when. Example: y := f(x); setTaint(x) matches Call(f,[x]) when ac(x). " +
      "Decision, kept: setTaint/setSink are intended for a harness prefix, where the two readings coincide.");
    box(s, C, 0.6, 1.45, 5.9, 2.35, "val, dep: write-once",
      ["Written only at a fresh allocation ([Binary Operation]); literals at initialisation",
       "So the final value is the value at every moment the location exists",
       "Objects get no value; the property map (overwritten!) is not in σ"],
      { titleColor: C.accent6, fontSize: 15 });
    box(s, C, 6.8, 1.45, 5.9, 2.35, "ac, sk: grow only",
      ["setTaint / setSink add a location, at any time",
       "The snapshot keeps that a location was marked, not when"],
      { titleColor: C.accent3, fontSize: 15 });
    // example timeline
    tx(s, "Example", { x: 0.6, y: 4.0, w: 2, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    code(s, C, "y := f(x);\nsetTaint(x)", 0.6, 4.45, 2.6, 0.85, { tag: false, fontSize: 14 });
    tx(s, "query", { x: 3.5, y: 4.0, w: 2, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    code(s, C, "Call(f, [x]) when ac(x)", 3.5, 4.45, 4.5, 0.6, { tag: false, fontSize: 14 });
    tx(s, "trace", { x: 0.6, y: 5.45, w: 1.0, h: 0.5, fontSize: 14, bold: true, color: C.text2, valign: "middle", margin: 0 });
    timeline(s, C, 1.5, 5.45, 2.2, ["call(f, [x])", "ret(f, y)"], { fontSize: 14, highlight: { 0: C.accent1 }, indices: true });
    s.addShape("roundRect", { x: 6.1, y: 5.45, w: 1.9, h: 0.5, rectRadius: 0.06, fill: { color: C.background1 }, line: { color: C.accent3, width: 1.5, dashType: "dash" } });
    tx(s, "setTaint(x)", { x: 6.1, y: 5.45, w: 1.9, h: 0.5, fontFace: L.CODE, fontSize: 14, color: C.accent3, align: "center", valign: "middle" });
    tx(s, "no action; marks x afterwards", { x: 5.85, y: 5.98, w: 2.4, h: 0.3, fontSize: 12, color: C.accent3, align: "center", margin: 0 });
    card(s, C, 8.3, 4.45, 4.4, 1.5, { fill: C.background2 });
    tx(s, [{ text: "Matches ", options: { bold: true, color: C.accent6 } },
           { text: "— ac(x) holds in the final σ, although x was not attacker-controlled at the call." }],
      { x: 8.45, y: 4.45, w: 4.15, h: 1.5, fontSize: 14, color: C.text1, valign: "middle" });
    pill(s, C, "DECISION · KEPT", 0.6, 6.45, C.accent4, { w: 1.9 });
    tx(s, "Meant for a harness prefix, where “marked at some point” and “marked before” coincide.",
      { x: 2.65, y: 6.41, w: 10.0, h: 0.4, fontSize: 15, color: C.text1, valign: "middle", margin: 0 });
  }

  // 9 ── From a run to an observation
  {
    const s = D.slide("From a run to an observation",
      "Obs.ofRun builds σ from the final heap and taint register. val, dep and sk are copied. ac is closed under reverse dependency: " +
      "a location is attacker-controlled if it was marked, or if it depends on a marked location. Why close ac here and not in the register? " +
      "Because setTaint can arrive after the locations that depend on it already exist; dep, by contrast, is only ever set on a fresh location " +
      "from sets that are already closed, so it stays transitive along a run (a theorem, BigStep.depInv, under an assumption on the initial register). " +
      "Obs.WF states the two closure properties. Crucially, no semantics assumes it: it is proved for real runs (BigStep.obs_wf). " +
      "This is a recurring design: the semantics is defined for every input; well-formedness is a separate hypothesis used only where needed.");
    code(s, C, "def Obs.ofRun (h : Heap) (δ : Reg) : Obs where\n  val := h.val\n  dep := δ.dep\n  ac  := fun l => δ.ac l ∨ ∃ l', δ.ac l' ∧ δ.dep l l'\n  sk  := δ.sk",
      0.6, 1.45, 7.3, 1.75, { fontSize: 13 });
    // dep graph
    const node = (x, y, label, col, sub) => {
      s.addShape("ellipse", { x, y, w: 1.0, h: 0.75, fill: { color: col }, line: { type: "none" } });
      s.addText(label, { x, y, w: 1.0, h: 0.75, fontSize: 16, bold: true, color: C.background1, align: "center", valign: "middle", margin: 0, isTextBox: true });
      if (sub) tx(s, sub.t || sub, { x: x - 0.45, y: sub.above ? y - 0.36 : y + 0.78, w: 1.9, h: 0.35, fontSize: 12, color: C.text2, align: "center" });
    };
    node(8.6, 1.75, "1100", C.accent3, { t: "b = a + one", above: true });
    node(10.6, 2.8, "15", C.accent3);
    tx(s, "literal 5 (a)", { x: 10.3, y: 3.6, w: 1.6, h: 0.35, fontSize: 12, color: C.text2, align: "center" });
    node(8.6, 3.25, "11", C.accent4, "literal 1 (one)");
    arrow(s, C, 9.6, 2.2, 10.6, 3.05, { color: C.text2 });
    arrow(s, C, 9.1, 2.5, 9.1, 3.25, { color: C.text2 });
    tx(s, "dep", { x: 10.05, y: 2.2, w: 0.7, h: 0.35, fontSize: 13, color: C.text2, fontFace: L.CODE });
    pill(s, C, "setTaint", 11.75, 3.01, C.accent3, { w: 0.95 });
    tx(s, "orange = ac in σ", { x: 10.4, y: 4.3, w: 2.3, h: 0.35, fontSize: 13, color: C.accent3, bold: true });
    box(s, C, 0.6, 3.45, 7.3, 1.85, "Why close ac here, not in the register?",
      "setTaint(a) can run after b := a + one already exists; b's dep mentions a, but nothing would add b to ac. dep, by contrast, is only set on a fresh location from closed sets, so it stays transitive (a theorem: BigStep.depInv).",
      { fontSize: 14 });
    card(s, C, 0.6, 5.55, 12.1, 1.0, { fill: C.accent2, transparency: 90, line: C.accent2 });
    tx(s, [{ text: "Obs.WF σ", options: { fontFace: L.CODE, bold: true } }, { text: " :  dep transitive  ∧  ac closed under reverse dep.  " },
           { text: "Recurring design: ", options: { bold: true, color: C.accent2 } },
           { text: "the semantics is defined for every record; well-formedness is a separate hypothesis, proved for real runs (BigStep.obs_wf) and used only where needed." }],
      { x: 0.8, y: 5.55, w: 11.7, h: 1.0, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // 10 ── Running example
  {
    const s = D.slide("Running example: pTaint",
      "This program from the test suite is our running example. It marks the sink function, taints a, computes b = a + 1 at a fresh location, " +
      "and calls the sink with b. The test instance puts literal n at 10 + n, so 5 is at 15 and 1 at 11; the function sink is at 204; " +
      "undefined is at 0; the fresh location from site 1 is 1100. The trace has two actions: the call of 204 with [1100], and its return of 0 " +
      "(sink falls through, so it returns undefined). In the observation 1100 is attacker-controlled only through dep.");
    code(s, C, "setSink (fid sink);\na := 5;\nsetTaint a;\none := 1;\nsix := 6;\nb := a + one;     // site 1\nr := sink(b)      // site 2",
      0.6, 1.45, 5.4, 2.35, { tag: "Core JS", tagW: 1.1, fontSize: 14 });
    tx(s, "Literal locations (test instance)", { x: 0.6, y: 3.95, w: 5.4, h: 0.4, fontSize: 15, bold: true, color: C.text2 });
    const lits = [["5", "15"], ["1", "11"], ["6", "16"], ["fid sink", "204"], ["undefined", "0"], ["a + one", "1100 (fresh)"]];
    lits.forEach(([v, l], k) => {
      const x = 0.6 + (k % 3) * 1.85, y = 4.4 + Math.floor(k / 3) * 0.85;
      card(s, C, x, y, 1.75, 0.75, { fill: C.background2 });
      tx(s, [{ text: v, options: { breakLine: true, bold: true } }, { text: "↦ " + l, options: { color: C.accent1 } }],
        { x: x + 0.05, y: y + 0.03, w: 1.65, h: 0.7, fontSize: 13, align: "center", color: C.text1, fontFace: L.CODE });
    });
    tx(s, "Trace  t", { x: 6.5, y: 1.45, w: 3, h: 0.4, fontSize: 16, bold: true, color: C.accent1 });
    // A list, indices under the elements (boundaries are only introduced in section 3).
    ["call(204, [1100])", "ret(204, 0)"].forEach((el, k) => {
      const x = 6.85 + k * 2.95;
      s.addShape("roundRect", { x, y: 1.95, w: 2.8, h: 0.55, rectRadius: 0.06, fill: { color: C.background2 },
        line: { color: C.accent4, width: 1 }, objectName: "element" });
      s.addText(el, { x, y: 1.95, w: 2.8, h: 0.55, fontFace: L.CODE, fontSize: 15, color: C.text1, align: "center", valign: "middle", margin: 0, isTextBox: true });
      s.addText(`t[${k}]`, { x, y: 2.55, w: 2.8, h: 0.3, fontFace: L.CODE, fontSize: 12, bold: true, color: C.accent4, align: "center", margin: 0, isTextBox: true });
    });
    s.addText("[", { x: 6.55, y: 1.92, w: 0.3, h: 0.6, fontFace: L.CODE, fontSize: 24, color: C.text2, align: "center", valign: "middle", margin: 0, isTextBox: true });
    s.addText("]", { x: 12.6, y: 1.92, w: 0.3, h: 0.6, fontFace: L.CODE, fontSize: 24, color: C.text2, align: "center", valign: "middle", margin: 0, isTextBox: true });
    tx(s, "Observation  σ", { x: 6.5, y: 3.35, w: 3, h: 0.4, fontSize: 16, bold: true, color: C.accent2 });
    const facts = [
      ["sk 204", "setSink"], ["ac 15", "setTaint (direct)"], ["ac 1100", "via dep 1100 ∋ 15"],
      ["dep 1100 = {15, 11}", "binary operation"], ["val 1100 = 6", "5 + 1"], ["¬ ac 11", "literal 1 is clean"],
    ];
    facts.forEach(([f, why], k) => {
      const x = 6.5 + (k % 2) * 3.1, y = 3.85 + Math.floor(k / 2) * 0.95;
      card(s, C, x, y, 3.0, 0.82, { fill: C.accent2, transparency: 90 });
      tx(s, [{ text: f, options: { fontFace: L.CODE, bold: true, breakLine: true } }, { text: why, options: { fontSize: 12, color: C.accent4 } }],
        { x: x + 0.12, y: y + 0.05, w: 2.8, h: 0.75, fontSize: 14, color: C.text1 });
    });
  }
};
