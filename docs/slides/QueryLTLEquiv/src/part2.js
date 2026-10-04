// Section 2: query syntax.
module.exports = function (D) {
  const { C, L } = D;
  const { tx, bullets, card, pill, code, math, arrow, line, box, timeline } = L;

  D.section("Query syntax", 2, "Queries describe vulnerable behaviours: an action pattern, guarded by an invariant and a mitigation",
    "Queries are defined in CoreJsQuerySyntax.lean. The file is pure syntax plus well-formedness predicates.");

  // grammar
  {
    const s = D.slide("The query grammar",
      "Queries are built from four layers. Query actions mirror trace actions but over variables instead of locations. " +
      "Patterns combine actions in time: empty, a single action, an invocation of another query, sequence, choice, and conjunction. " +
      "Predicates and invariants talk about the observation: sink, attacker-controlled, dependency, same value, has value. " +
      "A query body adds local variables, an invariant and an optional excluded pattern around a pattern. " +
      "Top: a query is a Query structure and its body a QBody structure. Bottom: every production of the grammar next to the Lean constructor " +
      "that represents it, with its type. Note that pattern and except are both Pat, while when is an Inv.");
    const line = (text, x, y, w, o = {}) => tx(s, L.sub(text), Object.assign({ x, y, w, h: 0.26, fontFace: L.CODE, fontSize: 13,
      color: C.text1, margin: 0, valign: "top" }, o));

    // Top band: query and body, and the two structures.
    card(s, C, 0.6, 1.45, 5.45, 1.75, { fill: C.background2 });
    pill(s, C, "syntax", 5.05, 1.55, C.accent4, { w: 0.9, h: 0.28, fontSize: 10 });
    line("query ::= Query Q(x₁, …, xₙ) { P }", 0.75, 1.62, 4.2);
    line("P ::= ⟨∃ y₁ … yₘ :⟩ F ⟨when I⟩ ⟨except F′⟩", 0.75, 1.98, 5.2);
    tx(s, "A query is a Query; its body P is a QBody.", { x: 0.75, y: 2.45, w: 5.2, h: 0.5, fontSize: 14, color: C.text2, margin: 0, valign: "middle" });
    card(s, C, 6.25, 1.45, 6.45, 1.75, { fill: C.accent1, transparency: 90 });
    pill(s, C, "Lean", 11.75, 1.55, C.accent4, { w: 0.85, h: 0.28, fontSize: 10 });
    const fields = (title, rows, x) => {
      line(title, x, 1.6, 3.2, { bold: true, color: C.accent1 });
      rows.forEach(([f, t], k) => {
        line("  " + f, x, 1.9 + k * 0.26, 1.1);
        line(": " + t, x + 1.1, 1.9 + k * 0.26, 1.9);
      });
    };
    fields("structure Query", [["name", "QName"], ["params", "List Var"], ["body", "QBody"]], 6.4);
    fields("structure QBody", [["locals", "List Var"], ["pattern", "Pat"], ["when", "Inv"], ["except", "Option Pat"]], 9.45);

    // Bottom band: each production next to its Lean constructor and type.
    // prodW: width of the grammar column; the constructor column follows, then the type.
    const prods = (rows, x0, w, prodW) => {
      const cx = x0 + 0.15 + prodW, tyx = cx + 0.75;
      tx(s, "grammar", { x: x0 + 0.15, y: 3.38, w: prodW, h: 0.3, fontSize: 12, bold: true, color: C.accent4, margin: 0 });
      tx(s, "Lean constructor : type", { x: cx, y: 3.38, w: w - prodW - 0.3, h: 0.3, fontSize: 12, bold: true, color: C.accent4, margin: 0 });
      card(s, C, x0, 3.7, w, 3.1, { fill: C.background2 });
      let y = 3.85;
      rows.forEach((r) => {
        if (!r) { y += 0.14; return; }
        const [prod, ctor, ty] = r;
        line(prod, x0 + 0.15, y, prodW, { fontSize: 12 });
        line(ctor, cx, y, 0.75, { fontSize: 12, bold: true, color: C.accent1 });
        line(": " + ty, tyx, y, x0 + w - tyx - 0.1, { fontSize: 12 });
        y += 0.245;
      });
    };
    prods([
      ["F ::= ε", "eps", "Pat"],
      ["    | a", "act", "QAct → Pat"],
      ["    | Q(z₁, …, zₖ)", "query", "QName → List Var → Pat"],
      ["    | F ; F", "seq", "Pat → Pat → Pat"],
      ["    | F ‖ F", "alt", "Pat → Pat → Pat"],
      ["    | F & F", "both", "Pat → Pat → Pat"],
      null,
      ["a ::= x₁ := x₂[x₃]", "lookup", "Var → Var → Var → QAct"],
      ["    | x₁[x₂] := x₃", "update", "Var → Var → Var → QAct"],
      ["    | Call(x_f, [x₁, …, xₙ])", "call", "Var → List Var → QAct"],
      ["    | Retn(x_f, x)", "retn", "Var → Var → QAct"],
    ], 0.6, 7.05, 3.0);
    prods([
      ["I ::= p", "pred", "Pred → Inv"],
      ["    | ¬I", "not", "Inv → Inv"],
      ["    | I ∨ I", "or", "Inv → Inv → Inv"],
      ["    | I ∧ I", "and", "Inv → Inv → Inv"],
      ["    | true", "tt", "Inv"],
      ["    | false", "ff", "Inv"],
      null,
      ["p ::= sk(x)", "sk", "Var → Pred"],
      ["    | ac(x)", "ac", "Var → Pred"],
      ["    | dep(x₁, x₂)", "dep", "Var → Var → Pred"],
      ["    | sv(x₁, x₂)", "sv", "Var → Var → Pred"],
      ["    | hv(x, c)", "hv", "Var → Val → Pred"],
    ], 7.85, 4.85, 1.9);
  }

  // anatomy
  {
    const s = D.slide("Anatomy of a query",
      "Read this example as: a sink f receives a value y derived from attacker input x, unless y was produced by the sanitizer s. " +
      "Parameters are the query's interface: a caller passes locations for them; at the top level they are the answer tuple, the locations " +
      "that witness a match. Locals are existentially quantified: the matcher chooses them, and they are private to the query. " +
      "The pattern is the behaviour being looked for. The invariant is a condition on the final snapshot, checked once. " +
      "The except pattern is the mitigation: if it occurs anywhere in the trace, this way of matching is ruled out. " +
      "In Lean, a Query has a name, its parameters and a body of type QBody; q.body is the whole ∃…when…except, and q.body.pattern is the pattern F.");
    // The query, left-aligned, one clause per line (∃ shares the pattern's line).
    card(s, C, 0.6, 1.45, 12.1, 1.65, { fill: C.background2 });
    const clause = (parts, last) => parts.map(([t, c], k) => ({ text: t,
      options: Object.assign({ color: c || C.text1, bold: !!c }, k === parts.length - 1 && !last ? { breakLine: true } : {}) }));
    tx(s, [
      ...clause([["Query Leak("], ["f, s, x", C.accent1], [") {"]]),
      ...clause([["  "], ["∃ y", C.accent2], [" : "], ["Call(f, [y])", C.accent3]]),
      ...clause([["  when "], ["sk(f) ∧ dep(y, x) ∧ ac(x)", L.WHEN]]),
      ...clause([["  except "], ["Retn(s, y)", L.EXCEPT]]),
      ...clause([["}"]], true),
    ], { x: 0.9, y: 1.52, w: 11.5, h: 1.5, fontFace: L.CODE, fontSize: 16, margin: 0, valign: "middle" });
    const ann = [
      ["Parameters", C.accent1, "The interface. A caller passes locations for them; at top level they are the answer tuple."],
      ["Locals ∃", C.accent2, "Chosen by the matcher; private to the query."],
      ["Pattern", C.accent3, "The behaviour looked for, matched in time over the trace."],
      ["when", L.WHEN, "Invariant on the final snapshot σ, checked once."],
      ["except", L.EXCEPT, "Mitigation: if it occurs anywhere in the trace, this match is ruled out."],
    ];
    ann.forEach(([h, col, b], k) => {
      const x = 0.6 + k * 2.44;
      card(s, C, x, 3.3, 2.3, 1.65, { fill: col, transparency: 88, line: col });
      tx(s, h, { x: x + 0.12, y: 3.38, w: 2.1, h: 0.4, fontSize: 16, bold: true, color: col });
      tx(s, b, { x: x + 0.12, y: 3.8, w: 2.1, h: 1.1, fontSize: 14, color: C.text1 });
    });
    code(s, C, "structure QBody where\n  locals  : List Var := []\n  pattern : Pat\n  when    : Inv := .tt\n  except  : Option Pat := none",
      0.6, 5.15, 5.75, 1.65, { fontSize: 14 });
    code(s, C, "structure Query where\n  name   : QName\n  params : List Var   -- the interface\n  body   : QBody      -- the query body P",
      6.6, 5.15, 6.1, 1.65, { fontSize: 14, fullWidth: true });
  }

  // programs are lists
  {
    const s = D.slide("Query programs are lists",
      "A query program is a list, and a query may only invoke queries later in the list. Why not a map with arbitrary recursion? " +
      "Two reasons. Lean: except negates satisfaction. If invocation were resolved inside the inductive that defines satisfaction, " +
      "a negated occurrence of the relation would appear in its own definition, which violates strict positivity. " +
      "Semantics: Q() { F except Q() } says Q holds iff F holds and Q does not; when F holds there is no consistent truth value. " +
      "Consequence: no recursion, so no Kleene star. Data-flow chains are covered by dep, which is already transitive; unbounded heap paths are not expressible.");
    const qs = ["Main", "Sink", "SanCalled", "Helper"];
    qs.forEach((q, k) => {
      const x = 0.9 + k * 3.0;
      card(s, C, x, 1.8, 2.2, 0.9, { fill: C.accent1, transparency: 85, line: C.accent1 });
      tx(s, q, { x, y: 1.8, w: 2.2, h: 0.9, fontFace: L.CODE, fontSize: 17, bold: true, color: C.accent1, align: "center", valign: "middle" });
    });
    arrow(s, C, 3.1, 2.25, 3.9, 2.25, { color: C.accent6, width: 2.5 });
    arrow(s, C, 6.1, 2.25, 6.9, 2.25, { color: C.accent6, width: 2.5 });
    arrow(s, C, 2.0, 2.9, 7.9, 2.9, { color: C.accent6, width: 1.5, dash: "dash" });
    arrow(s, C, 10.0, 1.5, 2.0, 1.5, { color: C.accent5, width: 1.5 });
    tx(s, "✗", { x: 5.75, y: 1.25, w: 0.5, h: 0.5, fontSize: 22, bold: true, color: C.accent5, align: "center", valign: "middle", margin: 0 });
    tx(s, "may invoke only queries to the right", { x: 0.9, y: 3.0, w: 6, h: 0.4, fontSize: 14, color: C.accent6, italic: true });
    box(s, C, 0.6, 3.6, 5.95, 2.1, "Lean: strict positivity",
      "except negates satisfaction. Resolving invocation inside the inductive that defines Pat.Sat would put ¬ Pat.Sat in its own definition: rejected by Lean. So Pat.Sat takes an interpretation Θ as a parameter, built from the list by structural recursion.",
      { fontSize: 14, titleColor: C.accent2 });
    box(s, C, 6.75, 3.6, 5.95, 2.1, "Semantics: a paradox",
      [{ text: "Query Q() { F except Q() }", options: { fontFace: L.CODE, bold: true, breakLine: true } },
       { text: "Q holds ⇔ F holds and Q does not. When F holds: “this sentence is false”. Recursion through negation has no meaning without extra machinery." }],
      { fontSize: 14, titleColor: C.accent5, bullets: false });
    card(s, C, 0.6, 5.95, 12.1, 0.8, { fill: C.background2 });
    tx(s, [{ text: "Consequence: ", options: { bold: true } }, { text: "no recursion, so no Kleene star. Data-flow chains are covered by dep (already transitive); unbounded heap paths are not expressible." }],
      { x: 0.8, y: 6.03, w: 11.7, h: 0.65, fontSize: 15, color: C.text1 });
  }

  // well-formedness
  {
    const s = D.slide("Well-formedness, kept separate",
      "Three predicates single out the sensible queries. Declared: all variables used are parameters or locals, with no duplicates. " +
      "CallsOK: every invoked name exists later in the program with the right arity. QProg.WF: every query is well-formed with respect " +
      "to the queries after it, and names are distinct. The semantics does not assume any of these. An undeclared variable just denotes location 0; " +
      "an invocation of a missing query is simply false. Same pattern as Obs.WF: total semantics, separate sanity conditions. " +
      "The translation proof is where WF is actually needed.");
    code(s, C,
      "def Query.Declared (q : Query) : Prop :=\n  (q.params ++ q.body.locals).Nodup ∧\n  ∀ v ∈ q.body.vars,\n    v ∈ q.params ∨ v ∈ q.body.locals\n\n" +
      "def Query.CallsOK (Δ : QProg) (q : Query) : Prop :=\n  ∀ c ∈ q.body.calls, ∃ q',\n    QProg.find? Δ c.1 = some q' ∧\n    q'.params.length = c.2.length\n\n" +
      "def QProg.WF : QProg → Prop\n  | []     => True\n  | q :: Δ => (q.Declared ∧ q.CallsOK Δ) ∧\n      QProg.find? Δ q.name = none ∧ QProg.WF Δ",
      0.6, 1.45, 7.6, 3.75, { fontSize: 13 });
    box(s, C, 8.5, 1.45, 4.2, 1.75, "Never assumed",
      ["undeclared variable ↦ location 0", "missing callee ↦ invocation is false", "wrong arity ↦ false"],
      { fontSize: 15, titleColor: C.accent1 });
    box(s, C, 8.5, 3.4, 4.2, 1.8, "Where WF is used",
      "The translation proof: callees must exist (to inline them) and be self-contained (Declared).",
      { fontSize: 14, titleColor: C.accent3 });
    card(s, C, 0.6, 5.45, 12.1, 1.0, { fill: C.accent2, transparency: 90, line: C.accent2 });
    tx(s, [{ text: "Same pattern as Obs.WF: ", options: { bold: true, color: C.accent2 } }, { text: "the semantics is total; well-formedness is a separate condition, assumed only by the theorems that need it." }],
      { x: 0.8, y: 5.45, w: 11.7, h: 1.0, fontSize: 15, color: C.text1, valign: "middle" });
  }
};
