// Section 3: query semantics.
module.exports = function (D) {
  const { C, L } = D;
  const { tx, bullets, card, pill, code, math, arrow, line, box, timeline } = L;

  D.section("Query semantics", 3, "When does a pattern match a stretch of the trace?",
    "CoreJsQuerySemantics.lean. The central judgement is t, σ, ξ ⊨ F : i ⇝ j.");

  // boundaries
  {
    const s = D.slide("Positions are boundaries",
      "Positions are boundaries between actions, not the actions themselves. Boundary 0 is before the first action, boundary n after the last. " +
      "The judgement t, σ, ξ ⊨ F : i ⇝ j says: F is performed using actions from t[i] up to and including t[j-1]; j is one past F's last action. " +
      "So 'after boundary i' and 'from action index i onwards' are the same thing. ε matches i ⇝ i using no action. " +
      "t is the trace (flattened), σ the observation, ξ the valuation from query variables to locations. t and σ never change during matching; " +
      "only the window i, j and the valuation do.");
    timeline(s, C, 1.2, 1.9, 2.4, ["t[0]", "t[1]", "t[2]", "t[3]"], { fontSize: 16, highlight: { 1: C.accent1, 2: C.accent1 },
      spans: [{ from: 1, to: 3, label: "F : 1 ⇝ 3   uses t[1], t[2]", color: C.accent1 }, { from: 4, to: 4, label: "  ε : 4 ⇝ 4", color: C.accent4, row: 1 }] });
    card(s, C, 0.6, 4.35, 12.1, 0.95, { fill: C.accent1, transparency: 90, line: C.accent1 });
    tx(s, [{ text: "t, σ, ξ ⊨ F : i ⇝ j", options: { fontFace: L.MATH, bold: true, color: C.accent1 } },
           { text: "    “F is performed after boundary i, and its last action is t[j − 1]”" }],
      { x: 0.8, y: 4.42, w: 11.7, h: 0.8, fontSize: 18, color: C.text1, valign: "middle" });
    const legend = [["t", "the trace, e.trc.toList"], ["σ", "the observation, e.obs"], ["ξ", "valuation Var → Loc"], ["i, j", "boundaries, 0 … |t|"]];
    legend.forEach(([a, b], k) => {
      const x = 0.6 + k * 3.05;
      card(s, C, x, 5.55, 2.9, 1.15, { fill: C.background2 });
      tx(s, [{ text: a, options: { fontFace: L.MATH, fontSize: 22, bold: true, color: C.accent1, breakLine: true } }, { text: b, options: { fontSize: 14 } }],
        { x: x + 0.15, y: 5.6, w: 2.65, h: 1.05, color: C.text1 });
    });
  }

  // actions and sequencing
  {
    const s = D.slide("Actions and sequencing",
      "The action rule requires i < j, not j = i + 1: the action may occur at any later position. Matching is subsequence matching; gaps are allowed. " +
      "Sequencing starts F₂ where F₁ ended, so every action of F₂ comes strictly after F₁'s last action. " +
      "In the example, the call is at position 1, a lookup sits in between, and the return at position 3 still completes the sequence. " +
      "Q: is it 'after position i' or 'from position i'? The same thing, because positions are boundaries.");
    math(s, C, [
      { text: "ε :  i ⇝ i", options: { breakLine: true } },
      { text: "a :  i ⇝ j    if  i < j ≤ |t|  and  t[j − 1] = a under ξ", options: { breakLine: true } },
      { text: "F₁ ; F₂ :  i ⇝ j    if  F₁ : i ⇝ k  and  F₂ : k ⇝ j" }],
      { x: 0.6, y: 1.4, w: 6.9, h: 1.85, fontSize: 18, lineSpacingMultiple: 1.2 });
    code(s, C, "| act {a i j} :\n    i < j → j ≤ t.length →\n    t[j - 1]? = some (a.inst ξ) →\n    Pat.Sat Θ t σ ξ (.act a) i j",
      7.6, 1.45, 5.1, 1.65, { fontSize: 13 });
    tx(s, "Call(f, [x]) ; Retn(f, y)    with  ξ = [f ↦ 7, x ↦ 5, y ↦ 9]", { x: 0.6, y: 3.35, w: 12.1, h: 0.45, fontSize: 17, bold: true, fontFace: L.CODE, color: C.text1 });
    timeline(s, C, 0.9, 4.0, 2.75, ["lookup(…)", "call(7, [5])", "lookup(…)", "ret(7, 9)"], { fontSize: 14, highlight: { 1: C.accent1, 3: C.accent1 },
      spans: [{ from: 0, to: 2, label: "Call : 0 ⇝ 2", color: C.accent1 }, { from: 2, to: 4, label: "Retn : 2 ⇝ 4", color: C.accent3 },
              { from: 0, to: 4, label: "Call ; Retn : 0 ⇝ 4", color: C.text2, row: 1 }] });
    pill(s, C, "subsequence matching: gaps allowed", 0.6, 6.4, C.accent1, { w: 3.9 });
  }

  // choice and conjunction
  {
    const s = D.slide("Choice and conjunction",
      "Choice matches if either side matches with the same window. Conjunction starts both sides at the same i, in either order, " +
      "and ends at the later of the two end points. Why max? The end boundary is where the next thing may start, so a conjunction is only " +
      "complete once its later side is. With min, (F₁ & F₂) ; F₃ could place F₃ before F₂ happened. " +
      "On the reversed trace, & still matches while ; does not. One action may serve both sides, so a & a matches exactly when a does.");
    math(s, C, [
      { text: "F₁ ‖ F₂ :  i ⇝ j    if  F₁ : i ⇝ j  or  F₂ : i ⇝ j", options: { breakLine: true } },
      { text: "F₁ & F₂ :  i ⇝ max(j₁, j₂)    if  F₁ : i ⇝ j₁  and  F₂ : i ⇝ j₂" }],
      { x: 0.6, y: 1.45, w: 12.1, h: 1.0, fontSize: 19, lineSpacingMultiple: 1.25 });
    tx(s, "Call(g,[x]) & Lookup(y,x,p)", { x: 0.6, y: 2.6, w: 6, h: 0.4, fontFace: L.CODE, fontSize: 15, bold: true, color: C.text1 });
    timeline(s, C, 0.9, 3.15, 2.6, ["call(7, [5])", "lookup(3, 5, 4)"], { fontSize: 14, highlight: { 0: C.accent1, 1: C.accent1 },
      spans: [{ from: 0, to: 1, label: "j₁ = 1", color: C.accent1 }, { from: 0, to: 2, label: "j₂ = 2  →  & : 0 ⇝ 2", color: C.accent3, row: 1 }] });
    tx(s, "reversed trace", { x: 7.0, y: 2.6, w: 5, h: 0.4, fontSize: 15, bold: true, color: C.text2 });
    timeline(s, C, 7.2, 3.15, 2.6, ["lookup(3, 5, 4)", "call(7, [5])"], { fontSize: 14, highlight: { 0: C.accent1, 1: C.accent1 } });
    card(s, C, 7.0, 4.25, 5.7, 1.0, { fill: C.background2 });
    tx(s, [{ text: "&  matches  ", options: { color: C.accent6, bold: true } }, { text: "(order free)    " },
           { text: ";  fails  ", options: { color: C.accent5, bold: true } }, { text: "(no lookup after the call)" }],
      { x: 7.15, y: 4.35, w: 5.4, h: 0.8, fontSize: 15, color: C.text1, valign: "middle" });
    box(s, C, 0.6, 5.35, 6.0, 1.4, "Why max?", "The end is where the next pattern may start: & is done only when its later side is.", { fontSize: 15, titleColor: C.accent3 });
    box(s, C, 6.8, 5.35, 5.9, 1.4, "One action, both sides", "a & a matches whenever a does (Pat.Sat.both_idem).", { fontSize: 15, titleColor: C.accent1 });
  }

  // no pairing
  {
    const s = D.slide("Consequence: calls and returns are not paired",
      "Because matching is by subsequence, nothing ties a return to the call it belongs to. Here the pattern pairs the first call with the second " +
      "invocation's return: x = a, y = r₂. There is also no way to say 'immediately next' or 'with nothing of kind X in between'. " +
      "Decision, kept: this over-approximates, giving more matches and so potentially more false positives, which is acceptable for a " +
      "vulnerability-finding language.");
    tx(s, "Call(f, [x]) ; Retn(f, y)", { x: 0.6, y: 1.45, w: 6, h: 0.45, fontFace: L.CODE, fontSize: 17, bold: true, color: C.text1 });
    timeline(s, C, 0.9, 2.2, 2.85, ["call(f, [a])", "ret(f, r₁)", "call(f, [b])", "ret(f, r₂)"], { fontSize: 15, highlight: { 0: C.accent3, 3: C.accent3 },
      spans: [{ from: 0, to: 4, label: "matches with  x = a,  y = r₂", color: C.accent3 }] });
    box(s, C, 0.6, 4.4, 5.9, 1.6, "Not expressible", ["“immediately next”", "“with nothing of kind X in between”", "pairing a return with its own call"], { fontSize: 15, titleColor: C.accent5 });
    box(s, C, 6.8, 4.4, 5.9, 1.6, "Accepted", "An over-approximation: more matches, so potentially more false positives. Acceptable for finding vulnerabilities.", { fontSize: 15, titleColor: C.accent6 });
    pill(s, C, "DECISION · KEPT", 0.6, 6.25, C.accent4, { w: 1.9 });
  }

  // predicates
  {
    const s = D.slide("Predicates read the snapshot",
      "Predicates are evaluated on σ under the valuation; there is nothing temporal about them. sv requires both values to be defined and equal. " +
      "Why not simply compare σ.val at both locations? Undefined is none, and none = none. Objects have no value, so the naive definition would say " +
      "any two objects hold the same value. Invariants are Boolean combinations of predicates, checked once per match.");
    code(s, C,
      "def Pred.Sat (σ : Obs) (ξ : LEnv) : Pred → Prop\n" +
      "  | .sk x      => σ.sk (ξ x)\n" +
      "  | .ac x      => σ.ac (ξ x)\n" +
      "  | .dep x₁ x₂ => σ.dep (ξ x₁) (ξ x₂)\n" +
      "  | .sv x₁ x₂  => ∃ v, σ.val (ξ x₁) = some v\n" +
      "                     ∧ σ.val (ξ x₂) = some v\n" +
      "  | .hv x c    => σ.val (ξ x) = some c",
      0.6, 1.45, 7.0, 3.0, { fontSize: 14 });
    box(s, C, 7.9, 1.45, 4.8, 3.0, "Why sv needs defined values",
      [{ text: "Naive:  σ.val l₁ = σ.val l₂", options: { fontFace: L.CODE, breakLine: true } },
       { text: "Objects have no value (none), and none = none: any two objects would hold “the same value”.", options: {} }],
      { fontSize: 15, titleColor: C.accent5, bullets: false });
    card(s, C, 0.6, 4.75, 12.1, 1.15, { fill: C.background2 });
    tx(s, [{ text: "dep(x₁, x₂)", options: { fontFace: L.CODE, bold: true } }, { text: " is plain membership ξ x₂ ∈ σ.dep (ξ x₁): no closure in the semantics. Transitivity is a property of the observation (Obs.WF), not of the query language." }],
      { x: 0.8, y: 4.85, w: 11.7, h: 0.95, fontSize: 15, color: C.text1 });
    card(s, C, 0.6, 6.05, 12.1, 0.75, { fill: C.accent1, transparency: 88 });
    tx(s, [{ text: "Invariants ", options: { bold: true, color: C.accent1 } }, { text: "I ::= p | ¬I | I ∨ I | I ∧ I | true | false are checked once per match, on σ: nothing temporal." }],
      { x: 0.8, y: 6.05, w: 11.7, h: 0.75, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // QBody.Sat
  {
    const s = D.slide("Query bodies: QBody.Sat",
      "This is QBody.Sat, the satisfaction of ∃ y₁ … yₘ : F when I except F'. It has one constructor with five premises. " +
      "Premises 1 and 2 implement the existential: proving the judgement means choosing a list ls of locations for the locals, and ξ' is ξ " +
      "with the locals overwritten. Nothing restricts ls to locations that occur in the trace. From premise 2 on, everything uses ξ': the pattern, " +
      "the invariant and the except all see the same choice of locals. Premise 5 reads: if there is an except pattern F', then F' matches from 0 to no k. " +
      "The '∀ F', except = some F' →' is just Lean's way of unwrapping an Option; there is at most one F'. " +
      "Worked example: Sink(a) { ∃ g : Call(g,[a]) when sk(g) } on [lookup, call(7,[5])] with a ↦ 5 and sk 7: choose ls = [7].");
    code(s, C,
      "inductive QBody.Sat (Θ : Interp) (t : List Act)\n" +
      "    (σ : Obs) : LEnv → QBody → Nat → Nat → Prop where\n" +
      "  | mk {ξ ξ' P ls i j} :\n" +
      "      ls.length = P.locals.length →          -- (1)\n" +
      "      ξ' = ξ.bind P.locals ls →              -- (2)\n" +
      "      Pat.Sat Θ t σ ξ' P.pattern i j →       -- (3)\n" +
      "      Inv.Sat σ ξ' P.when →                  -- (4)\n" +
      "      (∀ F', P.except = some F' →\n" +
      "         ∀ k, ¬ Pat.Sat Θ t σ ξ' F' 0 k) →   -- (5)\n" +
      "      QBody.Sat Θ t σ ξ P i j",
      0.6, 1.45, 7.0, 3.3, { fontSize: 13, fullWidth: true });
    tx(s, [{ text: "QBody.Sat Θ t σ ξ P i j", options: { fontFace: L.CODE, bold: true } },
           { text: ":  under ξ, the body P matches t from i to j (Θ answers invocations). One constructor, mk, with five premises." }],
      { x: 0.75, y: 4.08, w: 6.7, h: 0.6, fontSize: 13, color: C.text2, margin: 0, valign: "middle" });
    // One card per premise: what it says, then its formula on a line of its own.
    const steps = [
      ["(1)(2)", "choose locations ls for the locals (the ∃)", "ξ′ = ξ[y₁…yₘ ↦ ls]", C.accent2],
      ["(3)", "the pattern matches", "F : i ⇝ j   under ξ′", C.accent3],
      ["(4)", "the invariant holds on the snapshot", "σ, ξ′ ⊨ I", L.WHEN],
      ["(5)", "the except pattern, if any, matches nowhere", "∀ k.  ¬ (F′ : 0 ⇝ k)", L.EXCEPT],
    ];
    steps.forEach(([n, what, f, col], k) => {
      const y = 1.45 + k * 0.85;
      card(s, C, 7.85, y, 4.85, 0.75, { fill: col, transparency: 88, line: col });
      tx(s, [{ text: n + "  ", options: { bold: true, color: col } }, { text: what, options: { breakLine: true } },
             { text: f, options: { fontFace: L.MATH, fontSize: 15 } }],
        { x: 7.98, y, w: 4.6, h: 0.75, fontSize: 13, color: C.text1, valign: "middle", margin: 0 });
    });

    // Worked example: the query, its trace, and the five premises checked.
    tx(s, "Example", { x: 0.6, y: 4.95, w: 2, h: 0.35, fontSize: 15, bold: true, color: C.text1, margin: 0 });
    code(s, C, "Sink(a) {\n  ∃ g : Call(g, [a])\n  when sk(g) }", 0.6, 5.35, 3.6, 1.0, { tag: false, fontSize: 13 });
    tx(s, [{ text: "a ↦ 5", options: { fontFace: L.MATH } }, { text: "  (the argument),  " }, { text: "σ.sk 7", options: { fontFace: L.MATH } }],
      { x: 0.6, y: 6.42, w: 3.8, h: 0.35, fontSize: 13, color: C.text2, margin: 0 });
    tx(s, "trace", { x: 4.55, y: 4.95, w: 2, h: 0.35, fontSize: 15, bold: true, color: C.text1, margin: 0 });
    timeline(s, C, 4.65, 5.45, 1.75, ["lookup(1,2,3)", "call(7, [5])"], { fontSize: 12, highlight: { 1: C.accent3 },
      spans: [{ from: 0, to: 2, label: "Call(g, [a]) : 0 ⇝ 2", color: C.accent3 }] });
    tx(s, "premises", { x: 8.45, y: 4.95, w: 2, h: 0.35, fontSize: 15, bold: true, color: C.text1, margin: 0 });
    const checks = [
      ["(1)(2)", "ls = [7],  ξ′ = [a ↦ 5, g ↦ 7]", C.accent2],
      ["(3)", "t[1] = call(7, [5])", C.accent3],
      ["(4)", "sk(g):  σ.sk 7", L.WHEN],
      ["(5)", "no except", L.EXCEPT],
    ];
    checks.forEach(([n, f, col], k) => {
      tx(s, [{ text: n + "  ", options: { bold: true, color: col, fontFace: "Calibri" } }, { text: f, options: { fontFace: L.MATH } },
             { text: "  ✓", options: { color: C.accent6, bold: true } }],
        { x: 8.45, y: 5.35 + k * 0.36, w: 4.25, h: 0.34, fontSize: 14, color: C.text1, margin: 0, valign: "middle" });
    });
  }

  // except whole trace
  {
    const s = D.slide("except is checked over the whole trace",
      "The excluded pattern is matched from boundary 0, with any end point: it must occur nowhere in the trace, before, during or after the " +
      "positive match. Why: position independence. The guard does not depend on where its query starts, which is what lets the FO-LTL translation " +
      "place the guard exactly where the query occurs, and what keeps the & rule exact. It also gives lower_start, later. " +
      "Is this a source of false negatives, e.g. a sanitization after the sink? Not in the intended idiom: a sanitizer is modelled by its output, " +
      "Retn(san, y). Locations are write-once, so 'y was returned by san' is a timeless fact. If y was returned by san, that return necessarily " +
      "happened before y could be used. Decision, kept.");
    timeline(s, C, 0.9, 1.95, 2.25, ["…", "call(f, [y])", "…", "…", "ret(san, y′)"], { fontSize: 14, highlight: { 1: C.accent3, 4: L.EXCEPT },
      spans: [{ from: 1, to: 2, label: "pattern  i ⇝ j", color: C.accent3 }, { from: 0, to: 5, label: "except searched over 0 ⇝ k, any k: the whole trace", color: L.EXCEPT, row: 1 }] });
    code(s, C, "(∀ F', P.except = some F' → ∀ k, ¬ Pat.Sat Θ t σ ξ' F' 0 k)", 0.6, 4.05, 12.1, 0.6, { fontSize: 15, tag: false });
    box(s, C, 0.6, 4.9, 5.9, 1.85, "Why",
      ["Guard independent of where the query starts", "So the translation can place it in place (atStart)", "Keeps tr(F₁ & F₂) = tr F₁ ∧ tr F₂ exact"],
      { fontSize: 14, titleColor: C.accent3 });
    box(s, C, 6.8, 4.9, 5.9, 1.85, "Sanitizers: the output idiom",
      [{ text: "Leak(f, s, x) { ∃ y: Call(f, [y]) …", options: { fontFace: L.CODE, fontSize: 12, breakLine: true } },
       { text: "               except Retn(s, y) }", options: { fontFace: L.CODE, fontSize: 12, breakLine: true } },
       { text: "Locations are write-once: “y was returned by s” is timeless, so checking the whole trace is exactly right." }],
      { fontSize: 14, titleColor: C.accent6, bullets: false });
  }

  // quantifier pitfall
  {
    const s = D.slide("Pitfall: where the quantifier sits",
      "A frequent mistake. To say 'f was called, and san was never called with any argument', one might write ∃ x, y : Call(f,[x]) except Call(san,[y]). " +
      "But y is existential and chosen once for the whole body. The matcher can pick a y that was never passed to san, say an unused location, " +
      "and the except is vacuously satisfied. The quantifiers are in the wrong order: this is ∃y. ¬San(y), but we want ¬∃y. San(y). " +
      "The grammar expresses the latter through invocation: an invoked query's locals are private and quantified inside the negation. " +
      "So invocation does two jobs: reuse, and scoping a quantifier under except. Note also that Call takes a variable in callee position; " +
      "which function it is gets pinned down by hv(g, fid f).");
    box(s, C, 0.6, 1.45, 5.9, 2.45, "Wrong",
      [{ text: "∃ x, y : Call(f, [x]) except Call(san, [y])", options: { fontFace: L.CODE, fontSize: 14, bold: true, breakLine: true } },
       { text: "y is chosen once, by the matcher. Pick any y never passed to san: the except is vacuous.", options: { breakLine: true } },
       { text: "This is  ∃y. ¬San(y)", options: { fontFace: L.MATH, color: C.accent5, bold: true } }],
      { fontSize: 15, titleColor: C.accent5, bullets: false, line: C.accent5 });
    box(s, C, 6.8, 1.45, 5.9, 2.45, "Right: invoke a query",
      [{ text: "SanCalled() {", options: { fontFace: L.CODE, fontSize: 13, breakLine: true } },
       { text: "  ∃ s, z : Call(s, [z]) when hv(s, fid san) }", options: { fontFace: L.CODE, fontSize: 13, breakLine: true } },
       { text: "Unsanitized() {", options: { fontFace: L.CODE, fontSize: 13, breakLine: true } },
       { text: "  ∃ g, y : Call(g, [y]) when hv(g, fid f)", options: { fontFace: L.CODE, fontSize: 13, breakLine: true } },
       { text: "  except SanCalled() }", options: { fontFace: L.CODE, fontSize: 13, breakLine: true } },
       { text: "This is  ¬∃z. San(z)", options: { fontFace: L.MATH, color: C.accent6, bold: true } }],
      { fontSize: 15, titleColor: C.accent6, bullets: false, line: C.accent6 });
    tx(s, "The computed translation shows the ∃ of SanCalled's locals inside the ¬ (fresh tags #2, #3):", { x: 0.6, y: 4.1, w: 12.1, h: 0.4, fontSize: 15, color: C.text1 });
    code(s, C, "(∃#0. (∃#1. (hv(#0, fid f) ∧ (atStart(¬(∃#2. (∃#3. (hv(#2, fid san) ∧\n   F (call(#2, [#3]) ∧ X ⊤))))) ∧ F (call(#0, [#1]) ∧ X ⊤)))))",
      0.6, 4.55, 12.1, 0.95, { fontSize: 14, tag: "#guard", tagW: 1.0, tagColor: C.accent2 });
    card(s, C, 0.6, 5.75, 12.1, 0.7, { fill: C.background2 });
    tx(s, [{ text: "Invocation does two jobs: ", options: { bold: true } }, { text: "reuse, and scoping a quantifier under except. Pin callees with hv(g, fid f)." }],
      { x: 0.8, y: 5.75, w: 11.7, h: 0.7, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // Θ oracle
  {
    const s = D.slide("Invocation: the oracle Θ",
      "Pattern satisfaction is parametric in an interpretation Θ. Its type is QName → List Loc → Nat → Nat → Prop: a function returning a proposition, " +
      "that is, a relation, a set of 4-tuples. Θ Q ls i j reads: query Q, with its parameters set to the locations ls, matches the trace from i to j. " +
      "Θ is just a variable naming such a relation; Θ Q ls i j is function application. When Pat.Sat meets Q(z₁, …, zₖ) it does not evaluate Q: " +
      "it resolves the caller's variables to locations through ξ and asks Θ. The callee never sees the caller's variable names. " +
      "Worked example: u ↦ 5, w ↦ 9 in the caller. Sink(u) asks Θ Sink [5] 0 2, which holds; Sink(w) asks Θ Sink [9] 0 2, which does not; " +
      "[5, 6] fails the arity check.");
    code(s, C, "abbrev Interp :=\n  QName → List Loc → Nat → Nat → Prop\n\n| query {Q zs i j} :\n    Θ Q (zs.map ξ) i j →\n    Pat.Sat Θ t σ ξ (.query Q zs) i j",
      0.6, 1.45, 6.3, 2.2, { fontSize: 14 });
    card(s, C, 7.2, 1.45, 5.5, 2.2, { fill: C.accent3, transparency: 90, line: C.accent3 });
    tx(s, [{ text: "Θ Q ls i j", options: { fontFace: L.MATH, bold: true, color: C.accent3, fontSize: 20, breakLine: true } },
           { text: "“query Q, parameters ↦ ls, matches from i to j”", options: { italic: true, breakLine: true } },
           { text: "Θ is a relation (a set of tuples); Θ Q ls i j is function application, written without parentheses." }],
      { x: 7.4, y: 1.55, w: 5.1, h: 2.0, fontSize: 15, color: C.text1 });
    // flow
    const y = 4.1;
    card(s, C, 0.6, y, 3.0, 1.3, { fill: C.accent1, transparency: 88, line: C.accent1 });
    tx(s, [{ text: "caller", options: { bold: true, color: C.accent1, breakLine: true } }, { text: "ξ = [u ↦ 5, w ↦ 9]", options: { fontFace: L.MATH, breakLine: true } }, { text: "pattern  Sink(u)", options: { fontFace: L.CODE } }],
      { x: 0.75, y: y + 0.08, w: 2.75, h: 1.15, fontSize: 14, color: C.text1 });
    arrow(s, C, 3.6, y + 0.65, 4.6, y + 0.65, { color: C.accent3, width: 2.5 });
    tx(s, "zs.map ξ", { x: 3.55, y: y + 0.2, w: 1.1, h: 0.35, fontFace: L.CODE, fontSize: 12, color: C.accent3, align: "center" });
    card(s, C, 4.6, y, 2.8, 1.3, { fill: C.accent3, transparency: 85, line: C.accent3 });
    tx(s, "Θ Sink [5] 0 2 ?", { x: 4.6, y, w: 2.8, h: 1.3, fontSize: 18, bold: true, color: C.accent3, align: "center", valign: "middle", fontFace: L.MATH });
    arrow(s, C, 7.4, y + 0.65, 8.4, y + 0.65, { color: C.accent3, width: 2.5 });
    card(s, C, 8.4, y, 4.3, 1.3, { fill: C.accent1, transparency: 88, line: C.accent1 });
    tx(s, [{ text: "callee  Sink(a)", options: { bold: true, color: C.accent1, breakLine: true } }, { text: "fresh valuation  [a ↦ 5]", options: { fontFace: L.MATH, breakLine: true } }, { text: "the caller's names are invisible", options: { italic: true, fontSize: 13 } }],
      { x: 8.55, y: y + 0.08, w: 4.05, h: 1.15, fontSize: 14, color: C.text1 });
    tx(s, "Trace [lookup(1,2,3), call(7,[5])], σ.sk 7, Sink(a) { ∃ g : Call(g,[a]) when sk(g) }:", { x: 0.6, y: 5.65, w: 12.1, h: 0.4, fontSize: 14, color: C.text2 });
    const res = [["Θ Sink [5] 0 2", "✓", C.accent6], ["Θ Sink [5] 1 2", "✓", C.accent6], ["Θ Sink [9] 0 2", "✗  no call with 9", C.accent5], ["Θ Sink [5, 6] 0 2", "✗  arity", C.accent5]];
    res.forEach(([q, r, col], k) => {
      const x = 0.6 + k * 3.05;
      card(s, C, x, 6.1, 2.9, 0.7, { fill: col, transparency: 88 });
      tx(s, [{ text: q + "  ", options: { fontFace: L.MATH } }, { text: r, options: { bold: true, color: col } }], { x: x + 0.1, y: 6.15, w: 2.75, h: 0.6, fontSize: 13, color: C.text1, valign: "middle" });
    });
  }

  // QProg.interp
  {
    const s = D.slide("Building Θ from a program",
      "QProg.interp builds Θ by structural recursion on the program list. The empty program interprets every invocation as False. " +
      "For q :: Δ: if the name is q's, check the arity, then run q's body under a fresh valuation binding only the parameters, " +
      "with invocations inside q's body answered by the interpretation of the tail Δ. Otherwise delegate to the tail. " +
      "Why start from LEnv.empty and not the caller's ξ? So that the meaning of Q(z₁, …, zₖ) depends only on the argument locations: Θ's type has no ξ in it, " +
      "it is computed once per program, and there is no dynamic scoping. For well-formed queries both choices give the same result (coincidence lemma). " +
      "Exec.Matches starts at boundary 0, with any end j.");
    code(s, C,
      "def QProg.interp (t : List Act) (σ : Obs) :\n    QProg → Interp\n" +
      "  | []     => fun _ _ _ _ => False\n" +
      "  | q :: Δ => fun Q ls i j =>\n" +
      "      if Q = q.name then\n" +
      "        ls.length = q.params.length ∧\n" +
      "        QBody.Sat (QProg.interp t σ Δ) t σ\n" +
      "                  (LEnv.empty.bind q.params ls) q.body i j\n" +
      "      else QProg.interp t σ Δ Q ls i j\n\n" +
      "def Exec.Matches Δ e Q ls :=\n  ∃ j, Δ.interp e.trc.toList e.obs Q ls 0 j",
      0.6, 1.45, 7.6, 3.85, { fontSize: 13 });
    // list diagram
    const names = [["Main", "interp [Sink]"], ["Sink", "interp []"], ["[ ]", "always False"]];
    names.forEach(([n, d], k) => {
      const x = 8.6 + 0, y = 1.5 + k * 1.25;
      card(s, C, x, y, 1.6, 0.8, { fill: k === 2 ? C.accent4 : C.accent1, transparency: k === 2 ? 70 : 85, line: k === 2 ? C.accent4 : C.accent1 });
      tx(s, n, { x, y, w: 1.6, h: 0.8, fontFace: L.CODE, fontSize: 16, bold: true, color: k === 2 ? C.text1 : C.accent1, align: "center", valign: "middle" });
      if (k < 2) {
        arrow(s, C, x + 0.8, y + 0.8, x + 0.8, y + 1.25, { color: C.accent3, width: 2 });
        tx(s, [{ text: "body checked against", options: { breakLine: true } }, { text: d, options: { fontFace: L.CODE, bold: true } }], { x: x + 1.75, y, w: 2.4, h: 0.8, fontSize: 13, color: C.text1, valign: "middle" });
      }
    });
    box(s, C, 0.6, 5.5, 5.9, 1.4, "The arity check", "Θ Sink [5, 6] … is false here.", { fontSize: 15, titleColor: C.accent3 });
    box(s, C, 6.8, 5.5, 5.9, 1.4, "Why LEnv.empty, not the caller's ξ", "Meaning depends only on argument locations: no dynamic scoping.", { fontSize: 14, titleColor: C.accent1 });
  }

  // sanity results
  {
    const s = D.slide("Sanity results",
      "Three groups of facts. Interp.Ok says an interpretation only relates i ≤ j and stays inside the trace. Pat.Sat.le and .bound need it, " +
      "because the query constructor copies whatever Θ says. A bogus Θ relating 5 to 2 makes Q() & ε end at 5 while Q() ends at 2, " +
      "so F & ε ≡ F fails. QProg.interp_ok shows the real Θ is always Ok, so for real programs the hypothesis is free. " +
      "The algebra: ε is a unit for ;, ; is associative, ‖ and & are commutative and idempotent, & associative. " +
      "lower_start, added during review: starting a match earlier never forces finishing later. The weaker statement 'some match from 0' " +
      "is not inductive: lowering ε's start lowers its end, so in ε ; F₂ the second pattern must also be restarted. The query case needs the " +
      "same property of Θ, which holds because except is whole-trace. Corollary: Exec.Matches loses nothing by starting at 0.");
    box(s, C, 0.6, 1.45, 3.95, 3.25, "Interp.Ok",
      [{ text: "Θ only relates i ≤ j, within the trace.", options: { breakLine: true } },
       { text: "A bogus Θ := (i = 5 ∧ j = 2):", options: { breakLine: true, bold: true } },
       { text: "Q() : 5 ⇝ 2", options: { fontFace: L.MATH, breakLine: true } },
       { text: "Q() & ε : 5 ⇝ max(2, 5) = 5", options: { fontFace: L.MATH, breakLine: true } },
       { text: "so F & ε ≡ F fails. The real Θ is always Ok (QProg.interp_ok)." }],
      { fontSize: 14, titleColor: C.accent3, bullets: false });
    box(s, C, 4.7, 1.45, 3.95, 3.25, "Algebra",
      ["ε ; F ≡ F ≡ F ; ε", "(F ; G) ; H ≡ F ; (G ; H)", "‖ and &: commutative, idempotent", "& associative", "F & ε ≡ F  (needs Interp.Ok)"],
      { fontSize: 15, titleColor: C.accent1 });
    box(s, C, 8.8, 1.45, 3.9, 3.25, "lower_start  (new)",
      [{ text: "F : i ⇝ j  and  i′ ≤ i", options: { fontFace: L.MATH, bold: true, breakLine: true } },
       { text: "⟹  ∃ j′ ≤ j,  F : i′ ⇝ j′", options: { fontFace: L.MATH, bold: true, breakLine: true } },
       { text: "“Starting earlier never forces finishing later.”", options: { italic: true, breakLine: true } },
       { text: "“Some match from 0” alone is not inductive: in ε ; F₂, lowering ε lowers its end too." }],
      { fontSize: 14, titleColor: C.accent6, bullets: false });
    card(s, C, 0.6, 4.95, 12.1, 1.05, { fill: C.accent6, transparency: 88, line: C.accent6 });
    tx(s, [{ text: "Corollary  Exec.Matches.of_interp: ", options: { bold: true, color: C.accent6 } },
           { text: "a match from any boundary gives one from 0. Defining Exec.Matches from boundary 0 loses no generality. (Θ's case holds because except is whole-trace.)" }],
      { x: 0.8, y: 4.95, w: 11.7, h: 1.05, fontSize: 15, color: C.text1, valign: "middle" });
  }
};
