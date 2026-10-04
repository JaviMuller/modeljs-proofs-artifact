// Section 4: FO-LTL.  Section 5: the translation.
module.exports = function (D) {
  const { C, L } = D;
  const { tx, bullets, card, pill, code, math, arrow, line, box, timeline } = L;

  D.section("FO-LTL over finite traces", 4, "Standard first-order past and future LTL, with records as models",
    "CoreJsFoLtl.lean is organised like a logic textbook: signature, terms, atoms, formulas, models, satisfaction. It is self-contained and " +
    "does not depend on the query language.");

  // signature & formulas
  {
    const s = D.slide("Signature and formulas",
      "One sort of individuals, interpreted as locations; quantifiers range over Loc. No function symbols, so the only terms are variables. " +
      "Values appear only as constants inside hv. The relation symbols split into action symbols, whose truth varies along the trace, " +
      "and state symbols, which read the rigid observation. Call has a variable number of arguments, so it is really a family call_n, one " +
      "relation symbol per arity. eq exists for one purpose: the exclusivity formula. Formulas are the usual connectives, strong next X, until U, " +
      "yesterday Y, since S, and first-order quantifiers. F, G, O and H are derived. No normal-form restriction: formulas nest freely.");
    tx(s, "Signature: one sort (Loc), relation symbols only", { x: 0.6, y: 1.45, w: 6.2, h: 0.4, fontSize: 17, bold: true, color: C.text1 });
    const acts = [["lookup/3", "x₁ := x₂[x₃] now"], ["update/3", "x₁[x₂] := x₃ now"], ["call_n/(n+1)", "one symbol per arity n"], ["retn/2", "return now"]];
    const states = [["sk/1, ac/1", "sink, attacker-controlled"], ["dep/2, sv/2", "dependency, same value"], ["hv(_, c)/1", "one symbol per value c"], ["eq/2", "equality (for exclusivity)"]];
    tx(s, "action symbols: vary along the trace", { x: 0.6, y: 1.95, w: 6.2, h: 0.35, fontSize: 14, bold: true, color: C.accent2 });
    acts.forEach(([a, b], k) => {
      const y = 2.35 + k * 0.5;
      tx(s, [{ text: a, options: { fontFace: L.CODE, bold: true } }, { text: "   " + b }], { x: 0.75, y, w: 6, h: 0.45, fontSize: 14, color: C.text1 });
    });
    tx(s, "state symbols: read the rigid σ", { x: 0.6, y: 4.45, w: 6.2, h: 0.35, fontSize: 14, bold: true, color: C.accent1 });
    states.forEach(([a, b], k) => {
      const y = 4.85 + k * 0.48;
      tx(s, [{ text: a, options: { fontFace: L.CODE, bold: true } }, { text: "   " + b }], { x: 0.75, y, w: 6, h: 0.45, fontSize: 14, color: C.text1 });
    });
    card(s, C, 7.1, 1.45, 5.6, 3.4, { fill: C.accent2, transparency: 90, line: C.accent2 });
    tx(s, "Formulas  Ltl ν", { x: 7.3, y: 1.55, w: 5.2, h: 0.4, fontSize: 17, bold: true, color: C.accent2 });
    math(s, C, [
      { text: "φ ::= atom | ⊤ | ⊥ | ¬φ | φ ∧ φ | φ ∨ φ", options: { breakLine: true } },
      { text: "      | X φ | φ U φ          (future)", options: { breakLine: true } },
      { text: "      | Y φ | φ S φ          (past)", options: { breakLine: true } },
      { text: "      | ∃x. φ | ∀x. φ" }],
      { x: 7.3, y: 2.05, w: 5.2, h: 1.6, fontSize: 17 });
    math(s, C, [{ text: "F φ = ⊤ U φ      G φ = ¬F¬φ      (future)", options: { breakLine: true } },
                { text: "O φ = ⊤ S φ      H φ = ¬O¬φ      (past)" }],
      { x: 7.3, y: 3.8, w: 5.2, h: 0.8, fontSize: 16, color: C.text2 });
    box(s, C, 7.1, 5.05, 5.6, 1.7, "No normal form", "Past and future operators and quantifiers nest freely. ν is the variable type, so translations can rename variables.", { fontSize: 14, titleColor: C.accent2 });
  }

  // models
  {
    const s = D.slide("Models: a temporal part and a rigid part",
      "A model has a list of states and an observation. A state is a predicate over actions, a set of actions that hold there, not one action. " +
      "That is the standard first-order reading: at each time point each relation symbol is interpreted as an arbitrary relation. " +
      "Exec.toModel produces the intended models, where each state is the singleton {t[p]}. The price of generality is models no record produces: " +
      "states with no action, or with two actions at once. That is paid back by the exclusivity results at the end of the file.");
    code(s, C, "structure Model where\n  states : List (Act → Prop)\n  obs    : Obs\n\ndef Exec.toModel (e : Exec) : Model where\n  states := e.trc.toList.map\n              fun a => fun a' => a' = a\n  obs    := e.obs",
      0.6, 1.45, 6.8, 2.9, { fontSize: 14 });
    // diagram of record model
    tx(s, "Exec.toModel: each state is a singleton", { x: 7.7, y: 1.45, w: 5, h: 0.4, fontSize: 15, bold: true, color: C.accent2 });
    ["{ call(204,[1100]) }", "{ ret(204,0) }"].forEach((t, k) => {
      card(s, C, 7.7 + k * 2.55, 1.95, 2.4, 0.8, { fill: C.accent2, transparency: 85, line: C.accent2 });
      tx(s, t, { x: 7.7 + k * 2.55, y: 1.95, w: 2.4, h: 0.8, fontFace: L.CODE, fontSize: 12, color: C.text1, align: "center", valign: "middle" });
    });
    card(s, C, 7.7, 2.95, 4.95, 0.65, { fill: C.accent1, transparency: 85, line: C.accent1 });
    tx(s, "obs = σ  (rigid, shared by all states)", { x: 7.7, y: 2.95, w: 4.95, h: 0.65, fontSize: 14, color: C.text1, align: "center", valign: "middle" });
    tx(s, "A general model may have", { x: 7.7, y: 3.85, w: 5, h: 0.4, fontSize: 15, bold: true, color: C.accent5 });
    ["{ }", "{ call(1,[2]), call(3,[4]) }"].forEach((t, k) => {
      const w = k === 0 ? 1.2 : 3.6;
      const x = k === 0 ? 7.7 : 9.05;
      card(s, C, x, 4.3, w, 0.8, { fill: C.background1, line: C.accent5, dash: "dash" });
      tx(s, t, { x, y: 4.3, w, h: 0.8, fontFace: L.CODE, fontSize: 12, color: C.text1, align: "center", valign: "middle" });
    });
    box(s, C, 0.6, 4.6, 6.8, 2.15, "Why sets, not single actions?",
      "Standard first-order semantics: each relation symbol is interpreted as an arbitrary relation at each time point. Model is the logic's own class of structures; records are one way to produce them.",
      { fontSize: 15, titleColor: C.accent2 });
    box(s, C, 7.7, 5.35, 5.0, 1.4, "Price, and payback", "Models with 0 or ≥ 2 actions per state. Paid back by exclusivity (later).", { fontSize: 14, titleColor: C.accent3 });
  }

  // satisfaction
  {
    const s = D.slide("Satisfaction on finite traces",
      "Positions are boundaries 0 … n, n the number of states, exactly as in the query semantics. Boundary n is a sentinel at which no action holds. " +
      "X is strong: it needs a next boundary. Y is false at 0: there is no yesterday before the start. Both are standard for finite traces. " +
      "Until and since are the usual ones. Action atoms only hold at a state, never at the sentinel. State atoms read only σ, so they hold at every " +
      "boundary or at none: G p ≡ p ≡ F p.");
    timeline(s, C, 1.0, 1.8, 2.3, ["a₀", "a₁", "a₂"], { fontSize: 16, sentinel: true });
    tx(s, "← sentinel n: no action holds", { x: 8.1, y: 1.8, w: 4.0, h: 0.5, fontSize: 14, color: C.accent3, bold: true, valign: "middle", margin: 0 });
    code(s, C,
      "| ξ, .next φ,      i => i < m.len ∧ φ.Sat m ξ (i + 1)\n" +
      "| ξ, .until φ ψ,   i => ∃ k, i ≤ k ∧ k ≤ m.len ∧ ψ.Sat m ξ k\n" +
      "                          ∧ ∀ p, i ≤ p → p < k → φ.Sat m ξ p\n" +
      "| ξ, .yesterday φ, i => i ≠ 0 ∧ φ.Sat m ξ (i - 1)\n" +
      "| ξ, .since φ ψ,   i => ∃ k, k ≤ i ∧ ψ.Sat m ξ k\n" +
      "                          ∧ ∀ p, k < p → p ≤ i → φ.Sat m ξ p\n" +
      "| ξ, .ex x φ,      i => ∃ l, φ.Sat m (upd ξ x l) i",
      0.6, 3.15, 8.1, 2.65, { fontSize: 13 });
    box(s, C, 9.0, 3.15, 3.7, 1.25, "X is strong", "X φ at i needs i < n.", { fontSize: 15, titleColor: C.accent2 });
    box(s, C, 9.0, 4.55, 3.7, 1.25, "Y is false at 0", "No yesterday before 0.", { fontSize: 15, titleColor: C.accent2 });
    card(s, C, 0.6, 6.0, 12.1, 0.8, { fill: C.background2 });
    tx(s, [{ text: "Action atoms ", options: { bold: true, color: C.accent2 } }, { text: "hold only at a state (never at n).  " },
           { text: "State atoms ", options: { bold: true, color: C.accent1 } }, { text: "read only σ: true at every boundary or none, so G p ≡ p ≡ F p." }],
      { x: 0.8, y: 6.08, w: 11.7, h: 0.65, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // first & atStart
  {
    const s = D.slide("Reaching back to the start: first and atStart",
      "first is ¬Y⊤: true only at boundary 0, the only boundary without a yesterday. atStart φ is O(φ ∧ first): at some boundary k ≤ i, φ ∧ first " +
      "held; first forces k = 0, so this says φ held at 0, and since 0 ≤ i for every i, its truth value is the same at every boundary. " +
      "It behaves like a state atom whatever φ is. This is the standard trick for reaching back to the start of a finite trace from anywhere in a formula, " +
      "and it is how the query's whole-trace except is translated in place.");
    math(s, C, [{ text: "first  :=  ¬ Y ⊤", options: { breakLine: true } }, { text: "atStart φ  :=  O (φ ∧ first)" }],
      { x: 0.6, y: 1.45, w: 6.5, h: 1.1, fontSize: 22 });
    timeline(s, C, 1.0, 3.0, 2.2, ["a₀", "a₁", "a₂", "a₃", "a₄"], { fontSize: 15 });
    // arrow from boundary 4 back to 0
    arrow(s, C, 1.0 + 4 * 2.2, 2.75, 1.0, 2.75, { color: C.accent3, width: 3 });
    tx(s, "atStart φ at boundary 4  ⇔  φ at boundary 0", { x: 3.0, y: 2.3, w: 6, h: 0.4, fontSize: 15, bold: true, color: C.accent3, align: "center" });
    s.addShape("ellipse", { x: 0.85, y: 3.95, w: 0.3, h: 0.3, fill: { color: C.accent6 }, line: { type: "none" } });
    tx(s, "first holds only here", { x: 0.4, y: 4.3, w: 2.5, h: 0.4, fontSize: 13, color: C.accent6, bold: true });
    code(s, C, "theorem Ltl.sat_atStart :\n  (Ltl.atStart φ).Sat m ξ i ↔ φ.Sat m ξ 0\ntheorem Ltl.sat_atStart_indep :\n  (atStart φ) at i ↔ (atStart φ) at i'",
      0.6, 4.95, 7.6, 1.4, { fontSize: 13 });
    box(s, C, 8.5, 4.95, 4.2, 1.85, "Used for except", "The guard ∀k ¬F′ : 0 ⇝ k is anchored at 0; atStart(¬ tr F′) states it wherever the query sits.", { fontSize: 14, titleColor: C.accent3 });
  }

  // exclusivity
  {
    const s = D.slide("Exclusivity: one action per state",
      "Model.Excl says at most one action per state; record models satisfy it. To state it inside the logic we must spell it out atom by atom. " +
      "Different kinds may not co-occur; the same kind may only co-occur with equal arguments. Without the last conjunct the formula would forbid " +
      "an action co-occurring with itself, false wherever a call happens. call is an infinite family, so the formula is relative to a finite list of Shapes. " +
      "Only the soundness direction is proved. The plain converse is false: shapes not in the list are unconstrained. For shape-finite models it becomes a " +
      "characterisation. Nothing outside the file uses it; it is a guarantee for a future consumer, e.g. an off-the-shelf validity checker.");
    math(s, C, "Model.Excl m  :=  ∀ i a₁ a₂,  m.holds i a₁ → m.holds i a₂ → a₁ = a₂", { x: 0.6, y: 1.45, w: 12.1, h: 0.5, fontSize: 18 });
    tx(s, "Inside the logic, pair by pair (Shape names lookup, update, retn, call_n):", { x: 0.6, y: 2.1, w: 12.1, h: 0.4, fontSize: 15, color: C.text2 });
    code(s, C, "pairExcl (call 1) retn     = ∀ v0 v2 v1 v3. ¬( call(v0,[v2]) ∧ retn(v1,v3) )\n" +
               "pairExcl (call 1) (call 1) = ∀ v0 v2 v1 v3. ¬( call(v0,[v2]) ∧ call(v1,[v3])\n" +
               "                                             ∧ ¬(v0 = v1 ∧ v2 = v3) )\n" +
               "Ltl.excl v shapes          = G ⋀ { pairExcl v s s′ | s, s′ ∈ shapes }",
      0.6, 2.55, 12.1, 1.6, { fontSize: 14, tag: "formula", tagW: 1.1 });
    box(s, C, 0.6, 4.4, 3.9, 1.8, "Why the ≠ conjunct", "Without it, an action may not co-occur with itself: false wherever any call happens.", { fontSize: 14, titleColor: C.accent3 });
    box(s, C, 4.7, 4.4, 3.9, 1.8, "Proved", "Every exclusive model, so every record model, satisfies Ltl.excl v shapes (Exec.toModel_sat_excl).", { fontSize: 14, titleColor: C.accent6 });
    box(s, C, 8.8, 4.4, 3.9, 1.8, "Not proved", "Converse: false in general (unlisted shapes, call_n is infinite). For shape-finite models it holds. Unused by the translation.", { fontSize: 14, titleColor: C.accent5 });
  }

  // ════════════════════════ Section 5: translation
  D.section("The translation", 5, "Turning a query into a formula that means the same thing",
    "CoreJsQueryToLtl.lean. First the shape of the formulas, then the plumbing that avoids variable capture.");

  // continuations
  {
    const s = D.slide("Why continuations",
      "You cannot translate F on its own: to translate F₁ ; F₂ you need to know where F₁ ended, to start F₂ there. So every pattern is translated " +
      "together with a formula K, the continuation: what must hold once F has finished. The contract: tr(F, K) holds at boundary i iff F matches " +
      "from i to some j at which K holds. At the top level nothing has to come after a match, so K = ⊤, which mirrors 'there exists j' in Exec.Matches.");
    card(s, C, 0.6, 1.5, 12.1, 1.3, { fill: C.accent3, transparency: 90, line: C.accent3 });
    tx(s, [{ text: "The contract:   ", options: { bold: true, color: C.accent3, fontFace: L.CODE } },
           { text: "tr(F, K) holds at i   ⇔   ∃ j,  F : i ⇝ j   and   K holds at j", options: { fontFace: L.MATH } }],
      { x: 0.8, y: 1.6, w: 11.7, h: 1.1, fontSize: 21, color: C.text1, valign: "middle", align: "center" });
    timeline(s, C, 1.2, 3.5, 2.0, ["", "", "", "", ""], { fontSize: 13, highlight: { 1: C.accent1, 2: C.accent1 },
      spans: [{ from: 1, to: 3, label: "F : i ⇝ j", color: C.accent1 }] });
    card(s, C, 1.2 + 3 * 2.0, 2.95, 4.0, 0.4, { fill: C.accent2, transparency: 70 });
    tx(s, "K holds from here", { x: 1.2 + 3 * 2.0, y: 2.95, w: 4.0, h: 0.4, fontSize: 14, bold: true, color: C.accent2, align: "center", valign: "middle" });
    tx(s, "i", { x: 1.2 + 2.0 - 0.2, y: 2.95, w: 0.4, h: 0.4, fontSize: 18, bold: true, color: C.accent3, align: "center", fontFace: L.MATH });
    box(s, C, 0.6, 5.35, 5.9, 1.4, "Why K?", "tr(F₁ ; F₂) needs F₁'s end: give F₁ the continuation “then F₂, then K”.", { fontSize: 15, titleColor: C.accent3 });
    box(s, C, 6.8, 5.35, 5.9, 1.4, "Top level: K = ⊤", "Any end point will do, which mirrors “∃ j” in Exec.Matches.", { fontSize: 15, titleColor: C.accent2 });
  }

  // rules
  {
    const s = D.slide("The translation rules",
      "The six pattern rules and the query-body rule. ε passes the continuation through. An action becomes 'eventually: the action, and at the next boundary, K'. " +
      "Sequence threads the continuation: F₂ gets K, and F₁ gets F₂'s translation as its continuation. Choice and conjunction distribute. " +
      "Invocation inlines the callee's body, translated under a fresh renaming. A query body becomes an existential over its locals, the invariant, " +
      "the guard reaching back to the start, and the pattern's translation.");
    const rows = [
      ["ε", "K"], ["a", "F (a ∧ X K)"], ["F₁ ; F₂", "tr(F₁, tr(F₂, K))"], ["F₁ ‖ F₂", "tr(F₁, K) ∨ tr(F₂, K)"], ["F₁ & F₂", "tr(F₁, K) ∧ tr(F₂, K)"],
      ["Q(z₁, …, zₖ)", "tr(body of Q, K), parameters ↦ z₁ … zₖ, fresh locals"],
      ["∃y₁…yₘ: F when I except F′", "∃y₁…yₘ.  I ∧ atStart(¬ tr(F′, ⊤)) ∧ tr(F, K)"],
    ];
    card(s, C, 0.6, 1.45, 12.1, 0.55, { fill: C.text2 });
    tx(s, "F", { x: 0.8, y: 1.45, w: 4, h: 0.55, fontSize: 16, bold: true, color: C.background1, valign: "middle" });
    tx(s, "tr(F, K)", { x: 5.0, y: 1.45, w: 7, h: 0.55, fontSize: 16, bold: true, color: C.background1, valign: "middle" });
    rows.forEach(([f, t], k) => {
      const y = 2.05 + k * 0.62;
      card(s, C, 0.6, y, 12.1, 0.56, { fill: k % 2 ? C.background1 : C.background2 });
      tx(s, f, { x: 0.8, y, w: 4.1, h: 0.56, fontSize: 17, color: C.accent1, valign: "middle", fontFace: L.MATH, bold: true });
      tx(s, t, { x: 5.0, y, w: 7.6, h: 0.56, fontSize: 17, color: C.accent2, valign: "middle", fontFace: L.MATH });
    });
    card(s, C, 0.6, 6.5 - 0.1, 12.1, 0.5, { fill: C.accent3, transparency: 90 });
    tx(s, "Top level:  tr(q) = tr(q.body, ⊤)  with fresh tags from 0", { x: 0.8, y: 6.4, w: 11.7, h: 0.5, fontSize: 15, color: C.text1, valign: "middle", fontFace: L.MATH });
  }

  // worked example tree
  {
    const s = D.slide("Worked example: continuations flow inwards",
      "tr((a ; b) ‖ c, ⊤). Choice gives both alternatives the continuation ⊤. In the sequence, b is translated first with ⊤, giving F(b ∧ X ⊤), " +
      "and that formula becomes a's continuation. The formula is built inside-out: the end of the pattern is the innermost part. " +
      "Result: F(a ∧ X F(b ∧ X ⊤)) ∨ F(c ∧ X ⊤).");
    const node = (x, y, w, t, col, sub) => {
      card(s, C, x, y, w, 0.7, { fill: col, transparency: 85, line: col });
      tx(s, t, { x, y, w, h: 0.7, fontSize: 16, bold: true, color: col, align: "center", valign: "middle", fontFace: L.MATH });
      if (sub) tx(s, sub, { x: x - 0.4, y: y + 0.72, w: w + 0.8, h: 0.4, fontSize: 13, color: C.text2, align: "center", fontFace: L.MATH });
    };
    node(5.4, 1.5, 2.5, "‖", C.text2);
    tx(s, "K = ⊤ to both sides", { x: 8.05, y: 1.5, w: 3.0, h: 0.7, fontSize: 14, color: C.text2, fontFace: L.MATH, valign: "middle", margin: 0 });
    line(s, C, 6.1, 2.2, 3.3, 2.75); line(s, C, 7.2, 2.2, 9.9, 2.75);
    node(2.2, 2.75, 2.2, ";", C.text2);
    node(8.9, 2.75, 2.2, "c", C.accent1, "F(c ∧ X ⊤)");
    line(s, C, 2.8, 3.45, 1.6, 4.15); line(s, C, 3.8, 3.45, 5.0, 4.15);
    node(0.6, 4.15, 2.0, "a", C.accent1);
    node(4.2, 4.15, 2.0, "b", C.accent1, "① F(b ∧ X ⊤)");
    arrow(s, C, 4.2, 4.5, 2.6, 4.5, { color: C.accent3, width: 2.5 });
    tx(s, "② becomes a's K", { x: 2.4, y: 3.95, w: 2.0, h: 0.4, fontSize: 13, bold: true, color: C.accent3, align: "center" });
    card(s, C, 0.6, 5.55, 12.1, 1.2, { fill: C.accent2, transparency: 90, line: C.accent2 });
    tx(s, [{ text: "tr((a ; b) ‖ c, ⊤)  =  ", options: { color: C.text1 } },
           { text: "F(a ∧ X F(b ∧ X ⊤))", options: { color: C.accent2, bold: true } }, { text: "  ∨  ", options: { color: C.text1 } },
           { text: "F(c ∧ X ⊤)", options: { color: C.accent2, bold: true } }],
      { x: 0.8, y: 5.65, w: 11.7, h: 1.0, fontSize: 22, fontFace: L.MATH, align: "center", valign: "middle" });
    box(s, C, 7.6, 3.95, 5.1, 1.35, "Inside-out", "The end of the pattern is the innermost part of the formula, so it is built first.", { fontSize: 14, titleColor: C.accent3 });
  }

  // why the X
  {
    const s = D.slide("Why F(a ∧ X K): the X matters",
      "F picks a boundary p at or after i where a holds, so p = j - 1; X K puts the continuation at p + 1 = j. That is exactly the action rule. " +
      "Without the X, F(A₁ ∧ F A₂) lets one action serve both sides: on the single-action trace [Call(1,[2])] with A₁ = A₂ = Call(x,[y]), " +
      "it holds, but the sequence does not match. With X the second action must be strictly later, matching seq. " +
      "For two different kinds of action the two formulas agree on record models, because of exclusivity; they only diverge where one state could serve both. " +
      "Also: in seq, F₂ is translated first because F₁ needs its result; the counter follows the order of construction.");
    tx(s, "A₁ ; A₂  with  A₁ = A₂ = Call(x, [y]),  trace [ call(1, [2]) ]", { x: 0.6, y: 1.45, w: 12.1, h: 0.45, fontSize: 17, bold: true, color: C.text1, fontFace: L.MATH });
    timeline(s, C, 4.6, 2.2, 3.0, ["call(1, [2])"], { fontSize: 15, highlight: { 0: C.accent3 } });
    box(s, C, 0.6, 3.6, 5.9, 1.55, "F(A₁ ∧ F A₂)   holds ✗", "The inner F starts at the same boundary: one action serves both sides.", { fontSize: 15, titleColor: C.accent5 });
    box(s, C, 6.8, 3.6, 5.9, 1.55, "F(A₁ ∧ X F A₂)   fails ✓", "X moves past the first action: A₂ must be strictly later, like the seq rule.", { fontSize: 15, titleColor: C.accent6 });
    card(s, C, 0.6, 5.4, 12.1, 1.0, { fill: C.background2 });
    tx(s, [{ text: "Matches the query rules: ", options: { bold: true } },
           { text: "a : i ⇝ j puts a at j − 1 and resumes at j; F gives p = j − 1 ≥ i, X K puts K at p + 1 = j. In seq, F₂ is translated first because F₁ needs tr(F₂, K) as its continuation." }],
      { x: 0.8, y: 5.4, w: 11.7, h: 1.0, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // & and Mono
  {
    const s = D.slide("Conjunction needs downward-closed continuations",
      "Semantically F₁ & F₂ ends at max(j₁, j₂), so the contract wants K there. The formula tr(F₁,K) ∧ tr(F₂,K) gives K at j₁ and K at j₂. " +
      "These agree when K is downward-closed: true at p implies true at every q ≤ p. Counterexample: K = ¬X⊤, true only at the sentinel. " +
      "On [b, a], a & b: j₁ = 2 = n, j₂ = 1. Semantically & ends at 2 where K holds: match. The formula demands K at 1 too: false. " +
      "Why this never bites: the translation only builds Mono continuations. ⊤; anything of the form F(…), because a later witness still lies ahead " +
      "of an earlier boundary; atStart(…), position-independent; conjunctions and disjunctions of these; and invariants, which are state atoms. " +
      "This is the precise sense in which whole-trace except keeps & exact: an anchored guard would look at where the match is.");
    math(s, C, [{ text: "semantics:  K at max(j₁, j₂)        formula:  K at j₁  and  K at j₂", options: { breakLine: true } },
                { text: "Mono m ξ K  :=  ∀ q ≤ p ≤ n,  K at p  →  K at q", options: { color: C.accent3 } }],
      { x: 0.6, y: 1.45, w: 12.1, h: 1.0, fontSize: 18 });
    tx(s, "Counterexample  K = ¬X⊤  (true only at the sentinel),   a & b  on  [b, a]", { x: 0.6, y: 2.6, w: 12.1, h: 0.4, fontSize: 16, bold: true, color: C.accent5 });
    timeline(s, C, 1.0, 3.25, 2.6, ["b", "a"], { fontSize: 16, sentinel: true,
      spans: [{ from: 0, to: 2, label: "a : 0 ⇝ 2  (j₁ = 2 = n)", color: C.accent1 }, { from: 0, to: 1, label: "b : 0 ⇝ 1  (j₂ = 1)", color: C.accent2, row: 1 }] });
    card(s, C, 7.0, 3.1, 5.7, 1.55, { fill: C.background2 });
    tx(s, [{ text: "semantics: ", options: { bold: true } }, { text: "ends at 2, K holds → match", options: { color: C.accent6, breakLine: true } },
           { text: "formula: ", options: { bold: true } }, { text: "needs K at 1 → false", options: { color: C.accent5 } }],
      { x: 7.15, y: 3.2, w: 5.4, h: 1.4, fontSize: 16, color: C.text1, valign: "middle" });
    tx(s, "Every K the translation builds is Mono:", { x: 0.6, y: 5.35, w: 12.1, h: 0.4, fontSize: 15, bold: true, color: C.text1 });
    ["⊤", "F(…)", "atStart(…)", "∧, ∨ of these", "invariants"].forEach((t, k) => {
      pill(s, C, t, 0.6 + k * 2.45, 5.8, C.accent6, { w: 2.25, h: 0.45, fontSize: 14 });
    });
    tx(s, "Whole-trace except is what keeps the guard part position-independent, hence Mono.", { x: 0.6, y: 6.4, w: 12.1, h: 0.4, fontSize: 14, color: C.accent3, italic: true });
  }

  // query bodies
  {
    const s = D.slide("Query bodies, conjunct by conjunct",
      "The query-body rule mirrors the five premises of QBody.Sat one to one. The existential over the locals is the choice of ls. " +
      "The invariant is a state formula. The guard: F′ gets continuation ⊤ because premise 5 says 'for every end point k'. " +
      "It is wrapped in atStart(¬ …) because F′ must be matched from boundary 0, while the formula is evaluated wherever the query sits. " +
      "The pattern gets the outer continuation K, which sits inside the scope of the ∃: keep that in mind for the next slide.");
    card(s, C, 0.6, 1.5, 12.1, 1.1, { fill: C.background2 });
    const parts = [["∃y₁…yₘ.", C.accent2], ["  I", L.WHEN], ["  ∧  ", C.text1], ["atStart(¬ tr(F′, ⊤))", L.EXCEPT], ["  ∧  ", C.text1], ["tr(F, K)", C.accent3]];
    tx(s, parts.map(([t, c]) => ({ text: t, options: { color: c, bold: c !== C.text1 } })), { x: 0.8, y: 1.6, w: 11.7, h: 0.9, fontSize: 26, fontFace: L.MATH, align: "center", valign: "middle" });
    const m = [
      ["∃y₁…yₘ", C.accent2, "(1)(2) choose ls for the locals"],
      ["I", L.WHEN, "(4) the invariant: state atoms"],
      ["atStart(¬ tr(F′, ⊤))", L.EXCEPT, "(5) F′ from 0 to any k: K = ⊤ for “any end”, atStart for “from 0”"],
      ["tr(F, K)", C.accent3, "(3) the pattern, then the outer K"],
    ];
    m.forEach(([a, col, b], k) => {
      const y = 2.95 + k * 0.85;
      card(s, C, 0.6, y, 12.1, 0.72, { fill: col, transparency: 90 });
      tx(s, a, { x: 0.8, y, w: 3.6, h: 0.72, fontSize: 17, bold: true, color: col, fontFace: L.MATH, valign: "middle" });
      tx(s, b, { x: 4.5, y, w: 8.1, h: 0.72, fontSize: 15, color: C.text1, valign: "middle" });
    });
    card(s, C, 0.6, 6.4, 12.1, 0.45, { fill: C.accent3, transparency: 88 });
    tx(s, "Note: the outer continuation K ends up inside the scope of ∃y₁…yₘ. That is where variable capture can happen.", { x: 0.8, y: 6.4, w: 11.7, h: 0.45, fontSize: 14, color: C.text1, valign: "middle", bold: true });
  }

  // capture
  {
    const s = D.slide("The variable capture problem",
      "Ret(a) { ∃y: Retn(y, a) } says some function returns a. RetThenCall(x, y) { Ret(x) ; Call(y, [x]) } says x is returned by some function, " +
      "then the caller's y is called with x. In the query semantics there is no problem: Ret's body runs under a brand-new valuation, so its y and the " +
      "caller's y live in different valuations. A formula has one namespace. Translating with names copied verbatim, K = F(call(y,[x]) ∧ X⊤) mentions " +
      "the caller's y, and it lands under Ret's ∃y. The caller's y gets bound by Ret's local: the formula now says the same function that returned x is " +
      "called with x. The same can happen through arguments: Main(y) { Ret(y) } would become ∃y: Retn(y, y).");
    code(s, C, "Ret(a)            { ∃ y : Retn(y, a) }\nRetThenCall(x, y) { Ret(x) ; Call(y, [x]) }", 0.6, 1.45, 7.2, 1.05, { fontSize: 15, tag: "queries", tagW: 1.1 });
    box(s, C, 8.1, 1.45, 4.6, 1.15, "Query semantics: fine", "Ret's y has its own valuation.", { fontSize: 14, titleColor: C.accent6 });
    tx(s, "Naive translation (names copied verbatim):", { x: 0.6, y: 2.8, w: 12.1, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    card(s, C, 0.6, 3.3, 12.1, 0.95, { fill: C.accent5, transparency: 92, line: C.accent5 });
    tx(s, [{ text: "∃", options: {} }, { text: "y", options: { color: C.accent5, bold: true } }, { text: ". F( retn(" }, { text: "y", options: { color: C.accent5, bold: true } },
           { text: ", x) ∧ X F( call(" }, { text: "y", options: { color: C.accent5, bold: true, underline: { style: "sng" } } }, { text: ", [x]) ∧ X ⊤ ) )" }],
      { x: 0.8, y: 3.35, w: 11.7, h: 0.85, fontSize: 24, fontFace: L.MATH, align: "center", valign: "middle", color: C.text1 });
    tx(s, "↑ this y was the caller's parameter, now bound by Ret's ∃y", { x: 6.4, y: 4.3, w: 6.3, h: 0.4, fontSize: 14, color: C.accent5, bold: true });
    box(s, C, 0.6, 4.95, 5.9, 1.8, "What went wrong", "K was built outside, then placed under Ret's ∃y. Now it says “the same function that returned x is called with x”.", { fontSize: 14, titleColor: C.accent5 });
    box(s, C, 6.8, 4.95, 5.9, 1.8, "Also through arguments", [{ text: "Main(y) { Ret(y) }  ⟶  ∃y. Retn(y, y)", options: { fontFace: L.CODE, breakLine: true } }, { text: "“some function returns itself”: classic substitution capture." }], { fontSize: 14, titleColor: C.accent5, bullets: false });
  }

  // fix
  {
    const s = D.slide("The fix: fresh names for every local",
      "Formula variables are LVar = Var ⊕ Nat. inl x is a source name, used only for the top-level query's parameters. inr k, written #k, is a synthetic " +
      "name minted fresh for every local of every query body, the top-level one included. A counter only goes up, so every #k is bound exactly once. " +
      "The renaming ρ : Var → LVar says, inside the body being translated, which formula variable each source name stands for. At the top ρ = inl. " +
      "Entering a body with locals, extendFresh maps them to #n, #(n+1), …. Invoking Q(z₁, …, zₖ), ofParams maps Q's parameters to what the caller's arguments " +
      "already denote, and nothing else is visible: the syntactic twin of starting from LEnv.empty. Redoing the example: Ret's local is #0 and the caller's y is inl y. " +
      "Two invocations get different tags. In seq, F₂ is translated first, so Ret(y) gets #0 and Ret(x) gets #1.");
    code(s, C, "abbrev LVar := Var ⊕ Nat        -- inl x : source name,  inr k : fresh tag #k\nabbrev Ren  := Var → LVar        -- ρ: how each source name is written",
      0.6, 1.45, 12.1, 0.95, { fontSize: 15 });
    const r = [["top level", "ρ = inl", "every name stands for itself"], ["enter a body", "ρ.extendFresh locals n", "y₁ ↦ #n, y₂ ↦ #(n+1), …"], ["invoke Q(z₁, …, zₖ)", "ofParams q.params (zs.map ρ)", "params ↦ caller's args; nothing else visible"]];
    r.forEach(([a, b, c], k) => {
      const x = 0.6 + k * 4.1;
      card(s, C, x, 2.6, 3.9, 1.35, { fill: C.accent3, transparency: 88 });
      tx(s, [{ text: a, options: { bold: true, color: C.accent3, breakLine: true } }, { text: b, options: { fontFace: L.CODE, fontSize: 13, breakLine: true } }, { text: c, options: { fontSize: 13 } }],
        { x: x + 0.15, y: 2.65, w: 3.6, h: 1.25, fontSize: 15, color: C.text1 });
    });
    tx(s, "The example again (computed by Query.trStr):", { x: 0.6, y: 4.2, w: 12.1, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    card(s, C, 0.6, 4.65, 12.1, 0.95, { fill: C.accent6, transparency: 90, line: C.accent6 });
    tx(s, [{ text: "⊤ ∧ ∃" }, { text: "#0", options: { color: C.accent6, bold: true } }, { text: ". ⊤ ∧ F( retn(" }, { text: "#0", options: { color: C.accent6, bold: true } },
           { text: ", x) ∧ X F( call(" }, { text: "y", options: { color: C.accent1, bold: true } }, { text: ", [x]) ∧ X ⊤ ) )" }],
      { x: 0.8, y: 4.7, w: 11.7, h: 0.85, fontSize: 22, fontFace: L.MATH, align: "center", valign: "middle", color: C.text1 });
    box(s, C, 0.6, 5.75, 5.9, 1.1, "Counter only grows", "Every #k is bound exactly once.", { fontSize: 14, titleColor: C.accent3 });
    box(s, C, 6.8, 5.75, 5.9, 1.1, "Two invocations, two tags", "Ret(x) ; Ret(y):  Ret(y) gets #0, Ret(x) #1.", { fontSize: 14, titleColor: C.accent3 });
  }

  // spec vs computation
  {
    const s = D.slide("Specification and computation",
      "The translation is defined twice. Pat.Tr / QBody.Tr is a relation: φ is a translation of F with renaming ρ, program Δ, continuation K, fresh tags " +
      "from n up to n′. It is the specification, convenient for proofs. Pat.tr / QBody.tr / Query.tr is a function returning Option, computed by " +
      "well-founded recursion on (program length, pattern size): an invocation continues with the strictly shorter rest of the program. It returns none exactly " +
      "when an invocation is unresolved or has the wrong arity. The two are proved to agree both ways, so the relation is functional and the correctness " +
      "theorems apply to the computed formula. #guard checks pin the output for example queries; the build fails if the translation changes.");
    box(s, C, 0.6, 1.45, 5.6, 1.75, "Pat.Tr  (relation, the spec)",
      [{ text: "Pat.Tr ρ Δ F K n φ n′", options: { fontFace: L.CODE, bold: true, breakLine: true } },
       { text: "“φ translates F, renaming ρ, program Δ, continuation K, fresh tags from n up to n′”." }],
      { fontSize: 14, titleColor: C.accent2, bullets: false });
    box(s, C, 7.1, 1.45, 5.6, 1.75, "Pat.tr  (function)",
      [{ text: "Pat.tr ρ Δ F K n : Option (Ltl LVar × Nat)", options: { fontFace: L.CODE, bold: true, breakLine: true } },
       { text: "Well-founded on (|Δ|, size F). none ⇔ unresolved invocation or wrong arity." }],
      { fontSize: 14, titleColor: C.accent3, bullets: false });
    arrow(s, C, 6.2, 2.15, 7.1, 2.15, { color: C.accent6, width: 2.5 });
    arrow(s, C, 7.1, 2.55, 6.2, 2.55, { color: C.accent6, width: 2.5 });
    tx(s, "Tr.tr_eq", { x: 6.0, y: 1.75, w: 1.3, h: 0.35, fontSize: 11, color: C.accent6, align: "center", fontFace: L.CODE });
    tx(s, "tr_sound", { x: 6.0, y: 2.6, w: 1.3, h: 0.35, fontSize: 11, color: C.accent6, align: "center", fontFace: L.CODE });
    tx(s, "Computed, and checked at build time:", { x: 0.6, y: 3.45, w: 12.1, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    code(s, C,
      "#guard Query.trStr [] exSink ==\n  \"((sk(f) ∧ ac(x)) ∧ F (call(f, [x]) ∧ X ⊤))\"\n" +
      "#guard Query.trStr [] exExceptHit ==\n  \"(⊤ ∧ (atStart(¬F (retn(f, r) ∧ X ⊤)) ∧ F (call(f, [x]) ∧ X ⊤)))\"\n" +
      "#guard Query.trStr [exRet] exRetThenCall ==\n  \"(⊤ ∧ (∃#0. (⊤ ∧ F (retn(#0, x) ∧ X F (call(y, [x]) ∧ X ⊤)))))\"",
      0.6, 3.9, 12.1, 2.1, { fontSize: 14 });
  }
};
