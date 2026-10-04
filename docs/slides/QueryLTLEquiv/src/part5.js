// Section 6: the proof.  Section 7: wrap-up.  Appendix.
module.exports = function (D) {
  const { C, L } = D;
  const { tx, bullets, card, pill, code, math, arrow, line, box, timeline } = L;

  D.section("The equivalence proof", 6, "Why the translation means exactly what the query means",
    "The structure of the proof, not every line. The aim is that the statement, its premises and its conclusions all make sense.");

  // headline theorem
  {
    const s = D.slide("The headline theorem",
      "Query.tr_correct. hwf: the program q :: Δ is well formed. hTr: φ is a translation of q's body with renaming inl (every name stands for itself), " +
      "program Δ (q may only invoke what comes after it), continuation ⊤ (any end point), fresh tags from 0. e is any record, not only those produced by BigStep; " +
      "ls any argument list of the right length. hlen matters because Exec.Matches checks arity and the formula does not. topEnv sends each parameter to its " +
      "argument and every fresh tag to 0, which is safe because tags only occur under their own ∃. Checked by hand on Sink: both sides say there is a call of 204 with 1100, and 204 is a sink.");
    code(s, C,
      "theorem Query.tr_correct (hwf : QProg.WF (q :: Δ))\n" +
      "    (hTr : QBody.Tr Sum.inl Δ q.body Ltl.tt 0 φ n')\n" +
      "    (e : Exec) (ls : List Loc) (hlen : ls.length = q.params.length) :\n" +
      "    Exec.Matches (q :: Δ) e q.name ls ↔ φ.Holds e.toModel (q.topEnv ls)",
      0.6, 1.45, 12.1, 1.55, { fontSize: 15 });
    const rows = [
      ["hwf", "q :: Δ is well formed"], ["ρ = Sum.inl", "every source name stands for itself"], ["Δ (not q :: Δ)", "q may only invoke what comes after it"],
      ["K = ⊤", "any end point, like “∃ j” in Exec.Matches"], ["n = 0", "no fresh tags used yet"], ["e, ls, hlen", "any record; arguments of the right arity"],
    ];
    rows.forEach(([a, b], k) => {
      const x = 0.6 + (k % 2) * 6.1, y = 3.2 + Math.floor(k / 2) * 0.68;
      card(s, C, x, y, 5.95, 0.6, { fill: C.background2 });
      tx(s, [{ text: a + "   ", options: { fontFace: L.CODE, bold: true, color: C.accent3 } }, { text: b }], { x: x + 0.12, y, w: 5.7, h: 0.6, fontSize: 14, color: C.text1, valign: "middle" });
    });
    card(s, C, 0.6, 5.35, 12.1, 1.05, { fill: C.accent3, transparency: 90, line: C.accent3 });
    tx(s, [{ text: "On Sink(f, x) { Call(f,[x]) when sk(f) },  ls = [204, 1100]:", options: { bold: true, breakLine: true } },
           { text: "φ = sk(f) ∧ F(call(f, [x]) ∧ X ⊤)   under  f ↦ 204, x ↦ 1100   ⇔   some t[j−1] = call(204, [1100]) and σ.sk 204", options: { fontFace: L.MATH } }],
      { x: 0.8, y: 5.35, w: 11.7, h: 1.05, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // why generalise
  {
    const s = D.slide("Why the proof must generalise",
      "The headline statement fixes K = ⊤, ρ = inl, n = 0 and a fixed program. It cannot be proved by induction on its own terms, because inside the " +
      "translation those change. seq gives F₁ the continuation tr(F₂, K), which is not ⊤. Entering a body changes ρ (extendFresh) and the counter. " +
      "Invocation changes ρ (ofParams) and the program (the tail after the callee). So the proof first states correctness for every K, ρ, n and Δ: " +
      "that is PatCorrect N and QBodyCorrect N, for programs of length at most N. Query.tr_correct is the instance K = ⊤, ρ = inl, n = 0.");
    const items = [
      ["K", "seq gives F₁ the continuation tr(F₂, K) ≠ ⊤", C.accent3],
      ["ρ", "bodies extend it (extendFresh); invocation replaces it (ofParams)", C.accent2],
      ["n", "every body consumes fresh tags", C.accent2],
      ["Δ", "invocation continues with the shorter tail after the callee", C.accent1],
    ];
    items.forEach(([v, d, col], k) => {
      const y = 1.5 + k * 0.92;
      s.addShape("ellipse", { x: 0.6, y, w: 0.75, h: 0.75, fill: { color: col }, line: { type: "none" } });
      s.addText(v, { x: 0.6, y, w: 0.75, h: 0.75, fontSize: 22, bold: true, color: C.background1, align: "center", valign: "middle", fontFace: L.MATH, margin: 0, isTextBox: true });
      tx(s, d, { x: 1.55, y: y - 0.02, w: 5.4, h: 0.8, fontSize: 15, color: C.text1, valign: "middle" });
    });
    card(s, C, 7.2, 1.5, 5.5, 3.45, { fill: C.accent3, transparency: 90, line: C.accent3 });
    tx(s, [{ text: "So: prove it for every K, ρ, n, Δ", options: { bold: true, color: C.accent3, breakLine: true } },
           { text: "PatCorrect N  and  QBodyCorrect N", options: { fontFace: L.CODE, bold: true, breakLine: true } },
           { text: "for every program of length ≤ N.", options: { breakLine: true } },
           { text: " ", options: { breakLine: true } },
           { text: "Query.tr_correct is the instance", options: { breakLine: true } }, { text: "K = ⊤,  ρ = inl,  n = 0.", options: { fontFace: L.MATH } }],
      { x: 7.4, y: 1.5, w: 5.1, h: 3.45, fontSize: 17, color: C.text1, valign: "middle" });
    card(s, C, 0.6, 5.35, 12.1, 1.4, { fill: C.background2 });
    tx(s, [{ text: "The contract, as a theorem (C4): ", options: { bold: true } },
           { text: "(∃ j,  F : i ⇝ j under ξ ∘ ρ   and   K at j under ξ)   ⇔   tr(F, K) at i under ξ", options: { fontFace: L.MATH, color: C.accent3 } }],
      { x: 0.8, y: 5.45, w: 11.7, h: 1.2, fontSize: 15, color: C.text1, valign: "middle" });
  }

  // premises
  {
    const s = D.slide("PatCorrect: the premises",
      "P1 to P3: any record, program and renaming. P4: the induction counter: program length is what decreases at every invocation. Strong induction picks " +
      "N′ = the callee's tail length. P5: well-formedness, used only in the invocation case, for the callee and its tail. P6, P9: any translation derivation. " +
      "P7, ρ fresh below n: every tag ρ already uses is below n, so new tags never clash with names in ρ. P8, K independent of tags ≥ n: K was built outside " +
      "the body, so the body's new ∃ must not capture anything in it. Fresh and Indep are twins: one for the renaming, one for the continuation.");
    code(s, C,
      "def PatCorrect (N : Nat) : Prop :=\n" +
      "  ∀ e Δ ρ, Δ.length ≤ N → QProg.WF Δ →\n" +
      "  ∀ F n K φ n', ρ.Fresh n → K.Indep n → Pat.Tr ρ Δ F K n φ n' →\n" +
      "    n ≤ n' ∧ φ.Indep n' ∧ (Mono K → Mono φ) ∧ (C4)",
      0.6, 1.45, 12.1, 1.5, { fontSize: 15 });
    const rows = [
      ["P1–P3", "e, Δ, ρ", "any record, program, renaming"],
      ["P4", "Δ.length ≤ N", "induction counter: shrinks at every invocation"],
      ["P5", "QProg.WF Δ", "callees exist and are self-contained"],
      ["P6, P9", "Pat.Tr ρ Δ F K n φ n'", "any translation derivation"],
      ["P7", "ρ.Fresh n", "ρ uses no tag ≥ n: new tags never clash"],
      ["P8", "K.Indep n", "K ignores tags ≥ n: new ∃ capture nothing in K"],
    ];
    rows.forEach(([p, f, r], k) => {
      const y = 3.15 + k * 0.6;
      card(s, C, 0.6, y, 12.1, 0.52, { fill: k % 2 ? C.background1 : C.background2 });
      tx(s, p, { x: 0.75, y, w: 1.3, h: 0.52, fontSize: 15, bold: true, color: C.accent3, valign: "middle" });
      tx(s, f, { x: 2.1, y, w: 4.4, h: 0.52, fontSize: 14, fontFace: L.CODE, color: C.text1, valign: "middle" });
      tx(s, r, { x: 6.6, y, w: 6.0, h: 0.52, fontSize: 14, color: C.text1, valign: "middle" });
    });
  }

  // conclusions chain
  {
    const s = D.slide("Four conclusions that chain",
      "C4 is the one we want. C1 to C3 are carried along because the next step needs them. In seq, F₂ is translated first; its outputs are exactly what the F₁ step " +
      "needs as premises. C1, n ≤ n₁, plus Fresh.mono gives ρ fresh below n₁. C2, φ₂ independent of tags ≥ n₁, is P8 for F₁, whose continuation is φ₂. " +
      "C3 turns 'K is Mono' into 'φ₂ is Mono', which C4 for F₁ assumes. Each conclusion turns a guarantee about the input continuation into the same guarantee about the output formula.");
    const conc = [["C1", "n ≤ n′", "the counter only grows"], ["C2", "φ.Indep n′", "no free tags ≥ n′"], ["C3", "Mono K → Mono φ", "downward-closed in, downward-closed out"], ["C4", "the contract", "query match ⇔ formula"]];
    conc.forEach(([c, f, d], k) => {
      const x = 0.6 + k * 3.05;
      card(s, C, x, 1.45, 2.9, 1.3, { fill: k === 3 ? C.accent3 : C.text2, transparency: k === 3 ? 0 : 0 });
      tx(s, [{ text: c + "  ", options: { bold: true, fontSize: 18 } }, { text: f, options: { fontFace: L.MATH, breakLine: true } }, { text: d, options: { fontSize: 13 } }],
        { x: x + 0.12, y: 1.52, w: 2.7, h: 1.18, fontSize: 16, color: C.background1 });
    });
    // seq chaining diagram
    tx(s, "seq:  F₂ first, then F₁ with K := φ₂", { x: 0.6, y: 3.0, w: 12.1, h: 0.4, fontSize: 16, bold: true, color: C.text1 });
    card(s, C, 0.6, 3.5, 4.4, 2.75, { fill: C.accent1, transparency: 88, line: C.accent1 });
    card(s, C, 8.3, 3.5, 4.4, 2.75, { fill: C.accent2, transparency: 88, line: C.accent2 });
    tx(s, [{ text: "IH for F₂", options: { bold: true, color: C.accent1, breakLine: true } }, { text: "Pat.Tr ρ Δ F₂ K n φ₂ n₁", options: { fontFace: L.CODE, fontSize: 12 } }],
      { x: 0.75, y: 3.6, w: 4.1, h: 0.8, fontSize: 15, color: C.text1 });
    tx(s, [{ text: "IH for F₁ needs", options: { bold: true, color: C.accent2, breakLine: true } }, { text: "Pat.Tr ρ Δ F₁ φ₂ n₁ φ n′", options: { fontFace: L.CODE, fontSize: 12 } }],
      { x: 8.45, y: 3.6, w: 4.1, h: 0.8, fontSize: 15, color: C.text1 });
    const rows = [["C1:  n ≤ n₁", "P7:  ρ.Fresh n₁", "+ Fresh.mono"], ["C2:  φ₂.Indep n₁", "P8:  φ₂.Indep n₁", ""], ["C3:  Mono K → Mono φ₂", "C4 hyp.:  Mono φ₂", ""]];
    rows.forEach(([l, r, lab], k) => {
      const y = 4.45 + k * 0.55;
      tx(s, l, { x: 0.75, y, w: 4.1, h: 0.45, fontSize: 15, color: C.text1, valign: "middle", margin: 0 });
      tx(s, r, { x: 8.45, y, w: 4.1, h: 0.45, fontSize: 15, color: C.text1, valign: "middle", margin: 0 });
      arrow(s, C, 5.0, y + 0.225, 8.3, y + 0.225, { color: C.accent3, width: 2.5 });
      if (lab) tx(s, lab, { x: 5.55, y: y - 0.2, w: 2.2, h: 0.35, fontSize: 12, color: C.accent3, align: "center", fontFace: L.CODE });
    });
  }

  // Fresh Indep Mono
  {
    const s = D.slide("Fresh, Indep and Mono",
      "Three invariants. Fresh: ρ maps no source name to a tag at or above n, so allocating new tags from n can never collide. It is conservative: " +
      "with ρ = [a ↦ inl x, b ↦ #0, c ↦ #3], ρ is fresh below n exactly for n ≥ 4, even though one local at n = 2 would happen to be safe. " +
      "Indep: K's truth does not change if we change the values of any block of tags from n upward; informally, K has no free tags ≥ n. " +
      "It is for every k ≥ n because K may be pushed under several nested ∃ blocks. Mono: needed by &, as we saw. C3 is an implication, not 'φ is always Mono', " +
      "because tr(ε, K) = K passes the continuation through unchanged: the translation preserves Mono but cannot create it. At the top, ⊤ is Mono.");
    box(s, C, 0.6, 1.45, 3.95, 3.0, "ρ.Fresh n",
      [{ text: "ρ maps no name to a tag ≥ n", options: { bold: true, breakLine: true } },
       { text: "New tags never clash with ρ.", options: { breakLine: true } },
       { text: "ρ = [a ↦ inl x, b ↦ #0, c ↦ #3]", options: { fontFace: L.CODE, fontSize: 12, breakLine: true } },
       { text: "fresh below n  ⇔  n ≥ 4  (conservative)" }],
      { fontSize: 14, titleColor: C.accent2, bullets: false });
    box(s, C, 4.7, 1.45, 3.95, 3.0, "K.Indep n",
      [{ text: "K ignores tags ≥ n", options: { bold: true, breakLine: true } },
       { text: "Changing any block of tags from k ≥ n leaves K's truth unchanged.", options: { breakLine: true } },
       { text: "K is built outside a body, then placed under its ∃#n…: no capture. “Every k ≥ n” because bodies nest." }],
      { fontSize: 14, titleColor: C.accent2, bullets: false });
    box(s, C, 8.8, 1.45, 3.9, 3.0, "Mono K",
      [{ text: "true at p ⇒ true at q ≤ p", options: { bold: true, breakLine: true } },
       { text: "Needed by & (max).", options: { breakLine: true } },
       { text: "C3 is “Mono in ⇒ Mono out”,", options: { breakLine: true } },
       { text: "not “always Mono”, because", options: { breakLine: true } },
       { text: "tr(ε, K) = K", options: { fontFace: L.MATH, breakLine: true } },
       { text: "passes K through unchanged." }],
      { fontSize: 14, titleColor: C.accent3, bullets: false });
    card(s, C, 0.6, 4.7, 12.1, 1.3, { fill: C.background2 });
    tx(s, [{ text: "Twins: ", options: { bold: true } }, { text: "Fresh is about the renaming (no clash), Indep about the continuation (no capture). " },
           { text: "Both are kept true by C1 and C2. ", options: {} }, { text: "Mono starts true (⊤ at the top) and C3 carries it down.", options: { bold: true } }],
      { x: 0.8, y: 4.7, w: 11.7, h: 1.3, fontSize: 16, color: C.text1, valign: "middle" });
  }

  // skeleton
  {
    const s = D.slide("Proof skeleton",
      "Strong induction on N, the program length; inside, structural induction on the pattern. ε and actions are direct; for the action case C4 is arithmetic " +
      "about two descriptions of one event: j on the query side, k = j - 1 on the formula side. seq, alt, both use the structural hypotheses. " +
      "Invocation escapes to a smaller N: the callee's body is checked against the tail. That is the only place well-formedness is used: the formula gives the callee " +
      "the renaming ofParams, the semantics a fresh LEnv.empty.bind; they agree only on parameters, and Declared plus the coincidence lemma make that enough. " +
      "Everything bottoms out in QAct.sat_toAtom: the translated atom holds under ξ iff the query action under ξ ∘ ρ is the action at i. " +
      "ξ ∘ ρ: ρ turns source names into formula variables, ξ formula variables into locations.");
    const n = (x, y, w, t, col, fs) => {
      card(s, C, x, y, w, 0.75, { fill: col, transparency: 85, line: col });
      tx(s, t, { x, y, w, h: 0.75, fontSize: fs || 14, bold: true, color: C.text1, align: "center", valign: "middle" });
    };
    n(3.6, 1.45, 6.1, "strong induction on N = program length", C.accent3, 15);
    line(s, C, 6.65, 2.2, 6.65, 2.5);
    n(3.6, 2.5, 6.1, "structural induction on the pattern F", C.accent2, 15);
    line(s, C, 4.5, 3.25, 1.9, 3.65); line(s, C, 6.65, 3.25, 6.65, 3.65); line(s, C, 8.8, 3.25, 11.1, 3.65);
    n(0.6, 3.65, 3.3, "ε, a: direct", C.accent1);
    n(4.75, 3.65, 3.8, "seq, alt, both: structural IH", C.accent1);
    n(9.4, 3.65, 3.3, "Q(z₁, …, zₖ): IH at |Δ′| < N", C.accent5);
    box(s, C, 9.4, 4.55, 3.3, 1.75, "Uses WF here", "ofParams vs LEnv.empty.bind agree on params; Declared + coincidence make that enough.", { fontSize: 13, titleColor: C.accent5 });
    box(s, C, 0.6, 4.55, 8.6, 1.75, "Base fact: QAct.sat_toAtom",
      [{ text: "(a.toAtom ρ) holds at i under ξ   ⇔   t[i] = a.inst (ξ ∘ ρ)", options: { fontFace: L.MATH, bold: true, breakLine: true } },
       { text: "ρ = [a ↦ inl x, y ↦ #0],  ξ = [inl x ↦ 5, #0 ↦ 7]:  ξ ∘ ρ = [a ↦ 5, y ↦ 7]", options: { fontFace: L.MATH, breakLine: true } },
       { text: "retn(#0, inl x) under ξ  and  Retn(y, a) under ξ ∘ ρ  both demand  ret(7, 5)." }],
      { fontSize: 14, titleColor: C.accent3, bullets: false });
  }

  // existence etc
  {
    const s = D.slide("Existence, computation, trust",
      "Correctness alone says any derivation is right. exists_all shows a derivation always exists for well-formed programs, by the same induction, " +
      "constructing instead of consuming. Query.exists_tr_correct combines them. The computable version: Query.tr returns the formula, " +
      "Query.tr_computed_correct says it succeeds and is correct. Trust: #print axioms on the headline theorems shows only propext, Classical.choice, Quot.sound; " +
      "the computation-equivalence lemmas need not even choice. No sorry anywhere.");
    const cards = [
      ["exists_all", "For well-formed programs a derivation always exists (same induction, constructing)."],
      ["Query.exists_tr_correct", "Some φ exists, and it is semantics-preserving."],
      ["Query.tr_computed_correct", "Query.tr Δ q = some φ, and that φ is semantics-preserving."],
    ];
    cards.forEach(([h, b], k) => box(s, C, 0.6 + k * 4.1, 1.45, 3.9, 1.6, h, b, { fontSize: 14, titleColor: C.accent3, titleSize: 15 }));
    const stats = [["0", "sorry"], ["3", "standard axioms only"], ["6", "example formulas checked by #guard"]];
    stats.forEach(([n, l], k) => {
      const x = 0.6 + k * 4.1;
      tx(s, n, { x, y: 3.3, w: 3.9, h: 1.3, fontSize: 64, bold: true, color: C.accent3, align: "center", fontFace: "Cambria" });
      tx(s, l, { x, y: 4.6, w: 3.9, h: 0.45, fontSize: 15, color: C.text2, align: "center" });
    });
    code(s, C, "#print axioms Query.tr_correct   -- [propext, Classical.choice, Quot.sound]", 0.6, 5.4, 12.1, 0.6, { fontSize: 14, tag: false });
  }

  // ════════════════════════ Section 7
  D.section("Wrap-up", 7, "Decisions, limitations, and where to look", "What was decided, what the language cannot say, and where everything lives.");

  {
    const s = D.slide("Design decisions",
      "The decisions reviewed in the walkthrough. Kept: the final snapshot for ac/sk, subsequence matching without call/return pairing, whole-trace except, " +
      "shared literal locations under taint, and exclusivity as soundness only. Changed: removal of the unused and " +
      "slightly wrong Query.Safe. Added: the lower_start lemma and the computable translation.");
    const rows = [
      ["Final-snapshot ac / sk", "kept", "harness prefix: “marked at some point” = “marked before”"],
      ["Subsequence matching, no call/ret pairing", "kept", "over-approximation, fine for finding vulnerabilities"],
      ["except over the whole trace", "kept", "sanitizers via output (write-once); in-place translation"],
      ["Shared literal locations under taint", "kept", "marking a constant is the author's responsibility"],
      ["Exclusivity: soundness only", "kept", "no consumer yet; converse false in general"],
      ["Query.Safe / Pat.bound removed", "changed", "unused, and wrong for invocations"],
      ["lower_start, computable Query.tr", "added", "formalise “from 0”; print the formulas"],
    ];
    rows.forEach(([d, st, w], k) => {
      const y = 1.45 + k * 0.66;
      card(s, C, 0.6, y, 12.1, 0.58, { fill: k % 2 ? C.background1 : C.background2 });
      tx(s, d, { x: 0.75, y, w: 4.9, h: 0.58, fontSize: 14, bold: true, color: C.text1, valign: "middle" });
      pill(s, C, st, 5.75, y + 0.13, st === "kept" ? C.accent4 : C.accent6, { w: 1.0 });
      tx(s, w, { x: 6.95, y, w: 5.7, h: 0.58, fontSize: 14, color: C.text1, valign: "middle" });
    });
  }

  {
    const s = D.slide("Limitations and future work",
      "What the language cannot say, and what is left. No recursion or iteration: unbounded heap paths are not expressible; dep covers data flow. " +
      "No call/return pairing and no 'nothing in between'. ac/sk timing is lost by the snapshot. The exclusivity converse is unproved. " +
      "The model checker is being built on the automaton, not on FO-LTL; connecting walks through the labelled automaton to query satisfaction is the next step.");
    const items = [
      ["No recursion, no Kleene star", "Unbounded heap paths are not expressible (dep covers data flow)."],
      ["No pairing, no “in between”", "Calls are not tied to their returns."],
      ["Taint timing", "ac / sk record that, not when."],
      ["Exclusivity converse", "Needed only for checking validity over arbitrary models."],
      ["Model checking", "Planned on the automaton (walks over the labelled graph), not on FO-LTL."],
    ];
    items.forEach(([h, b], k) => {
      const col = k % 2 ? 6.75 : 0.6, y = 1.45 + Math.floor(k / 2) * 1.75;
      box(s, C, col, y, k === 4 ? 12.1 : 5.95, 1.55, h, b, { fontSize: 15, titleColor: k === 4 ? C.accent3 : C.text2 });
    });
  }

  {
    const s = D.slide("Where to look in the code",
      "A map from topics to files. All paths are under analysis/.");
    const rows = [
      ["CoreJS/CoreJsSemantics.lean", "Act, Trc, Obs, Exec, Obs.ofRun, Obs.WF, BigStep.obs_wf"],
      ["Queries/QueryLanguage/CoreJsQuerySyntax.lean", "QAct, Pat, Pred, Inv, QBody, Query, QProg.WF"],
      ["Queries/QueryLanguage/CoreJsQuerySemantics.lean", "Pat.Sat, QBody.Sat, QProg.interp, Exec.Matches, lower_start"],
      ["Queries/QueryLanguage/CoreJsQueryTests.lean", "pTaint and query tests (matching and non-matching)"],
      ["Queries/FoLtl/CoreJsFoLtl.lean", "Atom, Ltl, Model, Ltl.Sat, atStart, exclusivity, Ltl.toStr"],
      ["Queries/FoLtl/CoreJsFoLtlTests.lean", "FO-LTL tests on eTaint"],
      ["Queries/FoLtl/CoreJsQueryToLtl.lean", "LVar, Ren, Pat.Tr, Pat.tr, correct_all, Query.tr_correct, #guard examples"],
    ];
    rows.forEach(([f, d], k) => {
      const y = 1.45 + k * 0.76;
      card(s, C, 0.6, y, 12.1, 0.66, { fill: k % 2 ? C.background1 : C.background2 });
      tx(s, f, { x: 0.75, y, w: 5.6, h: 0.66, fontSize: 13, fontFace: L.CODE, bold: true, color: C.accent1, valign: "middle" });
      tx(s, d, { x: 6.45, y, w: 6.2, h: 0.66, fontSize: 14, color: C.text1, valign: "middle" });
    });
  }

  // ════════════════════════ Appendix
  D.setSection("Appendix");
  {
    const s = D.slide("Appendix: symbols",
      "A glossary of the symbols used throughout.");
    const g = [
      ["t", "trace as a list, e.trc.toList"], ["σ", "observation (val, dep, ac, sk)"], ["ξ", "valuation: Var → Loc (query) or LVar → Loc (formula)"],
      ["ρ", "renaming Var → LVar: how a source name is written"], ["Θ", "interpretation of invocations: QName → List Loc → Nat → Nat → Prop"],
      ["i, j, k", "boundaries 0 … |t|"], ["K", "continuation: what must hold after the pattern"], ["n, n′", "fresh-tag counter before / after"],
      ["#k", "fresh tag Sum.inr k"], ["Δ", "query program (list), usually the tail after q"],
    ];
    g.forEach(([a, b], k) => {
      const x = 0.6 + (k % 2) * 6.1, y = 1.45 + Math.floor(k / 2) * 1.05;
      card(s, C, x, y, 5.95, 0.9, { fill: C.background2 });
      tx(s, a, { x: x + 0.12, y, w: 1.0, h: 0.9, fontSize: 22, bold: true, color: C.accent3, valign: "middle", fontFace: L.MATH });
      tx(s, b, { x: x + 1.15, y, w: 4.7, h: 0.9, fontSize: 14, color: C.text1, valign: "middle" });
    });
  }
  {
    const s = D.slide("Appendix: reading the Lean",
      "A short guide to Lean notation on the slides.");
    const g = [
      ["{x y}", "implicit arguments: Lean infers them"],
      ["inductive R … : … → Prop", "a relation defined by rules (constructors)"],
      ["f a b", "application, no parentheses: Θ Q ls i j"],
      ["A → B → C", "premises chained: A and B imply C"],
      ["Option α", "some a or none (e.g. except, Pat.tr's result)"],
      ["ξ ∘ ρ", "composition: first ρ, then ξ"],
      ["Sum.inl / Sum.inr", "the two sides of Var ⊕ Nat"],
      ["Prop vs computable", "a relation in Prop cannot be run; a def can (#eval, #guard)"],
    ];
    g.forEach(([a, b], k) => {
      const x = 0.6 + (k % 2) * 6.1, y = 1.45 + Math.floor(k / 2) * 1.3;
      card(s, C, x, y, 5.95, 1.0, { fill: C.background2 });
      tx(s, [{ text: a, options: { fontFace: L.CODE, bold: true, color: C.accent2, breakLine: true } }, { text: b }], { x: x + 0.15, y, w: 5.65, h: 1.0, valign: "middle", fontSize: 15, color: C.text1 });
    });
  }
};
