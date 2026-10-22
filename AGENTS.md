# okay-proof — notes for agents

- Scala 3.3.8, sbt; depends on okay-simple's PUBLISHED 0.1.0 (resolver in build.sbt), not on the working tree of
  `~/work/my/okay-simple` (another session may be editing it). `sbt test` must pass before a commit; commits carry no
  Co-Authored-By lines.
- THE TRUSTED BASE is `Kernel.scala` (`Kernel.derive`, `Arithmetic`), `Logic.scala` and `Linear.scala` (linear forms,
  read by `Norm`, `LinComb`, `Tighten`); `docs/trust.md` says why
  nothing else is. Any change there: a test of what the rule refuses, not only what it gives (`KernelSuite`). Do not
  add a way to make a `Thm` outside `Kernel` (its constructor is `private[Kernel]`), nor to read one from data other
  than by `Certificate.check` (which derives every step again).
- The effect `Infer`: `Infer.step` accepts an answer only if `t.by eq rule`; `Infer.by` refuses a result of another
  kernel. `EffectsSuite` tries to forge both ways — keep it.
- Scala's precedence goes by an operator's first character: `==>` would bind tighter than `&&`, so implication is the
  word `implies` (it cost a policy read as `… ∧ (last → head)`).
- Speed (`Bench`, `ProfileDecision` for a profiler: `java -XX:StartFlightRecording=… -cp <Test/fullClasspath>
  okay.proof.ProfileDecision 15`): 2026-10-22 a decision 8.3 µs, refused 4.8 µs, from bounds 12.9 µs, ∀-out 263 ns, ∧ 17 ns,
  compute 108 ns, Norm 358 ns; certificates 18 µs written, 26 µs checked. What helped: hashes mixed from the children's cached ones (not
  `caseClassHash`, which walks the product boxed), `union` that makes nothing when a side is empty, sorts checked by
  loops; what did not: free variables computed eagerly (∀-out 315 → 523 ns: reverted, they stay `lazy`).
- LINEAR ARITHMETIC (2026-10-22): `Linarith` (untrusted) finds Farkas multipliers by Fourier–Motzkin, with the
  integers' tightening of the start rows and of derived ones, over the premises sharing atoms with the goal (all for a
  constant goal); it emits `LinComb`, `Compute` of the false constant's negation, `NotE`, `NotI`, `Classic`. An
  equation is two refutations and `Antisym`. `Auto`: a closed computable goal ends its branch (true: `compute`; false:
  no proof); a value a fact gives first; `Linarith` for a comparison next; rules last — that order keeps a decision
  at ~8 µs (with `Linarith` first it was 21 µs).
- LEMMAS: `Lemmas(kernel)`, proved on first use and kept per kernel; `LemmasSuite` checks each closed, of no
  hypothesis, owned. Add a lemma by proving it there (`arith` for linear ones), never as an axiom.
- `given` and `then` are Scala 3 keywords: not parameter names.
