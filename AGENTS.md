# okay-proof — notes for agents

- Scala 3.3.8, sbt; depends on okay-simple's PUBLISHED 0.1.0 (resolver in build.sbt), not on the working tree of
  `~/work/my/okay-simple` (another session may be editing it). `sbt test` must pass before a commit; commits carry no
  Co-Authored-By lines.
- THE TRUSTED BASE is `Kernel.scala` (`Kernel.derive`, `Arithmetic`) and `Logic.scala`; `docs/trust.md` says why
  nothing else is. Any change there: a test of what the rule refuses, not only what it gives (`KernelSuite`). Do not
  add a way to make a `Thm` outside `Kernel` (its constructor is `private[Kernel]`), nor to read one from data other
  than by `Certificate.check` (which derives every step again).
- The effect `Infer`: `Infer.step` accepts an answer only if `t.by eq rule`; `Infer.by` refuses a result of another
  kernel. `EffectsSuite` tries to forge both ways — keep it.
- Scala's precedence goes by an operator's first character: `==>` would bind tighter than `&&`, so implication is the
  word `implies` (it cost a policy read as `… ∧ (last → head)`).
- Speed (`Bench`, `ProfileDecision` for a profiler: `java -XX:StartFlightRecording=… -cp <Test/fullClasspath>
  okay.proof.ProfileDecision 15`): 2026-10-22 a decision 7.8 µs, refused 4.8 µs, ∀-out 266 ns, ∧ 23 ns, compute
  106 ns; certificates 18 µs written, 26 µs checked. What helped: hashes mixed from the children's cached ones (not
  `caseClassHash`, which walks the product boxed), `union` that makes nothing when a side is empty, sorts checked by
  loops; what did not: free variables computed eagerly (∀-out 315 → 523 ns: reverted, they stay `lazy`).
