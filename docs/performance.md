# Speed

What a proof costs at run time. `sbt "Test/runMain okay.proof.Bench"`: each lane warmed, then the median of five
rounds; JDK 26, Apple silicon, 2026-10-22.

| | |
|---|---|
| a decision proved: a transfer under the policy, 25 steps, found by the search on effects | 7.4 µs |
| a decision refused: every branch tried | 4.5 µs |
| a decision from bounds (`spent(ann) ≤ 300.00`), by linear arithmetic | 12.6 µs |
| one step of the kernel | 20–400 ns |
| exact money arithmetic, a step (`round(1234.567 · 0.19, 2) = 234.57`) | 104 ns |
| linear arithmetic: a chain of three over `Int` | 10.2 µs |
| an equation over `Dec` (two refutations) | 17.5 µs |
| the Omega test: `3x + 5y = 1` in a box (a fresh `σ`) | 60 µs |
| the Omega test: Pugh's example, ~1000 steps, by cases | 1.9 ms |
| products: `0 ≤ p ≤ 10, 0 ≤ q ≤ 5 ⊢ p·q ≤ 50` | 107 µs |
| the lemma library, 42 lemmas proved | 0.28 ms, once a kernel |
| a certificate written (3.5 KB, the theory in it by value) / checked, every step derived again | 34 µs / 58 µs |

`ProfileDecision` runs a decision in a loop for a profiler (`java -XX:StartFlightRecording=… -cp <Test/fullClasspath>
okay.proof.ProfileDecision 15`). What made it fast, and what did not: AGENTS.md.
