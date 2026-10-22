# okay-proof — the documentation

Every ```scala block in these pages is compiled and run by `sbt test` (`DocsSuite`): what you read works.

- [Getting started](getting-started.md) — a theorem by the kernel's rules, a policy decision proved, its certificate.
- [The logic](logic.md) — sorts, terms, formulas; the kernel's 28 rules, each in a line.
- [Arithmetic](arithmetic.md) — exact computation, linear arithmetic over the rationals and the integers (the Omega
  test), products of variables.
- [Proofs as programs, steps as an effect](effects.md) — `Infer`, the kernel as its handler; audit and control by
  okay-simple's interceptors; a guarded operation.
- [Proof search](search.md) — `Auto`: rules, facts, values, arithmetic; strategies as handlers.
- [Lemmas](lemmas.md) — the library: proved, not assumed.
- [Certificates](certificates.md) — a proof as JSON, its theory and digest; the second checker in Lean.
- [What is trusted](trust.md) — the trusted base, and why an effect does not widen it.
- [Speed](performance.md) — what a proof costs at run time, and how it is measured.
