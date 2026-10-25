# okay-proof

A small prover for the run time, in Scala 3: a kernel of first-order logic with equality, induction and exact
arithmetic, LCF-style — a theorem is a value only the kernel makes — whose inference steps are also an EFFECT of
[okay-scala](https://github.com/okay-effects/okay-scala)'s, so a proof can be audited step by step and controlled
by interceptors without trusting them. For decisions that must be justified: a transfer allowed by a policy, a sum of
money computed with its rounding named, a limit respected — each a theorem, in microseconds, with a certificate that
another checker — okay-lean's, in Lean — checks again.

```scala
import okay.proof.*
import okay.proof.syntax.*

val User = sort("User")
val Account = sort("Account")
val (ann, acc1) = (const("ann", User), const("acc1", Account))
val owns = pred("owns", User, Account)
val mayTransfer = pred("mayTransfer", User, Account, Sort.Dec)
val spent = fn("spentToday", User)(Sort.Dec)
val (u, a, amt) = (v("u", User), v("a", Account), v("amt", Sort.Dec))

// the policy: an owner may transfer, within 1000.00 a day with what was spent today
val policy = Theory("bank", "transfer" -> forall(u, a, amt)(
  owns(u, a) && spent(u) + amt <= 1000.00 implies mayTransfer(u, a, amt)))
val bank = Kernel(policy)

// what the request knows: spent today at most 300.00 — a bound, not a value
val facts = List(owns(ann, acc1), spent(ann) <= 300.00)

val Right(Some(allowed)) = Auto.prove(bank, facts, mayTransfer(ann, acc1, 700.00)): @unchecked
assert(allowed.hyps.subsetOf(facts.toSet))                                   // the facts it rests on
assert(Auto.prove(bank, facts, mayTransfer(ann, acc1, 700.01)) == Right(None))
assert(Certificate.checkAlone(Certificate.of(allowed)).isRight)              // checked again, from JSON
```

The syntax (`okay.proof.syntax`) builds the same terms and formulas as their constructors (`P(owns, List(u, a))`,
`Le(…)`); a literal takes the sort of its place, `+` and `<=` pick the kernel's function by sort.
[The logic](docs/logic.md).

- **A small kernel** (`Kernel.scala`, `Logic.scala`, `Linear.scala`): 28 rules, each a pure check; a theorem relative
  to the theory it was made under. [The logic](docs/logic.md), [what is trusted](docs/trust.md).
- **Arithmetic, by certificate**: exact computation in one step; linear arithmetic over the rationals (complete) and
  the integers (the Omega test, complete); products of variables (as `nlinarith`). The procedures find certificates,
  the kernel checks them. [Arithmetic](docs/arithmetic.md).
- **Steps as an effect**: `Infer`, the kernel its handler — `observe` for an audit of every step, `around` for a veto,
  and no interceptor can forge a theorem. [Proofs as programs](docs/effects.md).
- **Proof search** on effects (`Auto`): rules, facts, values, bounds; the strategy a handler. [Search](docs/search.md).
- **Lemmas**, proved by the kernel, not assumed. [Lemmas](docs/lemmas.md).
- **Certificates**: a proof as JSON with its theory and digest, checked by deriving every step again — here, or by
  okay-lean's second checker in Lean, which agrees with this kernel on 806 certificates and mutants.
  [Certificates](docs/certificates.md).
- **Fast**: a decision proved in ~7 µs, refused in ~5 µs; the Omega test's hard case in 2 ms. [Speed](docs/performance.md).

Documentation: [docs/](docs/README.md) — every example compiled and run by `sbt test`.

## Build

Scala 3.3 LTS, sbt; the JVM and the browser (Scala.js); depends on okay-scala's release
(`io.github.okay-effects::okay-scala:0.1.1`, from its Maven repository on GitHub Pages — `build.sbt` has the resolver).

```text
sbt proofJVM/test                         # the kernel, arithmetic, effects, search, lemmas, certificates, the docs —
                                          # and the differential test against okay-lean's checker, when it is built
sbt proofJS/test                          # the same in the browser's JavaScript (the docs and okay-lean's on the JVM)
sbt "proofJVM/Test/runMain okay.proof.Bench"   # what it costs
```

## The family

One of the [okay-effects](https://github.com/okay-effects) family: built on okay-scala's effects; its certificates
checked a second time by [okay-lean](https://github.com/okay-effects/okay-lean), in Lean.

License: Apache 2.0.
