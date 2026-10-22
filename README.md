# okay-proof

A small prover for the run time, in Scala 3: a kernel of first-order logic with equality, induction and exact
arithmetic, LCF-style — a theorem is a value only the kernel makes — whose inference steps are also an EFFECT of
[okay-simple](https://github.com/okay-effects/okay-simple)'s, so a proof can be audited step by step and controlled
by interceptors without trusting them. For decisions that must be justified: a transfer allowed by a policy, a sum of
money computed with its rounding named, a limit respected — each a theorem, in microseconds, with a certificate that
another checker — okay-lean's, in Lean — checks again.

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val User = Sort.Named("User")
val Account = Sort.Named("Account")
def const(name: String, sort: Sort): Term = Ap(Fn(name, Nil, sort), Nil)
def dec(s: String): Term = D(BigDecimal(s))
val (ann, acc1) = (const("ann", User), const("acc1", Account))
val owns = Pred("owns", List(User, Account))
val mayTransfer = Pred("mayTransfer", List(User, Account, Sort.Dec))
val spent = Fn("spentToday", List(User), Sort.Dec)
val (u, a, amt) = (V("u", User), V("a", Account), V("amt", Sort.Dec))

// the policy: an owner may transfer, within 1000.00 a day with what was spent today
val policy = Theory("bank", "transfer" -> Formula.all(u, a, amt)(
  P(owns, List(u, a)) && Le(Ap(Fns.dadd, List(Ap(spent, List(u)), amt)), dec("1000.00")) implies P(mayTransfer, List(u, a, amt))))
val bank = Kernel(policy)

// what the request knows: spent today at most 300.00 — a bound, not a value
val facts = List(P(owns, List(ann, acc1)), Le(Ap(spent, List(ann)), dec("300.00")))

val Right(Some(allowed)) = Auto.prove(bank, facts, P(mayTransfer, List(ann, acc1, dec("700.00")))): @unchecked
assert(allowed.hyps.subsetOf(facts.toSet))                                   // the facts it rests on
assert(Auto.prove(bank, facts, P(mayTransfer, List(ann, acc1, dec("700.01")))) == Right(None))
assert(Certificate.checkAlone(Certificate.of(allowed)).isRight)              // checked again, from JSON
```

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

Scala 3.3 LTS, sbt; depends on okay-simple's release (`io.github.okay-effects::okay-effects-machine:0.1.0`, from its
Maven repository on GitHub Pages — `build.sbt` has the resolver).

```text
sbt test                                  # the kernel, arithmetic, effects, search, lemmas, certificates, the docs —
                                          # and the differential test against okay-lean's checker, when it is built
sbt "Test/runMain okay.proof.Bench"       # what it costs
```

## The family

One of the [okay-effects](https://github.com/okay-effects) family: built on okay-simple's effects; its certificates
checked a second time by [okay-lean](https://github.com/okay-effects/okay-lean), in Lean.

License: Apache 2.0.
