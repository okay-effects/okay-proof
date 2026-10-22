# Getting started

## Get it

okay-proof is built with sbt on Scala 3.3 (LTS); it depends on okay-simple's release, from okay-simple's Maven
repository on GitHub Pages:

```text
resolvers += "okay-effects" at "https://okay-effects.github.io/okay-simple/maven"
libraryDependencies += "io.github.okay-effects" %% "okay-effects-machine" % "0.1.0"
```

Clone it and `sbt test`; your code beside it, or `sbt publishLocal` and depend on
`"io.github.okay-effects" %% "okay-proof" % "0.1.0-SNAPSHOT"`.

## A theorem, by the kernel's rules

A kernel is made for a theory (its axioms). Each rule is one call, `derive`, which checks it and gives a theorem — or
says why not:

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val k = Kernel(Theory.empty)
val small = k.derive(Rule.Compute(Lt(I(2), I(5)))).toOption.get   // computed: exact arithmetic, one step
val both = k.derive(Rule.AndI(small, small)).toOption.get
assert(both.concl == And(Lt(I(2), I(5)), Lt(I(2), I(5))))
assert(k.derive(Rule.Compute(Lt(I(5), I(2)))).isLeft)               // false: no theorem
```

A `Thm` is made by a kernel alone: there is no other way to have one.

## A decision, proved

A policy is a theory; what a request knows are facts; a decision is a theorem — proved from the facts, by the
policy's rules, found by `Auto`:

```scala
import okay.proof.syntax.*

val User = sort("User")
val Account = sort("Account")
val ann = const("ann", User)
val acc1 = const("acc1", Account)
val owns = pred("owns", User, Account)
val mayTransfer = pred("mayTransfer", User, Account, Sort.Dec)
val balance = fn("balance", Account)(Sort.Dec)

val (u, a, amt) = (v("u", User), v("a", Account), v("amt", Sort.Dec))
val policy = Theory("bank",
  "transfer" -> forall(u, a, amt)(owns(u, a) && amt >= 0 && amt <= balance(a) implies mayTransfer(u, a, amt)))

val bank = Kernel(policy)
val facts = List(owns(ann, acc1), balance(acc1) === dec("250.00"))
val goal = mayTransfer(ann, acc1, 100)

val Right(Some(decision)) = Auto.prove(bank, facts, goal): @unchecked
assert(decision.concl == goal)
assert(decision.hyps.subsetOf(facts.toSet))                          // exactly the facts it rests on
assert(Auto.prove(bank, facts, mayTransfer(ann, acc1, 300)) == Right(None))        // more than the balance
```

`okay.proof.syntax` writes formulas as they read: a symbol applied like a function, a literal taking the sort of its
place (`100` a `Dec` there), `+ - *` and `< <= > >= === =/=` picking the kernel's function by sort. It builds the
same data as the constructors — `P(owns, List(u, a))`, `Le(amt, Ap(balance, List(a)))` — and the kernel checks it
as any other. `a && b implies c` is `(a ∧ b) → c`: `implies` is a word, so it binds the loosest.

## Its certificate

The proof as JSON — checked again by deriving every step, here or in another process, another language:

```scala
val certificate = Certificate.of(decision)
assert(Certificate.check(certificate, Kernel(policy)).map(_.concl) == Right(goal))
assert(Certificate.check(certificate.replace("\"100\"", "\"300\""), Kernel(policy)).isLeft)   // changed: refused
```

## Next

[The logic](logic.md), [arithmetic](arithmetic.md), [proofs as programs](effects.md), [certificates](certificates.md).
