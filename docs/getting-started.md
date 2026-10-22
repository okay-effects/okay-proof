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
val User = Sort.Named("User")
val Account = Sort.Named("Account")
def const(name: String, sort: Sort): Term = Ap(Fn(name, Nil, sort), Nil)
val ann = const("ann", User)
val acc1 = const("acc1", Account)
val owns = Pred("owns", List(User, Account))
val mayTransfer = Pred("mayTransfer", List(User, Account, Sort.Dec))
val balance = Fn("balance", List(Account), Sort.Dec)
def dec(s: String): Term = D(BigDecimal(s))

val (u, a, amt) = (V("u", User), V("a", Account), V("amt", Sort.Dec))
val policy = Theory("bank",
  "transfer" -> Formula.all(u, a, amt)(
    P(owns, List(u, a)) && Le(dec("0"), amt) && Le(amt, Ap(balance, List(a))) implies P(mayTransfer, List(u, a, amt))))

val bank = Kernel(policy)
val facts = List(P(owns, List(ann, acc1)), Eq(Ap(balance, List(acc1)), dec("250.00")))
val goal = P(mayTransfer, List(ann, acc1, dec("100.00")))

val Right(Some(decision)) = Auto.prove(bank, facts, goal): @unchecked
assert(decision.concl == goal)
assert(decision.hyps.subsetOf(facts.toSet))                          // exactly the facts it rests on
assert(Auto.prove(bank, facts, P(mayTransfer, List(ann, acc1, dec("300.00")))) == Right(None))  // more than the balance
```

`a && b implies c` is `(a ∧ b) → c`: `implies` is a word, so it binds the loosest.

## Its certificate

The proof as JSON — checked again by deriving every step, here or in another process, another language:

```scala
val certificate = Certificate.of(decision)
assert(Certificate.check(certificate, Kernel(policy)).map(_.concl) == Right(goal))
assert(Certificate.check(certificate.replace("\"100\"", "\"300\""), Kernel(policy)).isLeft)   // changed: refused
```

## Next

[The logic](logic.md), [arithmetic](arithmetic.md), [proofs as programs](effects.md), [certificates](certificates.md).
