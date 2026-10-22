# Proofs as programs, steps as an effect

A proof is a program of okay-simple's that performs `Infer.Step(rule)`; the kernel is the handler that answers each
step (`Infer.by(kernel)`). So whatever okay-simple does with an effect — interception, audit, a journal — a proof has.

```scala
import okay.effects.*
import okay.effects.std.*
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val kernel = Kernel(Theory.empty)
val goal = And(Lt(I(2), I(5)), Le(I(5), I(5)))

def proof[R[_]: Has[Infer]]: Thm ! R =
  for
    a <- Infer.compute[R](Lt(I(2), I(5)))
    b <- Infer.compute[R](Le(I(5), I(5)))
    t <- Infer.andI[R](a, b)
  yield t

assert(run(Infer.by(kernel)(proof[Infer])).map(_.concl) == Right(goal))
```

## Audit: every step seen

```scala
type Audited[X] = (Writer % String + Infer)[X]
val audited = observe[Infer, Audited, Thm](proof[Audited])(new Observe[Infer, Audited]:
  def apply[X](op: Infer[X]): Unit ! Audited = op match
    case Infer.Step(r) => tell[String, Audited](r.productPrefix)
    case Infer.Refuse(why) => tell[String, Audited](s"refused: $why"))
val (log, result) = run(writer[String](Infer.by(kernel)(audited)))
assert(log == List("Compute", "Compute", "AndI"))
```

## Control: a rule vetoed

```scala
val vetoed = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
  def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
    case Infer.Step(Rule.AndI(_, _)) => Infer.refuse[Infer]("no conjunctions here")
    case _ => proceed)
assert(run(Infer.by(kernel)(vetoed)) == Left("no conjunctions here"))
```

## And no forging

An interceptor answering a step with another theorem — true, but not made from that step — is refused where the step
was performed (`t.by eq rule`); one answering with a theorem of another kernel (of a theory of its own) is refused by
every rule and by `Infer.by`:

```scala
val forged = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
  def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
    case Infer.Step(Rule.AndI(_, _)) => Infer.step[Infer](Rule.Compute(True))
    case _ => proceed)
assert(run(Infer.by(kernel)(forged)).left.exists(_.contains("not made from it")))

val lax = Kernel(Theory("lax", "anything" -> Lt(I(5), I(2))))
val foreign = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
  def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
    case Infer.Step(r @ Rule.Compute(_)) => pure(lax.derive(r).toOption.get)
    case _ => proceed)
assert(run(Infer.by(kernel)(foreign)).left.exists(_.contains("another kernel")))
```

So an interceptor can see, count, refuse, answer from a cache — and cannot make a false theorem. Why: [trust](trust.md).

## A guarded operation

An effect of one's own whose operation runs only with a theorem that it is allowed — of the policy's kernel, about
exactly this operation, from facts the guard knows. `PolicySuite`'s `Pay.Transfer` is one; the guard is an `around`:

```text
around[Pay, R, A](p)(new Around[Pay, R]:
  def apply[X](op: Pay[X], proceed: X ! R): X ! R = op match
    case Pay.Transfer(u, a, amount, t) =>
      if policyKernel.owns(t) && t.concl == mayTransfer(u, a, amount) && t.hyps.subsetOf(known) then proceed
      else refuse(...))
```
