package okay.proof

import okay.effects.*
import okay.effects.std.*
import Formula.*
import Term.*

/** an inference step as an effect: the kernel its handler, interceptors in between — seeing, refusing, never forging */
class EffectsSuite extends munit.FunSuite:
  val k = Kernel(Bank.policy)
  val goal = And(Lt(I(2), I(5)), Le(I(5), I(5)))

  def proof[R[_]: Has[Infer]]: Thm ! R =
    for
      a <- Infer.compute[R](Lt(I(2), I(5)))
      b <- Infer.compute[R](Le(I(5), I(5)))
      t <- Infer.andI[R](a, b)
    yield t

  test("a proof is a program of steps; the kernel, its handler, makes each theorem") {
    assertEquals(run(Infer.by(k)(proof[Infer])).map(_.concl), Right(goal))
  }

  test("OBSERVE: every step seen, in order — an audit of the proof") {
    type Row[X] = (Writer % String + Infer)[X]
    val audited = observe[Infer, Row, Thm](proof[Row])(new Observe[Infer, Row]:
      def apply[X](op: Infer[X]): Unit ! Row = op match
        case Infer.Step(r) => tell[String, Row](r.productPrefix)
        case Infer.Refuse(why) => tell[String, Row](s"refused: $why"))
    val (log, result) = run(writer[String](Infer.by(k)(audited)))
    assertEquals(log, List("Compute", "Compute", "AndI"))
    assertEquals(result.map(_.concl), Right(goal))
  }

  test("AROUND, refusing: a rule vetoed stops the proof") {
    val vetoed = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
      def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
        case Infer.Step(Rule.AndI(_, _)) => Infer.refuse[Infer]("conjunctions are not allowed here")
        case _ => proceed)
    assertEquals(run(Infer.by(k)(vetoed)).map(_.concl), Left("conjunctions are not allowed here"))
  }

  test("FORGING by another true theorem in an answer's place: refused, it was not made from the step") {
    val forged = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
      def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
        case Infer.Step(Rule.AndI(_, _)) => Infer.step[Infer](Rule.Compute(True))
        case _ => proceed)
    val got = run(Infer.by(k)(forged))
    assert(got.left.exists(_.contains("not made from it")), got.toString)
  }

  test("FORGING by another kernel's theorem — made from the very step, under a theory of the forger's: refused") {
    val lax = Kernel(Theory("lax", "anything" -> Lt(I(5), I(2))))
    val forged = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
      def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
        case Infer.Step(r @ Rule.Compute(_)) => pure(lax.derive(r).toOption.get)
        case _ => proceed)
    val got = run(Infer.by(k)(forged))
    assert(got.left.exists(_.contains("another kernel")), got.toString)
    // and as the result itself
    val whole = around[Infer, Infer, Thm](Infer.axiom[Infer]("anything"))(new Around[Infer, Infer]:
      def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
        case Infer.Step(r) => pure(lax.derive(r).toOption.get)
        case _ => proceed)
    assert(run(Infer.by(k)(whole)).left.exists(_.contains("another kernel")))
  }

  test("a cache in front of the kernel is fine: an answer made from the step, by the kernel") {
    val seen = scala.collection.mutable.Map.empty[Rule, Thm]
    val cached = around[Infer, Infer, Thm](proof[Infer])(new Around[Infer, Infer]:
      def apply[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
        case Infer.Step(r) => seen.get(r) match
          case Some(t) => pure(t)
          case None => proceed.map { t => seen(r) = t; t }
        case _ => proceed)
    assertEquals(run(Infer.by(k)(cached)).map(_.concl), Right(goal))
  }
