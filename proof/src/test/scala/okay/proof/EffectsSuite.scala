package okay.proof

import okay.scala3.*
import okay.scala3.std.*
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
    val audited = observe[Infer, Row, Thm](proof[Row])([X] => (op: Infer[X]) => op match
        case Infer.Step(r) => Writer.tell[String, Row](r.productPrefix)
        case Infer.Refuse(why) => Writer.tell[String, Row](s"refused: $why"))
    val (log, result) = run(Writer.run(Infer.by(k)(audited)))
    assertEquals(log, List("Compute", "Compute", "AndI"))
    assertEquals(result.map(_.concl), Right(goal))
  }

  test("AROUND, refusing: a rule vetoed stops the proof") {
    def veto[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
      case Infer.Step(Rule.AndI(_, _)) => Infer.refuse[Infer]("conjunctions are not allowed here")
      case _ => proceed
    val vetoed = around[Infer, Infer, Thm](proof[Infer])([X] => (op: Infer[X], go: X ! Infer) => veto(op, go))
    assertEquals(run(Infer.by(k)(vetoed)).map(_.concl), Left("conjunctions are not allowed here"))
  }

  test("FORGING by another true theorem in an answer's place: refused, it was not made from the step") {
    def forge[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
      case Infer.Step(Rule.AndI(_, _)) => Infer.step[Infer](Rule.Compute(True))
      case _ => proceed
    val forged = around[Infer, Infer, Thm](proof[Infer])([X] => (op: Infer[X], go: X ! Infer) => forge(op, go))
    val got = run(Infer.by(k)(forged))
    assert(got.left.exists(_.contains("not made from it")), got.toString)
  }

  test("FORGING by another kernel's theorem — made from the very step, under a theory of the forger's: refused") {
    val lax = Kernel(Theory("lax", "anything" -> Lt(I(5), I(2))))
    def computed[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
      case Infer.Step(r @ Rule.Compute(_)) => pure(lax.derive(r).toOption.get)
      case _ => proceed
    val forged = around[Infer, Infer, Thm](proof[Infer])([X] => (op: Infer[X], go: X ! Infer) => computed(op, go))
    val got = run(Infer.by(k)(forged))
    assert(got.left.exists(_.contains("another kernel")), got.toString)
    // and as the result itself
    def every[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
      case Infer.Step(r) => pure(lax.derive(r).toOption.get)
      case _ => proceed
    val whole = around[Infer, Infer, Thm](Infer.axiom[Infer]("anything"))(
      [X] => (op: Infer[X], go: X ! Infer) => every(op, go))
    assert(run(Infer.by(k)(whole)).left.exists(_.contains("another kernel")))
  }

  test("a cache in front of the kernel is fine: an answer made from the step, by the kernel") {
    val seen = scala.collection.mutable.Map.empty[Rule, Thm]
    def cache[X](op: Infer[X], proceed: X ! Infer): X ! Infer = op match
      case Infer.Step(r) => seen.get(r) match
        case Some(t) => pure(t)
        case None => proceed.map { t => seen(r) = t; t }
      case _ => proceed
    val cached = around[Infer, Infer, Thm](proof[Infer])([X] => (op: Infer[X], go: X ! Infer) => cache(op, go))
    assertEquals(run(Infer.by(k)(cached)).map(_.concl), Right(goal))
  }
