package okay.proof

import okay.effects.*

/**
 * AN INFERENCE STEP AS AN EFFECT. A proof is a program performing `Infer.Step(rule)`; the kernel is the handler that
 * answers it (`Infer.by(kernel)`). Between the two any interceptor of okay-simple's may stand — `observe` for an audit
 * of every step, `around` to refuse a rule, a cache — and none of them can forge:
 *
 *  - a theorem is made by a kernel alone (`Thm`'s constructor is `Kernel`'s), so an answer is a true theorem of SOME
 *    kernel whatever answered;
 *  - `step` accepts an answer only if it was made from this very step (`t.by eq rule`): another true theorem in its
 *    place is refused;
 *  - a theorem of another kernel (another theory) is refused as a premise by every rule, and `Infer.by` refuses one as
 *    the proof's result: a theorem is trusted relative to the kernel that owns it (`Kernel.owns`).
 *
 * So what an interceptor can do is what control needs — see, count, refuse, answer from a cache — and not what would
 * undo trust.
 */
enum Infer[X]:
  case Step(rule: Rule) extends Infer[Thm]
  case Refuse(reason: String) extends Infer[Nothing]

object Infer:
  /** one step, by whoever handles `Infer`: its theorem, made from this step */
  def step[R[_]: Has[Infer]](rule: Rule): Thm ! R =
    perform[Infer](Step(rule)).flatMap { t =>
      if t.by eq rule then pure[Thm, R](t)
      else refuse[R](s"an answer to a step that was not made from it: ${t.concl}")
    }

  /** the proof stops: a reason why not */
  def refuse[R[_]: Has[Infer]](reason: String): Nothing ! R = perform[Infer](Refuse(reason))

  /** the kernel answering every step of `p`; a refused step, or a result of another kernel, the proof's failure */
  def by[R[_], Rest[_]](k: Kernel)(p: Thm ! R)(using Split[Infer, R, Rest]): Either[String, Thm] ! Rest =
    handle(p, new Handler[Infer, Rest, Thm, Either[String, Thm]]:
      def ret(t: Thm) = pure(if k.owns(t) then Right(t) else Left(s"a theorem of another kernel: ${t.concl}"))
      def op[X](op: Infer[X], kx: X => Either[String, Thm] ! Rest) = op match
        case Step(rule) => k.derive(rule) match
          case Right(t) => kx(t)
          case Left(why) => pure(Left(why))
        case Refuse(why) => pure(Left(why)))

  /** the kernel answering every step of `p`, of any value: theorems in it are the caller's to check (`owns`) */
  def checking[R[_], Rest[_], A](k: Kernel)(p: A ! R)(using Split[Infer, R, Rest]): Either[String, A] ! Rest =
    handle(p, new Handler[Infer, Rest, A, Either[String, A]]:
      def ret(a: A) = pure(Right(a))
      def op[X](op: Infer[X], kx: X => Either[String, A] ! Rest) = op match
        case Step(rule) => k.derive(rule) match
          case Right(t) => kx(t)
          case Left(why) => pure(Left(why))
        case Refuse(why) => pure(Left(why)))

  // the rules as words of a proof program
  import Rule.*
  def assume[R[_]: Has[Infer]](f: Formula): Thm ! R = step(Assume(f))
  def axiom[R[_]: Has[Infer]](name: String): Thm ! R = step(Axiom(name))
  def compute[R[_]: Has[Infer]](f: Formula): Thm ! R = step(Compute(f))
  def andI[R[_]: Has[Infer]](a: Thm, b: Thm): Thm ! R = step(AndI(a, b))
  def impI[R[_]: Has[Infer]](f: Formula, t: Thm): Thm ! R = step(ImpI(f, t))
  def impE[R[_]: Has[Infer]](imp: Thm, arg: Thm): Thm ! R = step(ImpE(imp, arg))
  def allI[R[_]: Has[Infer]](x: Term.V, t: Thm): Thm ! R = step(AllI(x, t))
  def allE[R[_]: Has[Infer]](t: Thm, by: Term): Thm ! R = step(AllE(t, by))
  def refl[R[_]: Has[Infer]](t: Term): Thm ! R = step(Refl(t))
  def subst[R[_]: Has[Infer]](eq: Thm, x: Term.V, f: Formula, t: Thm): Thm ! R = step(Subst(eq, x, f, t))

  /** `⊢ f ∨ ¬f`, derived (the logic is classical): what a proof by cases splits on */
  def cases[R[_]: Has[Infer]](f: Formula): Thm ! R =
    val goal = Formula.Or(f, Formula.Not(f))
    for
      notGoal <- assume[R](Formula.Not(goal))
      yes <- assume[R](f)
      left <- step[R](OrI1(yes, Formula.Not(f)))
      c1 <- step[R](NotE(notGoal, left))
      notF <- step[R](NotI(f, c1))
      right <- step[R](OrI2(f, notF))
      c2 <- step[R](NotE(notGoal, right))
      nn <- step[R](NotI(Formula.Not(goal), c2))
      t <- step[R](Classic(nn))
    yield t
