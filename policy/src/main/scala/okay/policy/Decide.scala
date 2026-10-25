package okay.policy

import okay.proof.{Certificate, Formula, Infer, Thm}
import okay.scala3.*

/**
 * A DECISION: the verdict; the rules that gave it; the theorem that proves it (every verdict but the default deny);
 * the reasons — the rules' `because`, or, for the default, why each rule did not apply; the changes of state to make
 * if the call goes ahead.
 */
final case class Decision(verdict: Verdict, rules: List[TRule], theorem: Option[Thm], reasons: List[String],
                          updates: List[StateChange]):
  /** the facts the decision rests on: its theorem's hypotheses */
  def facts: Set[Formula] = theorem.fold(Set.empty)(_.hyps)
  /** the proof, written: what the audit keeps, checked again anywhere by `Certificate.check` */
  lazy val certificate: Option[String] = theorem.map(Certificate.of)
  override def toString: String =
    s"${verdict.word}${if reasons.isEmpty then "" else reasons.mkString(": ", "; ", "")}"

/** A POLICY READY TO DECIDE: checked, its theory and kernel made, once */
final class Compiled(val checked: Checked):
  val theorize: Theorize = Theorize(checked)
  val prove: Prove = Prove(theorize)
  def kernel = theorize.kernel

object Compiled:
  def apply(text: String): Either[List[Problem], Compiled] = Types(text).map(new Compiled(_))

/**
 * DECIDING A CALL: the facts and states its candidate rules read, asked at once (`Facts`, `States`); each rule
 * evaluated; the verdict by precedence — a deny, then an allow with a condition, then an ask, else the default deny;
 * the winning rule's decision proved by the kernel. A rule whose proof the kernel refuses does not apply: fail closed.
 */
object Decide:
  def apply[R[_]](policy: Compiled, call: Call)(using In[Facts, R], In[States, R]): Decision ! R =
    policy.checked.rulesOf.get(call.tool) match
      case None => pure(Decision(Verdict.Deny, Nil, None, List(s"no rule decides ${call.tool}"), Nil))
      case Some(rules) =>
        val env = call.env
        val counts = policy.checked.countsOf.getOrElse(call.tool, Nil)
        def read(when: Option[TCond], updates: List[TUpdate]) =
          when.toList.flatMap(Eval.refs(_, env)) ++ updates.flatMap(u => u.key.flatMap(Eval.refs(_, env)) ++
            Eval.refs(u.value, env) ++ List(true -> Eval.ref(u.state, u.key, env)))
        val needed = (rules.flatMap(r => read(r.when, r.updates)) ++ counts.flatMap(c => read(c.when, c.updates)))
          .distinct
        val (states, facts) = needed.partition(_._1)
        for
          fs <- Facts.ask[R](facts.map(_._2))
          ss <- States.read[R](states.map(_._2))
        yield decide(policy, call, rules, counts, Known(fs, ss))

  /** the decision, with what is known */
  def decide(policy: Compiled, call: Call, rules: List[TRule], counts: List[TCount], known: Known): Decision =
    val env = call.env
    def applies(r: TRule): Boolean = r.when.forall(c => Eval.holds(c, env, known).contains(true))
    def proved(r: TRule): Either[String, Thm] =
      run(Infer.by(policy.kernel)(policy.prove.decision[Infer](r, call, known)))
    def first(v: Verdict): Option[(TRule, Either[String, Thm])] =
      rules.iterator.filter(r => r.verdict == v && applies(r)).map(r => (r, proved(r))).find(_._2.isRight)
    def made(v: Verdict, r: TRule, thm: Thm): Decision =
      val with_ = rules.filter(x => x.verdict == v && applies(x))
      val counted = if v == Verdict.Deny then Nil
        else counts.filter(c => c.when.forall(w => Eval.holds(w, env, known).contains(true)))
      val changes = (with_.flatMap(_.updates) ++ counted.flatMap(_.updates)).map(u => change(u, env, known))
      if changes.exists(_.isEmpty) then
        Decision(Verdict.Deny, Nil, None, List(s"an update's value is unknown, so the call is denied"), Nil)
      else Decision(v, r :: with_.filterNot(_ eq r), Some(thm), with_.flatMap(_.because).distinct, changes.flatten)
    first(Verdict.Deny) match
      case Some((r, Right(t))) => made(Verdict.Deny, r, t)
      case _ => first(Verdict.Allow) match
        case Some((r, Right(t))) => made(Verdict.Allow, r, t)
        case _ => first(Verdict.Ask) match
          case Some((r, Right(t))) => made(Verdict.Ask, r, t)
          case _ =>
            val why = rules.filter(_.when.isDefined).flatMap { r =>
              val where = s"${r.verdict.word} (line ${r.source.pos.line})"
              val reasons = Eval.why(r.when.get, env, known)
              if reasons.nonEmpty then List(s"$where: ${reasons.mkString("; ")}")
              else proved(r).left.toOption.map(e => s"$where: its proof was refused: $e")
            }
            Decision(Verdict.Deny, Nil, None, why.ifEmpty(List("no rule allows it")), Nil)

  extension (l: List[String]) private def ifEmpty(d: => List[String]): List[String] = if l.isEmpty then d else l

  private def change(u: TUpdate, env: Map[String, Value], known: Known): Option[StateChange] =
    Eval.value(u.value, env, known).map(StateChange(Eval.ref(u.state, u.key, env), u.change, _))

  /** decided, and its changes made if allowed: what a guard does for a call */
  def enforce[R[_]](policy: Compiled, call: Call)(using In[Facts, R], In[States, R]): Decision ! R =
    apply[R](policy, call).flatMap(d => (if d.verdict == Verdict.Allow then States.update[R](d.updates) else unit[R])
      .as(d))

  /** an asked call approved by a human: its changes made */
  def approve[R[_]](d: Decision)(using In[States, R]): Unit ! R =
    if d.verdict == Verdict.Ask then States.update[R](d.updates) else unit[R]
