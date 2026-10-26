package okay.policy

import okay.proof.{Certificate, Formula, Infer, Thm}
import okay.scala3.*

/**
 * A DECISION: the verdict; the rules that gave it; the theorem that proves it — every verdict a rule gave; none for
 * the policy's DEFAULT (`byDefault`: no rule applied — reported, with why each rule did not, not proved); the reasons
 * — the rules' `because`, or, for the default, why each rule did not apply; the changes of state to make if the call
 * goes ahead; the webhooks to notify (`webhooks`: the deciding rules' and the notices on this verdict); what it read
 * (`known`), so a later outcome — approved, refused, timed out — can be matched against the notices.
 */
final case class Decision(verdict: Verdict, rules: List[TRule], theorem: Option[Thm], reasons: List[String],
                          updates: List[StateChange], byDefault: Boolean = false, webhooks: List[String] = Nil,
                          known: Known = Known(Map.empty, Map.empty)):
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
    policy.checked.rulesFor(call.tool) match
      case rules =>
        val env = call.env
        val supplied = Call.facts(policy.checked, call)
        if supplied.malformed.nonEmpty then
          pure(Decision(Verdict.Deny, Nil, None, supplied.malformed.map("a malformed call: " + _), Nil))
        else
          val counts = policy.checked.countsFor(call.tool)
          val fromCall = Known(supplied.facts, Map.empty, supplied.lists)
          def read(when: Option[TCond], updates: List[TUpdate]) =
            when.toList.flatMap(Eval.refs(_, env, fromCall)) ++ updates.flatMap(u =>
              u.key.flatMap(Eval.refs(_, env, fromCall)) ++ Eval.refs(u.value, env, fromCall) ++
                Eval.ref(u.state, u.key, env, fromCall).map(true -> _))
          val needed = (rules.flatMap(r => read(r.when, r.updates)) ++ counts.flatMap(c => read(c.when, c.updates)))
            .distinct
          // asked: the policy's own facts and states; the call's facts it gave itself
          val (states, facts) = needed.filter((st, r) => st || policy.checked.facts.contains(r.name)).partition(_._1)
          for
            fs <- Facts.ask[R](facts.map(_._2))
            ss <- States.read[R](states.map(_._2))
          yield decide(policy, call, rules, counts, Known(fs ++ supplied.facts, ss, supplied.lists))

  /** the decision, with what is known */
  def decide(policy: Compiled, call: Call, rules: List[TRule], counts: List[TCount], known: Known): Decision =
    val d = decided(policy, call, rules, counts, known)
    val by = d.rules.flatMap(_.source.notifies)
    d.copy(webhooks = (by ++ notices(policy, call, d.verdict match
      case Verdict.Allow => NoticeOn.Allow
      case Verdict.Ask => NoticeOn.Ask
      case Verdict.Deny => NoticeOn.Deny, known)).distinct, known = known)

  /** the webhooks the notices name for an outcome of a call — its verdict, or later a person's or the time's: those on
   * that outcome, of the call's tool, whose condition holds over what the decision read */
  def notices(policy: Compiled, call: Call, outcome: NoticeOn, known: Known): List[String] =
    policy.checked.notices.filter(n => n.on == outcome &&
      (n.tools.contains(call.tool) || !policy.checked.calls.contains(call.tool) &&
        policy.checked.open(n.source.target) && policy.checked.covers(n.source.target, call.tool)) &&
      n.when.forall(c => Eval.holds(c, call.env, known).contains(true))).flatMap(_.names).distinct

  /** the webhooks for what became of an asked call: approved, refused, timed out */
  def notices(policy: Compiled, call: Call, d: Decision, outcome: NoticeOn): List[String] =
    notices(policy, call, outcome, d.known)

  private def decided(policy: Compiled, call: Call, rules: List[TRule], counts: List[TCount], known: Known)
    : Decision =
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
            val v = policy.checked.default
            val counted = if v == Verdict.Deny then Nil
              else counts.filter(c => c.when.forall(w => Eval.holds(w, env, known).contains(true)))
            val changes = counted.flatMap(_.updates).map(u => change(u, env, known))
            val reasons = (if v == Verdict.Deny then why.ifEmpty(List("no rule allows it"))
              else s"by the policy's default: ${v.word}" :: why)
            if changes.exists(_.isEmpty) then
              Decision(Verdict.Deny, Nil, None, List(s"an update's value is unknown, so the call is denied"), Nil)
            else Decision(v, Nil, None, reasons, changes.flatten, byDefault = true)

  extension (l: List[String]) private def ifEmpty(d: => List[String]): List[String] = if l.isEmpty then d else l

  private def change(u: TUpdate, env: Map[String, Value], known: Known): Option[StateChange] =
    for v <- Eval.value(u.value, env, known); r <- Eval.ref(u.state, u.key, env, known) yield StateChange(r, u.change,
      v)

  /** decided, and its changes made if allowed: what a guard does for a call */
  def enforce[R[_]](policy: Compiled, call: Call)(using In[Facts, R], In[States, R]): Decision ! R =
    apply[R](policy, call).flatMap(d => (if d.verdict == Verdict.Allow then States.update[R](d.updates) else unit[R])
      .as(d))

  /** an asked call approved by a human: its changes made */
  def approve[R[_]](d: Decision)(using In[States, R]): Unit ! R =
    if d.verdict == Verdict.Ask then States.update[R](d.updates) else unit[R]
