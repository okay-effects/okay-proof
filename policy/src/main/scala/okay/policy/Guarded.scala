package okay.policy

import okay.scala3.*
import okay.scala3.std.*

/** an operation of an effect, described as the policy sees an action: its name (`service.operation`) and arguments */
final case class Described(operation: String, args: Map[String, Data])

/** how a service's effect `E` is seen by a policy: each operation an action — the service guarded in its own process,
 * no proxy (specs/policy.md, "In process") */
trait Describe[E[_]]:
  def apply[X](op: E[X]): Described

/** a person asked about an action the policy asks for: approved or not — the handler is the asking (a page, a chat, a
 * queue of approvals, a test's answer) */
enum Approval[X]:
  case Ask(action: Described, reasons: List[String]) extends Approval[Boolean]

/**
 * A SERVICE GUARDED IN ITS OWN PROCESS: each operation of its effect `E` described, decided by the policy before it
 * runs — allowed, it runs (and the policy's changes are made); denied, it does not, the program failing with the
 * reasons (`Fail % String`); asked, a person is (`Approval`), and it runs if approved. Every decision is the policy's
 * theorem; `seen` gets each one, for a journal. The program is the service's own — the guard an interceptor around it.
 */
object Guarded:
  def apply[E[_], R[_], A](policy: Compiled, caller: Value, p: A ! R,
                           seen: (Described, Decision) => Unit = (_, _) => ())(
    using describe: Describe[E], e: In[E, R], f: In[Facts, R], s: In[States, R], fail: In[Fail % String, R],
    ask: In[Approval, R]): A ! R =
    around[E, R, A](p)([X] => (op: E[X], proceed: X ! R) =>
      val d = describe(op)
      val call = Call(d.operation, caller, d.args)
      Decide.enforce[R](policy, call).flatMap { decision =>
        seen(d, decision)
        decision.verdict match
          case Verdict.Allow => proceed
          case Verdict.Deny => Fail.raise[String, R](decision.reasons.mkString("; "))
          case Verdict.Ask => perform[Approval](Approval.Ask(d, decision.reasons)).flatMap { yes =>
            if yes then Decide.approve[R](decision).andThen(proceed)
            else Fail.raise[String, R](s"refused by a person: ${decision.reasons.mkString("; ")}")
          }
      })

  /** a person's answers, as a function: a test's, a rule of thumb's */
  def approving[R[_], Rest[_], A](answer: Described => Boolean)(p: A ! R)(using Split[Approval, R, Rest]): A ! Rest =
    handle(p, Handler.tail[Approval, Rest, A, A](pure)([X] => (op: Approval[X]) => op match
      case Approval.Ask(action, _) => answer(action)))
