package okay.proof

import okay.effects.*
import okay.effects.std.*
import Bank.*
import Formula.*

/** a transfer decision as a theorem: proved from the request's facts and the bank's policy, its certificate checked
 * again elsewhere, and an operation that runs only with it */
class PolicySuite extends munit.FunSuite:
  val k = Kernel(policy)
  def proved(goal: Formula, fs: List[Formula] = facts): Option[Thm] =
    Auto.prove(k, fs, goal).fold(e => fail(s"a step refused: $e"), identity)

  test("within the limits: proved — its hypotheses exactly the facts it rests on") {
    val goal = transfer(ann, acc1, "500.00")
    val t = proved(goal).getOrElse(fail("no proof"))
    assertEquals(t.concl, goal)
    assert(t.hyps.subsetOf(facts.toSet), t.hyps.toString)
    assert(k.owns(t))
  }

  test("over a limit, an account the role may not use, a user with no role: no proof") {
    assertEquals(proved(transfer(ann, acc1, "1000.01")), None) // over the limit of one transfer
    assertEquals(proved(transfer(ann, acc1, "1250.00")), None) // and over the daily limit with 300 spent
    assertEquals(proved(transfer(ann, acc2, "10.00")), None)
    assertEquals(proved(transfer(bob, acc1, "10.00")), None)
  }

  test("the daily limit: what was spent counts") {
    assert(proved(transfer(ann, acc1, "1000.00")).isDefined) // 300 + 1000 ≤ 1500
    val later = facts.map {
      case Eq(s, _) if s == spent(ann) => Eq(spent(ann), dec("600.00"))
      case f => f
    }
    assertEquals(proved(transfer(ann, acc1, "1000.00"), later), None) // 600 + 1000 > 1500
  }

  test("facts as BOUNDS, not values: what was spent known only to be at most 300 — linear arithmetic decides") {
    val bounded = facts.map {
      case Eq(s, v) if s == spent(ann) => Le(spent(ann), v)
      case f => f
    }
    val t = proved(transfer(ann, acc1, "900.00"), bounded).getOrElse(fail("no proof")) // spent + 900 ≤ 300 + 900 ≤ 1500
    assert(t.hyps.contains(Le(spent(ann), dec("300.00"))), t.hyps.toString)
    assertEquals(proved(transfer(ann, acc1, "1250.00"), bounded), None) // over the limit of one transfer
    val looser = bounded.map(f => if f == Le(spent(ann), dec("300.00")) then Le(spent(ann), dec("600.00")) else f)
    assertEquals(proved(transfer(ann, acc1, "1000.00"), looser), None) // spent may be 600: 1600 > 1500
    assert(proved(transfer(ann, acc1, "900.00"), looser).isDefined) // 600 + 900 ≤ 1500
    val unknown = bounded.filterNot(_ == Le(spent(ann), dec("300.00")))
    assertEquals(proved(transfer(ann, acc1, "1.00"), unknown), None) // nothing known of what was spent
  }

  test("the CERTIFICATE: checked again by a fresh kernel of the policy; a changed one refused") {
    val goal = transfer(ann, acc1, "500.00")
    val t = proved(goal).get
    val cert = Certificate.of(t)
    assertEquals(Certificate.check(cert, Kernel(policy)).map(_.concl), Right(goal))
    assert(cert.contains("\"500\""), "the amount is in the certificate, canonically")
    assert(Certificate.check(cert.replace("\"500\"", "\"5000\""), Kernel(policy)).isLeft)
    assert(Certificate.check(cert, Kernel(Theory("bank"))).isLeft, "checked under a theory without the policy")
  }

  /** an operation of one's own, guarded: a transfer runs only with a theorem, of the policy's kernel, that it is
   * allowed — from the facts the guard knows */
  enum Pay[X]:
    case Transfer(user: Term, account: Term, amount: String, proof: Thm) extends Pay[String]

  def guard[R[_], A](known: Set[Formula])(p: A ! R)(using In[Pay, R], In[Writer % String, R]): A ! R =
    around[Pay, R, A](p)(new Around[Pay, R]:
      def apply[X](op: Pay[X], proceed: X ! R): X ! R = op match
        case Pay.Transfer(u, a, amount, t) =>
          val ok = k.owns(t) && t.concl == transfer(u, a, amount) && t.hyps.subsetOf(known)
          if ok then proceed else tell[String, R](s"refused: no proof for $u $a $amount").map(_ => "refused"))

  test("a GATE: a guarded operation runs with its proof, and without one is refused") {
    type Row[X] = (Writer % String + Pay)[X]
    def pay(amount: String, t: Thm): String ! Row = perform[Pay](Pay.Transfer(ann, acc1, amount, t))
    val good = proved(transfer(ann, acc1, "500.00")).get
    val program = for
      x <- pay("500.00", good)
      y <- pay("900.00", good) // the proof is of 500.00
    yield List(x, y)
    val ran = run(writer[String](handle(guard[Row, List[String]](facts.toSet)(program),
      new TailHandler[Pay, Writer % String, List[String], List[String]]:
        def ret(a: List[String]) = pure(a)
        def answer[X](op: Pay[X]): X = op match
          case Pay.Transfer(_, _, amount, _) => s"sent $amount")))
    assertEquals(ran, (List("refused: no proof for ann() acc1() 900.00"), List("sent 500.00", "refused")))
  }
