package okay.policy

import okay.scala3.*
import okay.scala3.std.*

/** a service on effects, guarded in its own process: its operations decided by the policy before they run */
class GuardedSuite extends munit.FunSuite:
  /** the service's own effect: what it does */
  enum Payments[X]:
    case Charge(customer: String, amount: BigDecimal) extends Payments[String]
    case Refund(charge: String, amount: BigDecimal) extends Payments[Unit]

  given Describe[Payments] with
    def apply[X](op: Payments[X]): Described = op match
      case Payments.Charge(c, n) => Described("payments.charge",
        Map("customer" -> Data.Leaf(Value.T(c)), "amount" -> Data.Leaf(Value.D(n))))
      case Payments.Refund(ch, n) => Described("payments.refund",
        Map("charge" -> Data.Leaf(Value.T(ch)), "amount" -> Data.Leaf(Value.D(n))))

  val policy = Compiled("""policy payments
    |type User
    |state charged(user: User): Dec per day = 0
    |call payments.charge(customer: Text, amount: Dec)
    |call payments.refund(charge: Text, amount: Dec)
    |allow payments.charge when charged(caller) + amount <= 1000
    |ask payments.refund when amount > 100 because "a large refund"
    |allow payments.refund
    |count payments.charge then charged(caller) += amount
    |""".stripMargin).fold(ps => fail(ps.mkString("\n")), identity)

  type R[X] = (Approval + States + Facts + Fail % String + Payments)[X]

  def charge(c: String, n: BigDecimal): String ! R = perform[Payments](Payments.Charge(c, n))
  def refund(ch: String, n: BigDecimal): Unit ! R = perform[Payments](Payments.Refund(ch, n))

  /** the business logic: it knows its effect, nothing of the guard */
  def checkout: String ! R =
    for
      ch <- charge("cus_1", 600)
      _ <- refund(ch, 50)
      ch2 <- charge("cus_1", 300)
      _ <- refund(ch2, 300)
    yield ch2

  /** the service's handler: the real payments, here a list */
  def run(p: String ! R, approve: Described => Boolean) =
    val done = scala.collection.mutable.ListBuffer.empty[String]
    val log = scala.collection.mutable.ListBuffer.empty[String]
    val store = States.Memory(policy.checked, () => 0L)
    val guarded = Guarded[Payments, R, String](policy, Value.E("User", "ann"), p,
      (d, decision) => log += s"${d.operation} ${decision.verdict.word}")
    val out = okay.scala3.run(
      handle(Fail.run(Facts.known(Map.empty)(store.handler(Guarded.approving(approve)(guarded)))),
        Handler.tail[Payments, Pure, Either[String, String], Either[String, String]](pure)(
          [X] => (op: Payments[X]) => op match
            case Payments.Charge(c, n) => done += s"charge $n"; s"ch_${done.size}"
            case Payments.Refund(ch, n) => done += s"refund $n of $ch"; ())))
    (out, done.toList, log.toList, store.get(FactRef("charged", List(Value.E("User", "ann")))))

  test("each operation decided before it runs; a small refund allowed, a large one asked and approved") {
    val (out, done, log, charged) = run(checkout, _ => true)
    assertEquals(out, Right("ch_3"))
    assertEquals(done, List("charge 600", "refund 50 of ch_1", "charge 300", "refund 300 of ch_3"))
    assertEquals(log,
      List("payments.charge allow", "payments.refund allow", "payments.charge allow", "payments.refund ask"))
    assertEquals(charged, Value.D(BigDecimal(900)))
  }

  test("a refusal stops the program before the operation; a denied operation never runs") {
    val (refused, done1, _, _) = run(checkout, _ => false)
    assertEquals(refused, Left("refused by a person: a large refund"))
    assertEquals(done1.last, "charge 300") // the large refund never ran
    val tooMuch: String ! R = charge("cus_1", 1500)
    val (denied, done2, log2, _) = run(tooMuch, _ => true)
    assert(denied.isLeft, denied.toString)
    assertEquals(done2, Nil)
    assertEquals(log2, List("payments.charge deny"))
  }
