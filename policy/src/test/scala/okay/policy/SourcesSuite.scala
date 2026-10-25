package okay.policy

import okay.scala3.*
import okay.scala3.std.*

import scala.concurrent.{ExecutionContext, Future}

/** external facts: each asked of its source, all sources at once; late, failing, lying sources answer nothing */
class SourcesSuite extends munit.FunSuite:
  given ExecutionContext = Async.defaultContext

  val policy = Compiled("""policy shop
    |type User
    |type Account
    |fact verified(user: User)
    |fact balance(account: Account): Dec from stripe
    |fact risk(user: User): Int from fraud
    |call pay(account: Account, amount: Dec)
    |allow pay when verified(caller) and amount <= balance(account) and risk(caller) < 50
    |""".stripMargin).fold(ps => fail(ps.mkString("\n")), identity)

  val ann = Value.E("User", "ann")
  val acc = Value.E("Account", "acc1")
  val call = Call.flat("pay", ann, Map("account" -> acc, "amount" -> Value.D(BigDecimal("40.00"))))
  val session = Source.of {
    case FactRef("verified", List(`ann`)) => Some(Answer.Holds(true))
    case _ => None
  }
  def after[A](ms: Long, a: => A): Map[FactRef, Answer] ! Async = Async.sleep[Async](ms).map(_ => a.asInstanceOf[Map[FactRef, Answer]])
  def stripe(ms: Long) = new Source:
    def ask(refs: List[FactRef]) = after(ms, refs.map(_ -> Answer.Is(Value.D(BigDecimal("100.00")))).toMap)
  def fraud(ms: Long, risk: Int = 10) = new Source:
    def ask(refs: List[FactRef]) = after(ms, refs.map(_ -> Answer.Is(Value.I(risk))).toMap)

  type Row[X] = (Async + States + Facts)[X]
  def decide(sources: Map[String, Source], timeout: Long = 500): Future[Decision] =
    val store = States.Memory(policy.checked)
    Async.toFuture(store.handler(Facts.from(policy.checked, sources, session, timeout)(Decide[Row](policy, call))))

  test("each fact from its source, the sources asked in parallel; the theorem rests on what they said") {
    val t0 = System.nanoTime()
    decide(Map("stripe" -> stripe(150), "fraud" -> fraud(150))).map { d =>
      assertEquals(d.verdict, Verdict.Allow)
      val ms = (System.nanoTime() - t0) / 1000000
      assert(ms < 290, s"$ms ms: one after the other")
      val facts = d.facts.map(_.toString)
      assert(facts.exists(_.startsWith("balance(acc1)")) && facts.exists(_.startsWith("risk(ann)")), facts.toString)
    }
  }

  test("a source missing, late, or failing: its facts unknown — denied, never allowed") {
    assertEquals(Facts.missing(policy.checked, Set("stripe")), Set("fraud"))
    val failing = new Source:
      def ask(refs: List[FactRef]) = Async.fromFuture(Future.failed(IllegalStateException("down")))
    for
      missing <- decide(Map("stripe" -> stripe(1)))
      late <- decide(Map("stripe" -> stripe(1), "fraud" -> fraud(400)), timeout = 100)
      failed <- decide(Map("stripe" -> stripe(1), "fraud" -> failing))
    yield
      for d <- List(missing, late, failed) do
        assertEquals(d.verdict, Verdict.Deny)
        assert(d.reasons.exists(r => r.contains("risk(ann)") && r.contains("unknown")), d.reasons.toString)
  }

  test("a source answers only its own facts, of their sort: a lie about another's fact, or a wrong sort, dropped") {
    val liar = new Source:
      def ask(refs: List[FactRef]) = pure(Map(
        FactRef("verified", List(ann)) -> Answer.Holds(true), // not stripe's fact
        FactRef("balance", List(acc)) -> Answer.Is(Value.T("lots")))) // not a Dec
    val noSession = Map[String, Source]("stripe" -> liar, "fraud" -> fraud(1))
    val store = States.Memory(policy.checked)
    Async.toFuture(store.handler(Facts.from(policy.checked, noSession)(Decide[Row](policy, call)))).map { d =>
      assertEquals(d.verdict, Verdict.Deny)
      assert(d.reasons.exists(_.contains("unknown")), d.reasons.toString)
    }
  }
