package okay.policy

import okay.proof.{Certificate, Kernel}
import okay.scala3.*

/** decisions: each verdict a theorem of the policy's kernel, its hypotheses the facts it used; the default deny
 * explained; state changed by allowed calls */
class DecideSuite extends munit.FunSuite:
  val policy = Compiled(Examples.payments).fold(ps => fail(ps.mkString("\n")), identity)
  val ann = Value.E("User", "ann")
  val acc1 = Value.E("Account", "acc1")
  def pay(amount: String, currency: String = "usd", account: Value = acc1, by: Value = ann) =
    Call("stripe.create_payment", by, Map("account" -> account, "amount" -> Value.D(BigDecimal(amount)),
      "currency" -> Value.T(currency)))
  val known = Map(
    FactRef("owns", List(ann, acc1)) -> Answer.Holds(true),
    FactRef("balance", List(acc1)) -> Answer.Is(Value.D(BigDecimal("900.00"))))

  type Row[X] = (Store + Facts)[X]
  def decide(call: Call, facts: Map[FactRef, Answer] = known, store: Store.Memory = Store.Memory(policy.checked)) =
    run(store.handler(Facts.known(facts)(Decide.enforce[Row](policy, call))))

  test("the spec's tests pass") {
    val outcomes = Tests.run(policy)
    assert(outcomes.forall(_.passed), outcomes.mkString("\n"))
    assertEquals(outcomes.size, 3)
  }

  test("ALLOW: a theorem of the policy's kernel, of exactly this call; its hypotheses the facts it rests on") {
    val d = decide(pay("50.00"))
    assertEquals(d.verdict, Verdict.Allow)
    val t = d.theorem.get
    assert(policy.kernel.owns(t))
    assertEquals(t.concl.toString.take(40), t.concl.toString.take(40))
    assert(t.concl.toString.startsWith("allow:stripe.create_payment(ann, acc1, 50"), t.concl.toString)
    val hyps = t.hyps.map(_.toString)
    assert(hyps.exists(_.startsWith("owns(ann, acc1)")), hyps.toString)
    assert(hyps.exists(_.contains("balance(acc1)")), hyps.toString)
    assert(hyps.exists(_.contains("spent(ann)")), hyps.toString)
  }

  test("the certificate: checked again by a fresh kernel of the same theory; a changed amount refused") {
    val cert = decide(pay("50.00")).certificate.get
    assert(Certificate.check(cert, Kernel(policy.theorize.theory)).isRight)
    assert(Certificate.check(cert.replace("\"50\"", "\"5000\""), Kernel(policy.theorize.theory)).isLeft)
  }

  test("ASK and DENY are theorems too; the default deny says why each rule did not apply") {
    val asked = decide(pay("800.00"))
    assertEquals(asked.verdict, Verdict.Ask)
    assertEquals(asked.reasons, List("a large payment"))
    assert(asked.theorem.exists(_.concl.toString.startsWith("ask:stripe.create_payment")))
    assertEquals(decide(pay("50.00", currency = "gbp")).verdict, Verdict.Ask) // the ask rule does not look at it
    val denied = decide(pay("50.00", currency = "gbp"), known.updated(FactRef("owns", List(ann, acc1)),
      Answer.Holds(false)))
    assertEquals(denied.verdict, Verdict.Deny)
    assertEquals(denied.theorem, None)
    assert(denied.reasons.exists(_.contains("currency (\"gbp\") in [\"usd\", \"eur\"] is false")), denied.reasons.toString)
    val huge = decide(pay("6000.00"))
    assertEquals(huge.verdict, Verdict.Deny)
    assert(huge.reasons.exists(_.contains("amount (6000.00) <= 5000.00 is false")), huge.reasons.toString)
  }

  test("an unknown fact: the rule does not apply — a missing fact never allows") {
    val d = decide(pay("50.00"), known - FactRef("owns", List(ann, acc1)))
    assertEquals(d.verdict, Verdict.Deny)
    assert(d.reasons.exists(_.contains("unknown: owns(ann, acc1)")), d.reasons.toString)
  }

  test("STATE: spent and counted by allowed calls; a budget runs out; asked calls change nothing until approved") {
    val store = Store.Memory(policy.checked)
    for _ <- 1 to 4 do assertEquals(decide(pay("500.00"), store = store).verdict, Verdict.Allow)
    assertEquals(store.get(FactRef("spent", List(ann))), Value.D(BigDecimal("2000.00")))
    assertEquals(store.get(FactRef("calls", List(ann))), Value.I(4))
    val over = decide(pay("1.00"), store = store) // 2000 + 1 > 2000: no allow, an ask (1 <= 5000)
    assertEquals(over.verdict, Verdict.Ask)
    assertEquals(store.get(FactRef("spent", List(ann))), Value.D(BigDecimal("2000.00")))
  }

  test("a window: the day's spending starts again the next day") {
    var now = 0L
    val store = Store.Memory(policy.checked, () => now)
    for _ <- 1 to 4 do decide(pay("500.00"), store = store)
    assertEquals(decide(pay("1.00"), store = store).verdict, Verdict.Ask)
    now = 86_400_000L
    assertEquals(decide(pay("1.00"), store = store).verdict, Verdict.Allow)
  }

  test("DENY over everything: too many calls in a minute") {
    val store = Store.Memory(policy.checked, () => 0L)
    store.set(FactRef("calls", List(ann)), Value.I(60))
    val d = decide(pay("1.00"), store = store)
    assertEquals(d.verdict, Verdict.Deny)
    assertEquals(d.reasons, List("too many calls"))
    assert(d.theorem.exists(_.concl.toString.startsWith("deny:stripe.create_payment")))
  }

  test("negations: not over and/or taken apart; a relation known false a hypothesis") {
    val p = Compiled("""policy n
      |type User
      |fact banned(user: User)
      |fact level(user: User): Int
      |call op(n: Int)
      |allow op when not (banned(caller) or level(caller) < 3) and not (n > 10)
      |""".stripMargin).fold(ps => fail(ps.mkString), identity)
    val facts = Map(FactRef("banned", List(ann)) -> Answer.Holds(false), FactRef("level", List(ann)) -> Answer.Is(Value.I(5)))
    val d = run(Store.Memory(p.checked).handler(Facts.known(facts)(Decide[Row](p, Call("op", ann, Map("n" -> Value.I(4)))))))
    assertEquals(d.verdict, Verdict.Allow)
    assert(d.facts.map(_.toString).exists(_.startsWith("¬banned(ann)")), d.facts.toString)
    val low = facts.updated(FactRef("level", List(ann)), Answer.Is(Value.I(2)))
    assertEquals(run(Store.Memory(p.checked).handler(Facts.known(low)(
      Decide[Row](p, Call("op", ann, Map("n" -> Value.I(4))))))).verdict, Verdict.Deny)
  }

  test("a wrong evaluator cannot make a wrong decision: a proof of a rule that does not hold is refused") {
    val allow = policy.checked.rulesOf("stripe.create_payment").head
    val k = Known(known, Map(FactRef("spent", List(ann)) -> Value.D(BigDecimal("0.00"))))
    val tooMuch = pay("600.00") // over the limit of one: the allow rule does not hold
    val got = run(okay.proof.Infer.by(policy.kernel)(policy.prove.decision[okay.proof.Infer](allow, tooMuch, k)))
    assert(got.left.exists(_.contains("600 ≤ 500")), got.toString)
    val ok = run(okay.proof.Infer.by(policy.kernel)(policy.prove.decision[okay.proof.Infer](allow, pay("60.00"), k)))
    assert(ok.isRight, ok.toString)
  }
