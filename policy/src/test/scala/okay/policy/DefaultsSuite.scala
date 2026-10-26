package okay.policy

import okay.scala3.*

/** a policy's default verdict, and its webhooks: on the deciding rules, and as notices on outcomes */
class DefaultsSuite extends munit.FunSuite:
  val text = """policy refunds
    |type User
    |webhook security = env "SECURITY_WEBHOOK"
    |webhook ops = "https://ops.example/hook"
    |state refunded(user: User): Dec per day = 0
    |call create_refund(amount: Dec)
    |call delete_customer(id: Text)
    |call get_balance()
    |default allow
    |ask create_refund when amount > 20000 because "a large refund"
    |deny delete_customer because "nothing is deleted" notify security, ops
    |count create_refund then refunded(caller) += amount
    |notify ops on ask create_refund when amount > 50000
    |notify security on refused *
    |notify ops on timed out *
    |""".stripMargin
  val policy = Compiled(text).fold(ps => fail(ps.mkString("\n")), identity)
  val ann = Value.E("User", "ann")
  type Row[X] = (States + Facts)[X]
  def decide(c: Call, store: States.Memory = States.Memory(policy.checked)) =
    run(store.handler(Facts.known(Map.empty)(Decide.enforce[Row](policy, c))))
  def refund(n: Int) = Call.flat("create_refund", ann, Map("amount" -> Value.D(BigDecimal(n))))

  test("written and read again; the checker: one default, webhooks declared") {
    val printed = Printer(Parser.parse(text).toOption.get)
    assertEquals(Printer(Parser.parse(printed).toOption.get), printed)
    assert(printed.contains("webhook security = env \"SECURITY_WEBHOOK\""), printed)
    assert(printed.contains("notify ops on timed out *"), printed)
    assertEquals(policy.checked.default, Verdict.Allow)
    assertEquals(policy.checked.webhooks("ops"), Hook.Url("https://ops.example/hook"))
    def problems(more: String) = Types(text + more).left.toOption.toList.flatten.map(_.message)
    assertEquals(problems("default deny\n"), List("a second default: a policy has one"))
    assertEquals(problems("deny get_balance notify audit\n"),
      List("an unknown webhook audit: declare it with `webhook`"))
    assertEquals(problems("notify audit on deny *\n"), List("an unknown webhook audit: declare it with `webhook`"))
    assertEquals(problems("webhook ops = \"x\"\n"), List("a webhook ops again"))
  }

  test("DEFAULT allow: when no rule applies — so an ask still asks; reported, not proved; counts made") {
    val store = States.Memory(policy.checked)
    val small = decide(refund(100), store)
    assertEquals((small.verdict, small.byDefault, small.theorem), (Verdict.Allow, true, None))
    assert(small.reasons.head == "by the policy's default: allow", small.reasons.toString)
    assert(small.reasons.exists(_.contains("amount (100) > 20000 is false")), small.reasons.toString)
    assertEquals(store.get(FactRef("refunded", List(ann))), Value.D(BigDecimal(100)))
    val big = decide(refund(30000), store)
    assertEquals((big.verdict, big.byDefault), (Verdict.Ask, false))
    assert(big.theorem.isDefined)
    assertEquals(decide(Call.flat("get_balance", ann, Map.empty)).verdict, Verdict.Allow)
  }

  test("no default: deny, as before") {
    val strict = Compiled(text.replace("default allow\n", "")).toOption.get
    val d = run(States.Memory(strict.checked).handler(Facts.known(Map.empty)(Decide[Row](strict, refund(100)))))
    assertEquals((d.verdict, d.byDefault), (Verdict.Deny, true))
  }

  test("WEBHOOKS: the deciding rule's, the notices on its verdict when their condition holds, later outcomes") {
    assertEquals(decide(Call.flat("delete_customer", ann, Map("id" -> Value.T("c1")))).webhooks, List("security",
      "ops"))
    assertEquals(decide(refund(30000)).webhooks, Nil) // an ask, but not over 50000
    val huge = decide(refund(60000))
    assertEquals(huge.webhooks, List("ops"))
    assertEquals(Decide.notices(policy, refund(60000), huge, NoticeOn.Refused), List("security"))
    assertEquals(Decide.notices(policy, refund(60000), huge, NoticeOn.TimedOut), List("ops"))
    assertEquals(Decide.notices(policy, refund(60000), huge, NoticeOn.Approved), Nil)
  }
