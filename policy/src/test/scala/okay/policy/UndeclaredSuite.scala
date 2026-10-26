package okay.policy

import okay.proof.{Certificate, Kernel}
import okay.scala3.*

/** a call of a tool the policy does not declare: decided by the open rules (`*`, `server.*`), then the default */
class UndeclaredSuite extends munit.FunSuite:
  val text = """policy any
    |type User
    |webhook security = "https://sec.example"
    |state calls(user: User): Int per minute = 0
    |call pay(amount: Dec)
    |default allow
    |deny * when tool starts "delete_" because "nothing is deleted"
    |ask stripe.* when not (tool ends "_list") because "stripe writes"
    |deny * when amount > 1000 because "too much"
    |count * then calls(caller) += 1
    |notify security on deny *
    |""".stripMargin
  val policy = Compiled(text).fold(ps => fail(ps.mkString("\n")), identity)
  val ann = Value.E("User", "ann")
  type Row[X] = (States + Facts)[X]
  def decide(tool: String, args: Map[String, Data] = Map.empty, store: States.Memory = States.Memory(policy.checked)) =
    run(store.handler(Facts.known(Map.empty)(Decide.enforce[Row](policy, Call(tool, ann, args)))))

  test("an undeclared tool: the default lets it through; a `*` rule over `tool` denies, as a theorem") {
    val store = States.Memory(policy.checked)
    val list = decide("list_things", store = store)
    assertEquals((list.verdict, list.byDefault), (Verdict.Allow, true))
    assertEquals(store.get(FactRef("calls", List(ann))), Value.I(1)) // counted by `count *`
    val del = decide("delete_customer", Map("customer" -> Data.Leaf(Value.T("x"))))
    assertEquals((del.verdict, del.reasons), (Verdict.Deny, List("nothing is deleted")))
    assertEquals(del.theorem.get.concl.toString, "deny:*(ann, call, \"delete_customer\")")
    assert(Certificate.check(del.certificate.get, Kernel(policy.theorize.theory)).isRight)
    assertEquals(del.webhooks, List("security"))
  }

  test("server.*: the tool is the server's — proved; its arguments unknown, so a rule on one does not apply") {
    val write = decide("stripe.create_refund", Map("amount" -> Data.Leaf(Value.D(BigDecimal(5000)))))
    assertEquals((write.verdict, write.reasons), (Verdict.Ask, List("stripe writes"))) // amount unread: no "too much"
    assertEquals(decide("stripe.charges_list").verdict, Verdict.Allow)
    assertEquals(decide("github.create_issue").verdict, Verdict.Allow) // not stripe's
    assertEquals(decide("pay", Map("amount" -> Data.Leaf(Value.D(BigDecimal(5000))))).verdict, Verdict.Deny) // declared
  }

  test("tests may call an undeclared tool") {
    val tests = """tests for any
      |test "a list"
      |  when ann calls list_things()
      |  expect allow
      |test "a delete"
      |  when ann calls delete_customer(customer: "x")
      |  expect deny "nothing is deleted"
      |""".stripMargin
    val outcomes = Tests.run(policy, tests).fold(ps => fail(ps.mkString("\n")), identity)
    assert(outcomes.forall(_.passed), outcomes.mkString("\n"))
  }
