package okay.policy

/** the checker: the spec's example checked; each problem the spec lists found, at its place */
class TypesSuite extends munit.FunSuite:
  val head =
    """policy p
      |type User
      |type Account
      |fact owns(user: User, account: Account)
      |fact role(user: User): Text
      |fact balance(account: Account): Dec
      |state spent(user: User): Dec per day = 0
      |call pay(account: Account, amount: Dec, currency: Text)
      |call refund(payment: Text)
      |""".stripMargin

  def problems(body: String): List[String] = Types(head + body) match
    case Left(ps) => ps.map(_.message)
    case Right(_) => Nil

  def ok(body: String): Checked = Types(head + body).fold(ps => fail(ps.mkString("\n")), identity)

  test("the spec's example: checked, its rules on their tools, its tests read") {
    val c = Types(Examples.payments).fold(ps => fail(ps.mkString("\n")), identity)
    assertEquals(c.rulesOf("stripe.create_payment").map(_.verdict), List(Verdict.Allow, Verdict.Ask, Verdict.Deny))
    assertEquals(c.rulesOf("stripe.refund").map(_.verdict), List(Verdict.Deny, Verdict.Allow))
    assertEquals(c.countsOf("stripe.refund").size, 1)
    assertEquals(c.states("spent").init, Value.D(BigDecimal("0.00")))
    val t = Types.tests(c, Examples.paymentsTests).fold(ps => fail(ps.mkString("\n")), identity).head
    assertEquals(t.caller, Value.E("User", "ann"))
    assertEquals(t.args("amount"), Data.Leaf(Value.D(BigDecimal("50.00"))))
    assertEquals(t.givens.head, TGiven("owns", List(Value.E("User", "ann"), Value.E("Account", "acc1")), Left(true)))
  }

  test("an Int literal where a Dec is wanted; dec(...) of an Int; entities by their names") {
    val c = ok("allow pay when amount <= 500 and amount * 2 <= balance(account) + 1 and caller = boss")
    val TCond.And(TCond.And(TCond.Compare(_, _, five), _), TCond.Compare(_, _,
      boss)) = c.rules.head.when.get: @unchecked
    assertEquals(five, TExpr.Lit(Value.D(BigDecimal(500))))
    assertEquals(boss, TExpr.Lit(Value.E("User", "boss")))
  }

  test("unknown names: facts, states, variables, tools, types") {
    assertEquals(problems("allow pay when owes(caller, account)"), List("an unknown fact owes"))
    assertEquals(problems("allow pay when limit(caller) > 1"), List("an unknown fact or state limit"))
    assertEquals(problems("allow pay when price > 1"), List("an unknown name price"))
    assertEquals(problems("allow send when amount > 1"), List("an unknown tool send: declare it with `call`"))
    assertEquals(problems("fact f(x: Money)"), List("an unknown type Money"))
  }

  test("an argument of only some of the rule's tools") {
    assertEquals(problems("allow * when amount < 10"),
      List("`amount` is not an argument of every tool this rule decides (*): only of pay"))
    assertEquals(problems("allow refund when amount < 10"), List("an unknown name amount"))
  }

  test("sorts: mixed, ordered, nonlinear, Int and Dec") {
    assertEquals(problems("allow pay when amount < currency"), List("Dec < Text: different sorts"))
    assertEquals(problems("allow pay when currency < \"usd\""), List("< on Text: an order of numbers only"))
    assertEquals(problems("allow pay when amount * balance(account) < 10"),
      List("a product by a literal only (the conditions stay linear): amount * balance(account)"))
    assertEquals(problems("allow pay when amount + currency < 10"), List("+ of Dec and Text: numbers only"))
    assertEquals(problems("allow pay when caller != boss"),
      List("!= between Users: not yet (two names are not known to be two things)"))
  }

  test("text tests: texts only") {
    assertEquals(problems("allow refund when payment starts \"pi_\" and not (payment contains \"test\")"), Nil)
    assertEquals(problems("allow pay when amount starts \"1\""), List("Dec starts Text: texts only"))
  }

  test("facts: arity, sorts, relation or value, nested") {
    assertEquals(problems("allow pay when owns(caller)"), List("owns takes 2 arguments, given 1"))
    assertEquals(problems("allow pay when owns(account, caller)"), List("expected User, found Account",
      "expected Account, found User"))
    assertEquals(problems("allow pay when owns(caller, account) = 1"),
      List("owns is a relation: a condition, not a value"))
    assertEquals(problems("allow pay when role(caller)"),
      List("role is a function fact: compare its value (`role(...) = ...`)"))
    assertEquals(problems("allow pay when balance(account) > spent(caller) and owns(caller, account)"), Nil)
    assertEquals(problems("fact boss(user: User): User\nallow pay when role(boss(caller)) = \"x\""),
      List("a fact's argument is a name or a literal, not a fact: boss(caller)"))
  }

  test("updates: only states, of their sorts") {
    assertEquals(problems("allow pay when amount < 1 then balance(account) -= amount"),
      List("balance is a fact: only a state changes"))
    assertEquals(problems("allow pay when amount < 1 then spent(caller) += currency"), List("expected Dec, found Text"))
    assertEquals(problems("allow pay"), Nil) // allows every call of pay
    assertEquals(problems("count pay then balance(account) += 1"), List("balance is a fact: only a state changes"))
    assertEquals(problems("count * then spent(caller) += amount"),
      List("`amount` is not an argument of every tool this rule decides (*): only of pay"))
  }

  test("tests: unknown tools, arguments, facts; missing arguments") {
    def t(s: String) = Types.tests(ok(""), s"tests for p\ntest \"t\"\n  $s").left.toOption.toList.flatten.map(_.message)
    assertEquals(t("given owns(ann, acc1) when ann calls send(amount: 1) expect allow"), List("an unknown tool send"))
    assertEquals(
      t("given owns(ann, acc1) when ann calls pay(account: acc1, amount: 1, currency: \"usd\", x: 1) expect allow"),
      List("pay has no argument x"))
    assertEquals(t("given owns(ann, acc1) when ann calls pay(account: acc1) expect allow"),
      List("the call's argument amount is missing", "the call's argument currency is missing"))
    assertEquals(t("given owes(ann, acc1) when ann calls refund(payment: \"p\") expect allow"),
      List("an unknown relation fact owes"))
    assertEquals(t("given spent(ann) = \"x\" when ann calls refund(payment: \"p\") expect allow"),
      List("expected Dec, found Text"))
  }

  test("a file of tests for another policy") {
    assertEquals(Types.tests(ok(""), "tests for q").left.map(_.map(_.message)), Left(List("tests for q, not for p")))
  }

  test("problems sorted by place, several at once") {
    val ps = Types(head + "allow pay when price > 1\nallow refund when cost > 2").left.toOption.get
    assertEquals(ps.map(_.pos.line), List(10, 11))
  }
