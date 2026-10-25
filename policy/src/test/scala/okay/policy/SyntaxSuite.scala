package okay.policy

/** the text to a policy and back; problems with their places */
class SyntaxSuite extends munit.FunSuite:
  def parsed(text: String): Policy = Parser.parse(text).fold(p => fail(p.toString), identity)

  /** a policy with its positions zeroed: to compare what was written, not where */
  def unplaced(p: Policy): String = Printer(p)

  test("the spec's example: every declaration read") {
    val p = parsed(Examples.payments)
    assertEquals(p.name, "payments")
    assertEquals(p.types.map(_.name), List("User", "Account"))
    assertEquals(p.facts.map(_.name), List("owns", "role", "balance"))
    assertEquals(p.facts.map(_.source), List(None, None, Some("stripe")))
    assertEquals(p.states.map(s => (s.name, s.window)), List(("spent", Some(Window.Day)), ("calls", Some(Window.Minute))))
    assertEquals(p.calls.map(_.tool), List("stripe.create_payment", "stripe.refund"))
    assertEquals(p.rules.map(r => (r.verdict, r.target)), List(
      (Verdict.Allow, Target.Tool("stripe.create_payment")), (Verdict.Ask, Target.Tool("stripe.create_payment")),
      (Verdict.Deny, Target.Any), (Verdict.Allow, Target.Tool("stripe.refund"))))
    assertEquals(p.counts.map(_.target), List(Target.Any))
  }

  test("the tests, in their own file") {
    val f = Parser.parseTests(Examples.paymentsTests).fold(p => fail(p.toString), identity)
    assertEquals(f.policy, "payments")
    assertEquals(f.tests.map(_.expect), List(Verdict.Allow, Verdict.Ask, Verdict.Deny))
    assertEquals(f.tests(1).because, Some("a large payment"))
    val Given.Holds(name, _, truth, _) = f.tests(2).givens.head: @unchecked
    assertEquals((name, truth), ("owns", false))
    val once = Printer(f)
    assertEquals(Printer(Parser.parseTests(once).toOption.get), once)
    assertEquals(Parser.parse("policy p\ntest \"t\"").left.map(_.message),
      Left("a test goes in the policy's file of tests (`tests for <policy>`), not in it"))
  }

  test("printed and parsed again: the same text") {
    val once = Printer(parsed(Examples.payments))
    val twice = Printer(parsed(once))
    assertEquals(twice, once)
    assert(once.contains("spent(caller) + amount <= 2000.00"), once)
    assert(once.contains("currency in [\"usd\", \"eur\"]"), once)
  }

  test("precedence: and over or, not over and, parentheses kept where needed; * over +") {
    def rule(c: String) = parsed(s"policy p\nallow * when $c").rules.head.when.get
    assertEquals(Printer.cond(rule("a(x) or b(x) and c(x)")), "a(x) or b(x) and c(x)")
    assertEquals(Printer.cond(rule("(a(x) or b(x)) and c(x)")), "(a(x) or b(x)) and c(x)")
    assertEquals(Printer.cond(rule("not (a(x) and b(x))")), "not (a(x) and b(x))")
    assertEquals(Printer.cond(rule("(x + y) * 2 <= 10")), "(x + y) * 2 <= 10")
    assertEquals(Printer.cond(rule("x + y * 2 <= 10")), "x + y * 2 <= 10")
    assertEquals(Printer.cond(rule("(x + 1) <= 10")), "x + 1 <= 10")
    assertEquals(Printer.cond(rule("x - (y - 1) >= -2.50")), "x - (y - 1) >= -2.50")
  }

  test("problems, with their places") {
    def problem(text: String) = Parser.parse(text).left.toOption.getOrElse(fail(s"parsed: $text"))
    assertEquals(problem("policy p\ntype user").toString, "2:6: a type's name starts with a capital: user")
    assertEquals(problem("policy p\nallow * when amount <").message, "expected a value: a number, a text, a name, a fact, found the end")
    assertEquals(problem("policy p\nallow * when x + 1").message,
      "expected a comparison (=, !=, <, <=, >, >=), 'in', or a text test (starts, ends, contains), found the end")
    assertEquals(problem("policy p\nfact f(x User)").pos, Pos(2, 10))
    assertEquals(problem("policy p\nallow * because \"no end\n").message, "a text not closed on its line")
    assertEquals(problem("policy p\nallow * because \"no end").message, "a text not closed")
    assertEquals(problem("policy p\nallow * when x # 1").message, "an unexpected character '#'")
    assertEquals(problem("policy p\nwhen").message,
      "expected a declaration: type, fact, state, call, allow, ask, deny or count, found 'when'")
  }

  test("a tool no name can be, in quotes: written and read again") {
    val text = "policy p\ntype User\ncall \"list-files\"(path: Text)\nallow \"list-files\" when path starts \"/ws/\"\n"
    val p = parsed(text)
    assertEquals(p.calls.map(_.tool), List("list-files"))
    assertEquals(p.rules.head.target, Target.Tool("list-files"))
    assertEquals(Printer(parsed(Printer(p))), Printer(p))
    assert(Printer(p).contains("allow \"list-files\""))
    val tests = "tests for p\ntest \"t\"\n  given x(a)\n  when ann calls \"list-files\"(path: \"/ws/a\")\n  expect allow\n"
    assertEquals(Parser.parseTests(tests).map(_.tests.head.tool), Right("list-files"))
  }

  test("a test with no given: a call alone") {
    val f = Parser.parseTests("tests for p\ntest \"t\"\n  when ann calls tool(x: 1)\n  expect deny\n").toOption.get
    assertEquals(f.tests.head.givens, Nil)
    assertEquals(Printer(Parser.parseTests(Printer(f)).toOption.get), Printer(f))
  }

