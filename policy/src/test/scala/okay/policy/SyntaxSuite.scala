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
    assertEquals(p.tests.map(_.expect), List(Verdict.Allow, Verdict.Ask, Verdict.Deny))
    assertEquals(p.tests(1).because, Some("a large payment"))
    assertEquals(p.tests(2).givens.head, Given.Holds("not owns".drop(4), p.tests(2).givens.head match
      case Given.Holds(_, as, _, _) => as
      case _ => Nil, false, p.tests(2).givens.head match
      case g: Given.Holds => g.pos
      case _ => Pos(0, 0)))
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
    assertEquals(problem("policy p\nallow * when x").message,
      "expected a comparison (=, !=, <, <=, >, >=), 'in', or a text test (starts, ends, contains), found the end")
    assertEquals(problem("policy p\nfact f(x User)").pos, Pos(2, 10))
    assertEquals(problem("policy p\nallow * because \"no end\n").message, "a text not closed on its line")
    assertEquals(problem("policy p\nallow * because \"no end").message, "a text not closed")
    assertEquals(problem("policy p\nallow * when x # 1").message, "an unexpected character '#'")
    assertEquals(problem("policy p\nwhen").message,
      "expected a declaration: type, fact, state, call, allow, ask, deny, count or test, found 'when'")
  }
