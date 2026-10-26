package okay.policy

import okay.scala3.*

/** layers: deny over ask over allow; a layer with no rule applying says nothing; the bottom's default last; reads */
class LayersSuite extends munit.FunSuite:
  def compile(t: String) = Compiled(t).fold(ps => fail(ps.mkString("\n")), identity)
  val org = compile("""policy org
    |type User
    |call pay(amount: Dec)
    |call list() reads
    |deny pay when amount > 10000 because "the organization's limit"
    |""".stripMargin)
  val team = compile("""policy team
    |type User
    |call pay(amount: Dec)
    |call list() reads
    |default allow
    |ask pay when amount > 500 because "the team asks over 500"
    |""".stripMargin)
  val ann = Value.E("User", "ann")
  type Row[X] = (States + Facts)[X]
  def decide(p: Compiled, c: Call) = run(States.Memory(p.checked).handler(Facts.known(Map.empty)(Decide[Row](p, c))))
  def pay(n: Int) = Call.flat("pay", ann, Map("amount" -> Value.D(BigDecimal(n))))
  def layered(c: Call) = Layers.combine(List(decide(org, c), decide(team, c)))._1

  test("the org's deny wins; the team's ask; neither speaks: the bottom's default (allow), not the org's (deny)") {
    assertEquals(layered(pay(20000)), Verdict.Deny)
    assertEquals(layered(pay(800)), Verdict.Ask)
    assertEquals(layered(pay(100)), Verdict.Allow)
    assertEquals(Layers.said(decide(org, pay(100))), Said.Nothing)
  }

  test("a call declared to read: `reads`, written and read again") {
    assert(org.checked.calls("list").reads && !org.checked.calls("pay").reads)
    assert(Printer(org.checked.policy).contains("call list() reads"))
  }

  test("an ASK is stronger than an ALLOW: `allow github.*` with `ask github.create_pull_request` asks") {
    val p = compile("""policy gh
      |type User
      |call github.create_pull_request(title: Text)
      |call github.list_issues()
      |allow github.*
      |ask github.create_pull_request because "a pull request is a person's"
      |""".stripMargin)
    val pr = decide(p, Call.flat("github.create_pull_request", ann, Map("title" -> Value.T("Fix"))))
    assertEquals((pr.verdict, pr.reasons), (Verdict.Ask, List("a pull request is a person's")))
    assert(pr.theorem.isDefined)
    assertEquals(decide(p, Call.flat("github.list_issues", ann, Map.empty)).verdict, Verdict.Allow)
    assertEquals(decide(p, Call.flat("github.delete_repo", ann, Map.empty)).verdict, Verdict.Allow) // undeclared, open
  }

