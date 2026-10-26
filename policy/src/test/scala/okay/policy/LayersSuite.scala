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
