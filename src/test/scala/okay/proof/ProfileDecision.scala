package okay.proof

import Bank.*

/** the decision, in a loop, for a profiler */
object ProfileDecision:
  def main(args: Array[String]): Unit =
    val k = Kernel(policy)
    val goal = transfer(ann, acc1, "500.00")
    val until = System.nanoTime() + args.headOption.map(_.toLong).getOrElse(15L) * 1_000_000_000L
    var n = 0L
    while System.nanoTime() < until do { Auto.prove(k, facts, goal); n += 1 }
    println(s"decisions: $n")
