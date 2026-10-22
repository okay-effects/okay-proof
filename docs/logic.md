# The logic

Many-sorted first-order logic with equality, classical. `Logic.scala` and `Kernel.scala`.

## Sorts, terms, formulas

| | |
|---|---|
| sorts | `Sort.Int` (unbounded integers), `Sort.Dec` (exact decimals), `Sort.Str`, `Sort.Named("Account")` |
| terms | `V(name, sort)` a variable; `I(n)`, `D(x)`, `S(s)` literals; `Ap(fn, args)` an application |
| functions | `Fn(name, argSorts, resultSort)`: the kernel's own (`Fns`, computed) or one's own (known by axioms and facts) |
| predicates | `Pred(name, argSorts)`: one's own |
| formulas | `True`, `False`, `Eq`, `Lt`, `Le`, `P(pred, args)`, `Not`, `And`, `Or`, `Imp`, `All(x, f)`, `Ex(x, f)` |
| in Scala | `a && b`, `a \|\| b`, `!a`, `a implies b`, `Formula.all(x, y)(f)` |

The kernel's functions (`Fns`): over `Int` `+ - * neg div mod` (floor division; nothing computed of a division by
zero); `dec` from `Int` to `Dec`; over `Dec` `d+ d- d*`, `d/` to a scale (half to even), `round` (half to even),
`roundHalfUp`; over `Str` `++ length`. Rounding happens only where a function says so, and how.

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val x = V("x", Sort.Int)
val limit = Fn("limit", Nil, Sort.Dec)                  // a function of one's own: a constant
val vat = Ap(Fns.round, List(Ap(Fns.dmul, List(D(BigDecimal("1234.567")), D(BigDecimal("0.19")))), I(2)))
val k = Kernel(Theory.empty)
assert(k.derive(Rule.Compute(Eq(vat, D(BigDecimal("234.57"))))).isRight)
assert(Logic.wellSorted(Le(Ap(limit, Nil), D(BigDecimal("1000")))))
assert(!Logic.wellSorted(Le(x, D(BigDecimal("1")))))   // an Int against a Dec
```

## The rules

A theorem is `hypotheses ⊢ conclusion`. Each rule is a case of `Rule`; `Kernel.derive` checks it.

| rule | from | gives |
|---|---|---|
| `Assume(f)` | | `{f} ⊢ f` |
| `Axiom(name)` | the theory's axiom | `⊢ a` |
| `Compute(f)` | `f` closed, of the kernel's functions, evaluated true | `⊢ f` |
| `AndI`, `AndE1`, `AndE2` | `a`, `b` / `a ∧ b` | `a ∧ b` / `a` / `b` |
| `OrI1`, `OrI2`, `OrE` | `a` / `b` / `a ∨ b`, `c` from `a`, `c` from `b` | `a ∨ b` / `a ∨ b` / `c` |
| `ImpI(f)`, `ImpE` | `c` (`f` discharged) / `a → b`, `a` | `f → c` / `b` |
| `NotI(f)`, `NotE`, `Classic`, `FalseE` | `False` from `f` / `¬f`, `f` / `¬¬f` / `False` | `¬f` / `False` / `f` / anything |
| `AllI(x)`, `AllE(t)` | `c`, `x` free in no hypothesis / `∀x. f` | `∀x. c` / `f[t/x]` |
| `ExI`, `ExE(y)` | `f[t/x]` / `∃x. f`, `c` from `f[y/x]`, `y` fresh | `∃x. f` / `c` |
| `Refl(t)`, `Subst` | / `s = u`, `f[s/x]` | `t = t` / `f[u/x]` |
| `Induct(x, f)` | `f[0/x]`, `∀x. 0 ≤ x ∧ f → f[x+1/x]` | `∀x. 0 ≤ x → f` |
| `Norm(f)` | the sides' polynomial forms differ by a constant of the right sign | `f` (a ring identity) |
| `LinComb` | comparisons, each times a coefficient (≥ 0 for an inequality) | `0 ≤ Σ` (`0 <`, if a strict one counts) |
| `Antisym` | `a ≤ b`, `b ≤ a` | `a = b` |
| `Tighten` | over `Int`, `0 ≤ F` | `0 ≤ F/g`, the constant rounded down (`g` the gcd) |
| `MulNonneg`, `Square(t)` | `0 ≤ F`, `0 ≤ G` / | `0 ≤ F·G` / `0 ≤ t·t` |

Substitution avoids capture (a bound variable in the way is renamed `y1`, `y2`, …); formulas are compared up to the
names of bound variables. A theorem of one kernel is refused as a premise by another: a theorem is relative to the
theory it was made under (`kernel.owns(t)`).

Induction, an example — `∀n. 0 ≤ n → 0 ≤ sum(n)` from `sum`'s definition, its arithmetic by `Linarith`:

```scala
val sumFn = Fn("sum", List(Sort.Int), Sort.Int)
def sum(t: Term): Term = Ap(sumFn, List(t))
def plus(a: Term, b: Term): Term = Ap(Fns.add, List(a, b))
val n = V("n", Sort.Int)
val sums = Theory("sums",
  "sum0" -> Eq(sum(I(0)), I(0)),
  "sumS" -> All(n, Imp(Le(I(0), n), Eq(sum(plus(n, I(1))), plus(sum(n), plus(n, I(1)))))))
val ks = Kernel(sums)
def ok(r: Rule): Thm = ks.derive(r).toOption.get
def arith(goal: Formula, theorems: Thm*): Thm = Linarith.decide(ks, goal, Nil, theorems.toList).toOption.flatten.get

val f = Le(I(0), sum(x))
val base = arith(Le(I(0), sum(I(0))), ok(Rule.Axiom("sum0")))
val hyp = And(Le(I(0), x), f)
val h = ok(Rule.Assume(hyp))
val unfold = ok(Rule.ImpE(ok(Rule.AllE(ok(Rule.Axiom("sumS")), x)), ok(Rule.AndE1(h))))
val next = arith(Le(I(0), sum(plus(x, I(1)))), ok(Rule.AndE1(h)), ok(Rule.AndE2(h)), unfold)
val everyN = ok(Rule.Induct(x, f, base, ok(Rule.AllI(x, ok(Rule.ImpI(hyp, next))))))
assert(everyN.concl == All(x, Imp(Le(I(0), x), f)) && everyN.hyps.isEmpty)
```
