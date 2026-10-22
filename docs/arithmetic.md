# Arithmetic

Three levels, each a certificate the kernel checks — the procedures that find them are trusted for nothing.

## Computed: a closed formula, one step

`Rule.Compute(f)`: `f` has no variable and no symbol of one's own; it is evaluated exactly — unbounded integers,
decimals of any scale, rounding only by a function that names it.

```scala
import okay.proof.*
import okay.proof.Formula.*
import okay.proof.Term.*

val k = Kernel(Theory.empty)
def dec(s: String): Term = D(BigDecimal(s))
def computes(f: Formula): Boolean = k.derive(Rule.Compute(f)).isRight
assert(computes(Eq(Ap(Fns.dadd, List(dec("0.1"), dec("0.2"))), dec("0.3"))))            // exact: no floating point
assert(computes(Eq(Ap(Fns.round, List(dec("2.345"), I(2))), dec("2.34"))))               // half to even
assert(computes(Eq(Ap(Fns.roundHalfUp, List(dec("2.345"), I(2))), dec("2.35"))))
assert(computes(Eq(Ap(Fns.ddiv, List(dec("10"), dec("3"), I(2))), dec("3.33"))))
assert(computes(Eq(Ap(Fns.div, List(I(-7), I(2))), I(-4))))                              // floor division
```

## Linear, with variables: `Linarith`

A comparison over `Int` or `Dec` from facts (and theorems given): the negated goal refuted, the multipliers found by
Fourier–Motzkin elimination are the certificate (`LinComb`, Farkas'). Terms of one's own are atoms:

```scala
val (x, y, z) = (V("x", Sort.Int), V("y", Sort.Int), V("z", Sort.Int))
def proves(goal: Formula, facts: Formula*): Boolean = Linarith.decide(k, goal, facts.toList).exists(_.isDefined)

assert(proves(Le(x, z), Le(x, y), Le(y, z)))
assert(proves(Lt(x, z), Lt(x, y), Le(y, z)))
assert(proves(Eq(x, I(4)), Eq(x, Ap(Fns.add, List(y, I(1)))), Eq(y, I(3))))
val spent = Ap(Fn("spent", Nil, Sort.Dec), Nil)
assert(proves(Le(Ap(Fns.dadd, List(spent, dec("900"))), dec("1500")), Le(spent, dec("300.00"))))
assert(!proves(Le(y, x), Le(x, y)))                                                        // does not follow
```

Over `Dec` (the rationals) this is complete.

## The integers: the Omega test

Over `Int` a strict bound is `+ 1 ≤`, a derived bound is tightened by the gcd of its coefficients (`Tighten`), and
what that does not refute goes to the OMEGA TEST (Pugh): exact elimination where it can be; an equation with no
coefficient ±1 solved through a fresh `σ` (`mod̂`, `∃σ. σ = Q` and `ExE`); otherwise the dark shadow, or the grey
shadow's splinters, each a case. Complete for linear constraints over the integers:

```scala
def lin(a: Int, u: Term, b: Int, v: Term): Term =
  Ap(Fns.add, List(Ap(Fns.mul, List(I(a), u)), Ap(Fns.mul, List(I(b), v))))
val falsum = Lt(I(1), I(0))

assert(proves(Not(Lt(x, y)), Lt(y, Ap(Fns.add, List(x, I(1))))))   // x < y < x + 1: no integer between
assert(proves(falsum, Eq(lin(6, x, 9, y), I(4))))                   // 6x + 9y = 4: 3 does not divide 4
// Pugh's example: rational solutions, no integer one
assert(proves(falsum, Le(I(27), lin(11, x, 13, y)), Le(lin(11, x, 13, y), I(45)),
  Le(I(-10), lin(7, x, -9, y)), Le(lin(7, x, -9, y), I(4))))
assert(!proves(falsum, Eq(lin(3, x, 5, y), I(1))))                  // x = 2, y = −1
```

The tests hold it to brute force on 600 random systems, among them 300 crossing thin strips where the rationals'
elimination alone does not refute.

## Products of variables

A term is a polynomial: `Norm` proves ring identities. The kernel knows that products of non-negatives are
non-negative (`MulNonneg`) and squares are (`Square`); the search adds the premises' pairwise products and the atoms'
squares, then eliminates (as Mathlib's `nlinarith`). Sound, not complete — nothing can be over the integers:

```scala
def times(u: Term, v: Term): Term = Ap(Fns.mul, List(u, v))
val (p, q) = (V("p", Sort.Dec), V("q", Sort.Dec))
assert(k.derive(Rule.Norm(Eq(times(Ap(Fns.add, List(x, y)), Ap(Fns.add, List(x, y))),
  Ap(Fns.add, List(Ap(Fns.add, List(times(x, x), times(I(2), times(x, y)))), times(y, y)))))).isRight)
assert(proves(Le(I(0), times(x, y)), Le(I(0), x), Le(I(0), y)))
assert(proves(Le(I(4), times(x, x)), Le(I(2), x)))
assert(proves(Le(Ap(Fns.dmul, List(p, q)), dec("50.00")),
  Le(dec("0"), p), Le(p, dec("10.00")), Le(dec("0"), q), Le(q, dec("5"))))
assert(!proves(Le(I(0), times(x, y)), Le(I(0), x)))
```
