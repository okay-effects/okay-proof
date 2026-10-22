# What is trusted, and what an effect changes

okay-proof is an LCF-style prover: a theorem is a value of type `Thm`, and only the kernel can make one. A proof is a
program that asks the kernel for steps. This page says what has to be right for a `Thm` to be true, and why making
the inference step an effect (`Infer`) does not add to it.

## The trusted base

- `Kernel.derive`: each rule, a pure function of its premises, checked (`Kernel.scala`).
- `Logic`: sorts, free variables, capture-avoiding substitution, alpha-equivalence.
- `Arithmetic`: the intrinsic evaluator behind `Rule.Compute` — exact integers, exact decimals, rounding only by the
  functions that say so (`round` half to even, `roundHalfUp`, `d/` to a scale), strings. A formula it cannot evaluate
  (a symbol of one's own, a quantifier, a division by zero) is never computed, so it proves nothing about it.
- `Linear` and the linear rules (`Norm`, `LinComb`, `Antisym`, `Tighten`): a term of `Int` or `Dec` read as
  `Σ cᵢ·aᵢ + c` by identities true of the integers and the rationals only (`+ - neg`, a product by a constant, a closed
  computable term its value; an atom's numeric arguments in canonical form, a function giving equal values for equal
  arguments). Why each rule is sound, in one line each:
  - `Norm`: if `b - a` normalizes to a constant `c`, then `b - a = c` for every value of the atoms, so `a = b`,
    `a ≤ b`, `a < b` hold as `c = 0`, `c ≥ 0`, `c > 0`;
  - `LinComb`: premises `0 ≤ Fᵢ` (`<`, `=`) true; a sum of non-negative multiples of non-negatives is non-negative,
    positive if a strict one has a positive multiple; any multiple of `0 = F` is `0`. Over `Int`, `a < b` is read
    `a + 1 ≤ b` (true of the integers), and the multipliers are integers, so the sum is a term of `Int`;
  - `Antisym`: the orders are antisymmetric;
  - `Tighten`: over `Int`, `Σcᵢxᵢ ≥ -k` with `g` dividing every `cᵢ` gives `Σ(cᵢ/g)xᵢ ≥ ⌈-k/g⌉ = -⌊k/g⌋`, the left
    side an integer.

  The decision procedure that finds the multipliers (`Linarith`: Fourier–Motzkin, the integers' tightening) is NOT
  trusted: its result is a list of steps the kernel checks. Lemmas (`Lemmas`) are theorems proved by the kernel, not
  axioms.
- The THEORY's content: its axioms are taken as given. A policy that is wrong gives wrong theorems, correctly derived
  from it. A theory refuses an axiom that is open or ill-sorted, nothing more.
- Scala's encapsulation: `Thm`'s constructor is `private[Kernel]`. Reflection, `asInstanceOf` on a forged object, or
  a debugger can break that, as they can break any JVM invariant; code that can do those is trusted anyway.

Everything else is NOT trusted: proof search (`Auto`), certificates (`Certificate`), every handler and interceptor.
A bug there can fail to find a proof, never make a false theorem.

## A step as an effect

A proof program performs `Infer.Step(rule)`; the kernel is the handler that answers it (`Infer.by(kernel)`). Between
them any interceptor of okay-simple's may stand. What it can do, and why that is safe:

| an interceptor … | effect | why it is safe |
|---|---|---|
| sees each step (`observe`) | an audit trail of the proof, step by step | it only reads |
| refuses a step (`around`, `Infer.refuse`) | the proof stops with the reason | no theorem is made |
| answers from a cache | the same theorem again | the cached theorem was made by the kernel from that very step |
| answers with ANOTHER true theorem | refused by `Infer.step`: `t.by eq rule` fails | a theorem remembers the step that made it |
| answers with a theorem of ANOTHER kernel, made from this very step under a theory of its own | refused: no rule takes a premise of another kernel, and `Infer.by` refuses one as the result | a theorem is relative to the kernel that owns it (`Kernel.owns`) |
| makes a `Thm` | impossible | the constructor is the kernel's |

So the effect gives control (who may use which rule, which axioms, at what cost) and audit (every step seen) without
widening the trusted base. The checks are tested in `EffectsSuite`.

## Theorems are relative to a kernel

A kernel is made for one theory. A theorem of a kernel is a premise of that kernel's rules only, and a consumer asks
`kernel.owns(t)` before acting on `t` — the gate in `PolicySuite` does, and also checks the conclusion is exactly
what it is about to do and the hypotheses are facts it knows.

## Certificates

A certificate is a proof as data. It is never turned into a `Thm` directly: `Certificate.check` parses it and
derives every step again with the kernel it is given. A changed amount, a missing step, a premise that refers
forward, a theory without the policy: refused.
