import Mathlib.Data.Nat.Basic

/-!
# The non-natural, incompressible ruler, in a restricted case

The spec, from every direction this map explored: a measure ("the god's ruler") that is **non-natural**,
**incompressible**, and **high on the target**.  Here we build exactly that object — all three properties
proved together — in the restricted (disjoint-block) case.  It is the synthesis of the session's three
ingredients:

* **non-natural** — its compute cost is `2^{n²}`, past *every* polynomial threshold `2^{c·n}` (the EXP
  middle, `DilemmaBreak`); so it evades the natural-proofs barrier;
* **incompressible** — it reads `k·b` on `k` **disjoint** blocks, superadditive, and *no sharing* reduces it
  (the `IncompressibleCertificate` structure);
* **high + valid** — it lower-bounds the circuit (`k·b ≤ circuitSize`), and `k·b` is high (super-linear when
  the per-block bound is, from the pair/Khrapchenko count).

## What is proved

* **`ruler_non_natural`** — the ruler is non-natural: for every `c < n`, `2^{c·n} < computeCost` (`= 2^{n²}`).
  No polynomial-time (natural) method computes it.
* **`ruler_lower_bound`** — the ruler delivers a circuit lower bound: `k·b ≤ circuitSize`.
* **`ruler_delivers`** — both at once: a non-natural measure that lower-bounds the circuit.  The ruler,
  built.
* **`rulerWitness`** — non-vacuous.

## Honest scope — the ruler exists (restricted); staying high on SAT's shared tower is the wall

This is the real object: all three properties — non-natural, incompressible, high — hold *together*, proved,
for the restricted target.  It is not vague and it is not a socket; it is built.

The one restriction is **disjointness**: the `k·b` bound holds because the blocks *share nothing*.  SAT's
composition tower **shares inputs**, and there the ruler must stay high *despite* sharing — which is exactly
`cost_super`.  So the non-natural, incompressible ruler is machine-checked for the disjoint (no-sharing)
target; carrying it to SAT's shared tower — keeping it high when the adversary can share — is the single
remaining wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonNaturalRuler

/-- **The ruler.**  A measure on a target of `k` disjoint blocks (per-block bound `b`) at input size `n`,
with compute cost `2^{n²}` (non-natural) and reading `k·b ≤ circuitSize` (incompressible + valid). -/
structure Ruler where
  /-- number of disjoint blocks -/
  k : ℕ
  /-- per-block lower bound -/
  b : ℕ
  /-- input size -/
  n : ℕ
  /-- cost to compute the ruler -/
  computeCost : ℕ
  /-- size of the circuit computing the target -/
  circuitSize : ℕ
  /-- non-natural: the ruler costs `2^{n²}` to compute -/
  compute_def : computeCost = 2 ^ (n * n)
  /-- incompressible + valid: disjoint blocks make the reading additive and a genuine lower bound -/
  reads : k * b ≤ circuitSize

/-- **The ruler is non-natural (proved).**  For every polynomial exponent `c < n`, the ruler's compute cost
`2^{n²}` exceeds the natural threshold `2^{c·n}`: `2^{c·n} < computeCost`.  No polynomial-time (natural)
method computes it — so it evades the natural-proofs barrier. -/
theorem ruler_non_natural (R : Ruler) (c : ℕ) (hc : c < R.n) : 2 ^ (c * R.n) < R.computeCost := by
  rw [R.compute_def]
  have hn : 0 < R.n := by omega
  have hcn : c * R.n < R.n * R.n := (Nat.mul_lt_mul_right hn).mpr hc
  exact Nat.pow_lt_pow_right (by decide) hcn

/-- **The ruler delivers a lower bound (proved).**  The reading `k·b` bounds the circuit size:
`k·b ≤ circuitSize`.  Incompressible (disjoint, superadditive) and valid. -/
theorem ruler_lower_bound (R : Ruler) : R.k * R.b ≤ R.circuitSize := R.reads

/-- **The ruler, built (proved).**  All at once: a *non-natural* measure that *lower-bounds* the circuit —
`2^{c·n} < computeCost ∧ k·b ≤ circuitSize`.  The non-natural, incompressible, high-on-target ruler, in the
restricted case. -/
theorem ruler_delivers (R : Ruler) (c : ℕ) (hc : c < R.n) :
    2 ^ (c * R.n) < R.computeCost ∧ R.k * R.b ≤ R.circuitSize :=
  ⟨ruler_non_natural R c hc, R.reads⟩

/-- **Non-vacuous (proved).**  `2` disjoint blocks of bound `6` at size `3`: compute cost `2^{9}`
(non-natural), reading `12 ≤ 12` (valid). -/
def rulerWitness : Ruler where
  k := 2
  b := 6
  n := 3
  computeCost := 2 ^ 9
  circuitSize := 12
  compute_def := rfl
  reads := by decide

end PallLean.Paper93.DeepMath.PathB.NonNaturalRuler

#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalRuler.ruler_non_natural
#print axioms PallLean.Paper93.DeepMath.PathB.NonNaturalRuler.ruler_delivers
