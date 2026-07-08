import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKRW

/-!
# The N-Frame Scale Ceiling: why the "super-polynomial scale bridge" (H4) is not a bridge

The N-frame program proves a super-**linear** lower bound `Θ(N log N)`: the recursion on a size-`N` object
has depth `d = log₂ N` (binary splitting `F_{k+1} = Mix(F_k(x_L), F_k(x_R))`), and each level contributes
fresh no-amortization debt bounded by the block size, `≤ cN`.  The "Global Godmove" / H4 asks to lift this
to a super-**polynomial** bound.  The synthesis names H4 the "super-polynomial scale bridge": the debt
should not merely add over the `log N` levels but *globally compound* into a super-polynomial quantity.

This file proves that **no such compounding exists inside the recursion** — additive OR multiplicative.
A depth-`d` accumulation with per-level increment bounded by `B` is capped at `d·B` (additive) or `B^d·c₀`
(multiplicative).  With `d = log₂ N`:

  • additive, `B ≤ cN`  ⟹ total `≤ cN·log₂N`  = **polynomial in `N`**;
  • multiplicative, even perfect per-level doubling (`B = 2`) ⟹ total `≤ 2^{log₂N}·c₀ = N·c₀`
    = **polynomial in `N`**.

Consequently a super-polynomial accumulated obstruction *forces a super-polynomial per-level increment*
(`scale_bridge_needs_superpoly_per_level`): the debt at some single scale must already be super-polynomial
on a poly-size block — which is a super-polynomial circuit lower bound at one level, i.e. the destination
itself, not a lemma feeding it.

## The dilemma (no intermediate regime)

  • **Super-log depth** (`d = poly(n)` levels) forces the object to size `N = 2^{poly(n)}`; the debt
    `N log N` is then super-poly in the *input* `n`, but it lower-bounds circuits computing a
    `2^{poly(n)}`-size *explicit* object, which trivially need `≥ 2^{poly(n)}` gates — **vacuous** (a big
    object needs a big circuit; it separates nothing in the decision sense).
  • **Super-poly per-level debt** on a poly-size block is a single-scale super-polynomial circuit lower
    bound — **P ≠ NP in one step**, not a bridge to it.

So **H4 is not weaker than `P ≠ NP`; it is equivalent to a super-polynomial circuit lower bound.** Stating
it as a hypothesis and deriving `P ≠ NP` is sound but content-free (`P ≠ NP → P ≠ NP`).  The theorems below
are the honest crystallization: they prove the *accumulation mechanism* the N-frame uses cannot reach the
far shore, so the far shore must be reached in one step and that step is the whole theorem.

## Scope

Everything here is elementary `ℕ` arithmetic on the accumulation recurrence — the twin of
`ComputationalDepthNFrameKRW.krw_amplifies` (which is the *lower* bound `d·Δ ≤ D d`; this is the *upper*
ceiling `D d ≤ d·B`).  It is unconditional and clean-axiom.  It proves a **no-go for the accumulation
route**, in the same spirit as the repo's other honest no-gos.  It does not prove, assume, or approach
`P ≠ NP`; it locates precisely why the framework's scale is capped.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling

/-- **ADDITIVE SCALE CEILING (proved)**: if the accumulated obstruction starts at `0` and each level adds
at most `B` (`Φ (k+1) ≤ Φ k + B`), then after `d` levels `Φ d ≤ d·B`.  With `d = log₂ N` and `B ≤ cN`,
the ceiling is `cN·log₂N` — polynomial in `N`.  This is the exact upper twin of `krw_amplifies`
(`D 0 + d·Δ ≤ D d`): the same linear accumulation, bounding from above. -/
theorem scale_ceiling_additive (Φ : ℕ → ℕ) (B : ℕ)
    (hΦ0 : Φ 0 = 0) (hstep : ∀ k, Φ (k + 1) ≤ Φ k + B) :
    ∀ d, Φ d ≤ d * B := by
  intro d
  induction d with
  | zero => simp [hΦ0]
  | succ n ih =>
    have hs := hstep n
    have e : (n + 1) * B = n * B + B := by ring
    omega

/-- **THE HONEST CORE — a super-polynomial total forces a super-polynomial per-level increment (proved)**:
if the accumulated obstruction exceeds `target` after `d` levels, then `d·B > target`.  So with depth
`d = log₂ N`, reaching a super-polynomial `target` forces the single-level bound `B > target / log₂ N`,
which is itself super-polynomial.  The "scale bridge" cannot manufacture super-poly out of poly-per-level
over logarithmic depth: the super-poly must already be present at one scale. -/
theorem scale_bridge_needs_superpoly_per_level (Φ : ℕ → ℕ) (B d target : ℕ)
    (hΦ0 : Φ 0 = 0) (hstep : ∀ k, Φ (k + 1) ≤ Φ k + B)
    (hsuper : target < Φ d) :
    target < d * B := by
  have h := scale_ceiling_additive Φ B hΦ0 hstep d
  omega

/-- **MULTIPLICATIVE SCALE CEILING (proved)**: if each level multiplies the obstruction by at most `A`
(`Φ (k+1) ≤ A · Φ k`) and `Φ 0 ≤ c₀`, then `Φ d ≤ A^d · c₀`.  HAL's "globally compounds" is exactly this
regime, and it is still capped: with `d = log₂ N` and constant `A`, `A^{log₂N} = N^{log₂A}` — polynomial
in `N`.  Even perfect doubling (`A = 2`) gives only `N·c₀`. -/
theorem scale_ceiling_multiplicative (Φ : ℕ → ℕ) (A c0 : ℕ)
    (hΦ0 : Φ 0 ≤ c0) (hstep : ∀ k, Φ (k + 1) ≤ A * Φ k) :
    ∀ d, Φ d ≤ A ^ d * c0 := by
  intro d
  induction d with
  | zero => simpa using hΦ0
  | succ n ih =>
    calc Φ (n + 1) ≤ A * Φ n := hstep n
      _ ≤ A * (A ^ n * c0) := Nat.mul_le_mul (le_refl A) ih
      _ = A ^ (n + 1) * c0 := by rw [pow_succ]; ring

/-- **PERFECT DOUBLING STAYS POLYNOMIAL (proved, concrete)**: at `N = 2^100` (depth `100 = log₂ N`), even
if the obstruction *doubles at every level* from a unit base, it reaches only `Φ 100 ≤ N` — polynomial.
The multiplicative "compounding" cannot cross the poly barrier over logarithmic depth. -/
theorem doubling_stays_polynomial_at_2pow100
    (Φ : ℕ → ℕ) (N : ℕ) (hN : N = 2 ^ 100)
    (hΦ0 : Φ 0 ≤ 1) (hstep : ∀ k, Φ (k + 1) ≤ 2 * Φ k) :
    Φ 100 ≤ N := by
  have h := scale_ceiling_multiplicative Φ 2 1 hΦ0 hstep 100
  rw [hN]; simpa using h

/-- **THE CEILING FORCES A SINGLE-SCALE SUPER-POLY LOWER BOUND (proved, concrete)**: at `N = 2^100`
(depth `100`), to accumulate an obstruction exceeding `N^200` the per-level debt `B` must satisfy
`100·B > N^200`, i.e. `B > N^200/100` — a super-polynomial lower bound *at a single scale*, on a poly-size
block.  That single-scale super-poly bound is `P ≠ NP` in one step; the accumulation added nothing.  This
is the precise sense in which H4 is the destination, not a bridge to it. -/
theorem scale_ceiling_forces_superpoly_per_level_at_2pow100
    (Φ : ℕ → ℕ) (B N : ℕ) (_hN : N = 2 ^ 100)
    (hΦ0 : Φ 0 = 0) (hstep : ∀ k, Φ (k + 1) ≤ Φ k + B)
    (hsuper : N ^ 200 < Φ 100) :
    N ^ 200 < 100 * B := by
  have h := scale_bridge_needs_superpoly_per_level Φ B 100 (N ^ 200) hΦ0 hstep hsuper
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling.scale_ceiling_additive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling.scale_bridge_needs_superpoly_per_level
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling.scale_ceiling_multiplicative
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling.doubling_stays_polynomial_at_2pow100
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameScaleCeiling.scale_ceiling_forces_superpoly_per_level_at_2pow100
