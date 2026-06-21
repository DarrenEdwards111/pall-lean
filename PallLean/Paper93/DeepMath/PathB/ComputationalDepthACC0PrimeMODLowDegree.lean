import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeMODFactor

/-!
# Brick A.2 — single prime-`MOD_p` gate as a degree-`(p-1)` `F_p` polynomial (proved)

After the CRT reduction (Brick A.1, `modm_iff_residues`), a composite-`MOD_m` gate is a conjunction of prime-power residue
gates `(weight : ZMod (p^{e_p})) = 0`.  This file represents the **prime case** (`e_p = 1`) exactly by a low-degree
polynomial over `F_p`, the Razborov–Smolensky / Fermat seed:

* the weight casts to the *linear* form `∑ᵢ [xᵢ]` over `F_p`;
* by Fermat (`ZMod.pow_card_sub_one_eq_one`), `y = 0 ↔ y^{p-1} = 0` in `F_p`;
* hence `MOD_p` of the weight `↔ (∑ᵢ [xᵢ])^{p-1} = 0` — a degree-`(p-1)` polynomial (a linear form raised to `p-1`).

Combined with A.1 this gives a low-degree representation of every **squarefree** composite-`MOD` gate (all `e_p = 1`, e.g.
`MOD₆`, `MOD₃₀`).  The prime-power case `e_p ≥ 2` needs Toda lifting (named below, not done here).

## What is proved (clean axioms, no `sorry`)

* **`prime_pow_zero_iff`** (PROVED) — in `ZMod p` (prime `p`): `y = 0 ↔ y^{p-1} = 0`.
* **`hammingWeight_cast`** (PROVED) — `(hammingWeight x : ZMod p) = ∑ i, (if x i then 1 else 0)` (the linear form).
* **`modp_iff_fermat`** (PROVED) — `(hammingWeight x : ZMod p) = 0 ↔ (∑ i, if x i then (1:ZMod p) else 0)^{p-1} = 0` — the
  exact degree-`(p-1)` `F_p` representation of a single prime-`MOD_p` gate.

## Honest scope

This is the **prime** (`e=1`) single-gate representation (degree `p-1`).  It does **not** prove the prime-power (`e≥2`) Toda
lifting, a formal `MvPolynomial` degree-membership, the quasipoly `SYM∘AND` packaging, nor degree-additive depth composition
(Brick C) — i.e. general YBT / `composite_BT_degree` remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)

/-- **In `F_p`, a value is zero iff its `(p-1)`-th power is (PROVED).** -/
theorem prime_pow_zero_iff {p : ℕ} [Fact p.Prime] (y : ZMod p) : y = 0 ↔ y ^ (p - 1) = 0 := by
  have hp2 := (Fact.out : p.Prime).two_le
  constructor
  · intro h; subst h; exact zero_pow (by omega)
  · intro h; by_contra hy; rw [ZMod.pow_card_sub_one_eq_one hy] at h; exact one_ne_zero h

/-- **The Hamming weight casts to the linear form over `F_p` (PROVED).** -/
theorem hammingWeight_cast {n : ℕ} (p : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (hammingWeight x : ZMod p) = ∑ i, (if x i then (1 : ZMod p) else 0) := by
  rw [hammingWeight, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : x i = true <;> simp [h]

/-- **Single prime-`MOD_p` gate as a degree-`(p-1)` `F_p` polynomial (PROVED).** -/
theorem modp_iff_fermat {n : ℕ} (p : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (hammingWeight x : ZMod p) = 0 ↔ (∑ i, (if x i then (1 : ZMod p) else 0)) ^ (p - 1) = 0 := by
  rw [hammingWeight_cast]
  exact prime_pow_zero_iff _

/-!
**The prime single-gate representation, proved.**  A `MOD_p` gate is exactly `(∑ᵢ [xᵢ])^{p-1} = 0` over `F_p` — a degree-
`(p-1)` polynomial.  With A.1 this covers squarefree composite moduli.  Next: prime-power (`e≥2`) Toda lifting, then
degree-additive depth composition — the remaining content of general YBT.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree.prime_pow_zero_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree.modp_iff_fermat
