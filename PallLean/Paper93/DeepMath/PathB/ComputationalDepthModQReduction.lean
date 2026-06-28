import Mathlib

/-!
# The `MOD_q` reduction — algebraic heart (PROVED); the `q`-ary generalization fenced

`no_parity_circuit` (`ComputationalDepthRSHardnessSkeleton`) closes the `q = 2` (parity) Razborov–Smolensky lower
bound unconditionally.  The general `MOD_q` case (`q ≠ 2`, `q` coprime to `p`) is **also a real theorem**
(Smolensky 1987) — *not* a natural-proofs barrier (that barrier concerns P/poly, far above AC⁰[p]).  What it needs
is the **`q`-ary generalization** of the whole `q = 2` argument: replace the `{−1,+1}` alphabet (`walshFn`,
boosting, dimension) by the `q`-th roots of unity `{1, ω, …, ω^{q-1}}` in a field extension `𝔽_{p^ℓ}` (with
`q ∣ p^ℓ − 1`).

This file proves the **algebraic heart** of that reduction — the part that makes `MOD_q` look like a *full product*,
exactly as parity is `∏(-1)^{xᵢ}`:

  `rootsOfUnity_filter` — for a primitive `q`-th root `ω`, the geometric/Fourier filter
        `Σ_{j<q} ω^{j·a} = q·[q ∣ a]`.
  `modq_indicator_eq` — the `MOD_q` indicator is a Fourier combination of the `q`-ary **full product**
        `∏ᵢ ω^{xᵢ}`:  `q·[q ∣ Σxᵢ] = Σ_{j<q} (∏ᵢ ω^{xᵢ})^j`.  (At `q = 2`, `ω = −1`, this is
        `2·[2 ∣ Σxᵢ] = 1 + ∏(-1)^{xᵢ} = 1 + walshFn univ`, the `q = 2` packaging.)

So `MOD_q` is, up to the field-`q`-ary Fourier transform, the full product `∏ᵢ ω^{xᵢ}` — the object the boosting /
dimension argument bounds.  **What remains (honestly fenced, a real undertaking, not faked):** generalize the
boosting surjection, the Walsh span, and the dimension argument from the binary cube to the `q`-ary cube over
`𝔽_{p^ℓ}`, and instantiate `ω` via a concrete extension with `q ∣ p^ℓ − 1`.  That re-does, `q`-ary, what the
`q = 2` files prove.  It is **not** done here; this file is the algebraic bridge only.
-/

namespace PallLean.Paper93.DeepMath.PathB.ModQReduction

open Finset

/-- **Roots-of-unity filter.**  For a primitive `q`-th root of unity `ω` (`orderOf ω = q`) in a field,
`Σ_{j<q} ω^{j·a} = q` if `q ∣ a` and `0` otherwise — the geometric sum is `q` when `ω^a = 1` and collapses
(telescopes to `0`) otherwise, since `(ω^a)^q = 1`.  The `q`-ary analogue of `[2 ∣ a] = (1 + (-1)^a)/2`. -/
theorem rootsOfUnity_filter {F : Type*} [Field F] {q : ℕ} {ω : F} (hω : orderOf ω = q) (a : ℕ) :
    ∑ j ∈ Finset.range q, ω ^ (j * a) = if q ∣ a then (q : F) else 0 := by
  have hpow : ∀ j, ω ^ (j * a) = (ω ^ a) ^ j := fun j => by rw [mul_comm, pow_mul]
  simp_rw [hpow]
  have hqa : (ω ^ a) ^ q = 1 := by
    rw [← pow_mul, mul_comm a q, pow_mul, ← hω, pow_orderOf_eq_one, one_pow]
  by_cases hdvd : q ∣ a
  · rw [if_pos hdvd]
    have h1 : ω ^ a = 1 := orderOf_dvd_iff_pow_eq_one.mp (hω.symm ▸ hdvd)
    rw [h1]; simp
  · rw [if_neg hdvd]
    have h1 : ω ^ a ≠ 1 := fun h => hdvd (hω ▸ orderOf_dvd_iff_pow_eq_one.mpr h)
    rw [geom_sum_eq h1, hqa]; simp

/-- **`MOD_q` as a Fourier combination of the `q`-ary full product.**  `q·[q ∣ Σxᵢ] = Σ_{j<q} (∏ᵢ ω^{xᵢ})^j`:
the `MOD_q` indicator on the number of `true` bits is a fixed linear combination of powers of the full product
`∏ᵢ ω^{xᵢ}`.  This is the `q`-ary `walshFn_univ_eq` — it makes `MOD_q` a function of the full product, which the
(yet-to-be-generalized) `q`-ary boosting/dimension argument bounds. -/
theorem modq_indicator_eq {F : Type*} [Field F] {n q : ℕ} {ω : F} (hω : orderOf ω = q) (x : Fin n → Bool) :
    (if q ∣ (∑ i, (x i).toNat) then (q : F) else 0)
      = ∑ j ∈ Finset.range q, (∏ i, ω ^ (x i).toNat) ^ j := by
  rw [← rootsOfUnity_filter hω (∑ i, (x i).toNat)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, Nat.mul_comm]

end PallLean.Paper93.DeepMath.PathB.ModQReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.rootsOfUnity_filter
#print axioms PallLean.Paper93.DeepMath.PathB.ModQReduction.modq_indicator_eq
