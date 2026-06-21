import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrApprox

/-!
# Brick (balancedness) — a nonzero linear form over `F_p` vanishes with probability `1/p` (proved)

The genuine probabilistic heart of the Razborov–Smolensky `OR` approximator (`…ACC0OrApprox`).  For a fixed nonzero
`x : Fin n → F_p`, the linear functional `a ↦ ∑ᵢ xᵢ aᵢ` is **surjective**, so its zero-fiber is the kernel of a rank-1 map
and has exactly `p^{n-1}` points — i.e. `∑ᵢ xᵢ aᵢ = 0` for a `1/p` fraction of all `a`.

This is exactly the "bad-set" measure bound that `orApprox` needed: for any *nonzero* input `x`, a uniformly random
coefficient vector `a` makes the linear form vanish (and the approximator err) with probability only `1/p`.  Combined with
`orApprox_eval_of_form_ne_zero`, a single random linear form computes `OR` correctly with probability `≥ 1-1/p`.

## What is proved (clean axioms, no `sorry`)

* **`card_linearForm_eq_zero`** (PROVED) — for `x ≠ 0`,
  `(univ.filter (fun a => ∑ᵢ xᵢ aᵢ = 0)).card = p^{n-1}` — the zero-fiber is a `1/p` fraction.

## Honest scope

This is the **single-form** balancedness bound (the `1/p` bad-set measure).  It does **not** assemble the `t`-fold
amplification (error `p^{-t}` at degree `t(p-1)`), the averaging/existence of one globally-good polynomial, prime-power
composition, nor `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Balancedness

open Module

/-- **Balancedness (PROVED): a nonzero linear form over `F_p` vanishes on a `1/p` fraction of inputs.**
The zero-fiber of `a ↦ ∑ᵢ xᵢ aᵢ` has exactly `p^{n-1}` points when `x ≠ 0`. -/
theorem card_linearForm_eq_zero (p n : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) (hx : x ≠ 0) :
    (Finset.univ.filter (fun a : Fin n → ZMod p => ∑ i, x i * a i = 0)).card = p ^ (n - 1) := by
  classical
  -- The linear functional `L a = ∑ᵢ xᵢ aᵢ`.
  let L : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p := ∑ i, (x i) • LinearMap.proj i
  have hLa : ∀ a, L a = ∑ i, x i * a i := fun a => by simp [L, LinearMap.proj]
  -- `L` is surjective (some `xⱼ ≠ 0`).
  have hsurj : Function.Surjective L := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    rw [Pi.zero_apply] at hj
    intro c
    refine ⟨Pi.single j (c * (x j)⁻¹), ?_⟩
    rw [hLa, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_comm c ((x j)⁻¹), ← mul_assoc, mul_inv_cancel₀ hj, one_mul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Rank-nullity: `finrank ker = n - 1`.
  have hrange : Module.finrank (ZMod p) (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hker : Module.finrank (ZMod p) (LinearMap.ker L) = n - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange] at h
    have hdom : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by
      simp [Module.finrank_fintype_fun_eq_card]
    rw [hdom] at h; omega
  -- Cardinality of the kernel.
  have hcard : Fintype.card (LinearMap.ker L) = p ^ (n - 1) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hker]
  -- The filter equals the kernel as a set, so its card is the kernel's card.
  have hfilter_eq : (Finset.univ.filter (fun a : Fin n → ZMod p => ∑ i, x i * a i = 0))
      = (Finset.univ.filter (fun a : Fin n → ZMod p => a ∈ LinearMap.ker L)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker, hLa]
  rw [hfilter_eq, ← hcard]
  exact (Fintype.card_subtype (fun a : Fin n → ZMod p => a ∈ LinearMap.ker L)).symm

/-!
**Balancedness, proved.**  A nonzero linear form over `F_p` is zero on exactly a `1/p` fraction of coefficient vectors —
the bad-set measure bound for the RS `OR` approximator: a single random linear form computes `OR` with error `≤ 1/p`.
Remaining (open, not faked): `t`-fold amplification, existence of a globally-good polynomial, and the rest of YBT.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Balancedness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Balancedness.card_linearForm_eq_zero
