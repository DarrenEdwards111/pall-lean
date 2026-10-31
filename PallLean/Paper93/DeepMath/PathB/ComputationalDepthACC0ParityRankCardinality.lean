import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityConstraintRealization
import Mathlib.FieldTheory.Finiteness

/-!
# The exact `2^rank` cardinality of the reachable parity image

`…ACC0ParityConstraintRealization` showed the reachable parity image `Set.range (parityVector S)` is an F₂-subspace
(closed under `0` and `+`).  This file gives the exact cardinality: realizing the parity statistic as an **F₂-linear
map** `parityLinMap S : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)`, the reachable image equals its `range`
(`range_parityVector`), and a finite F₂-vector space has card `2^{finrank}` (`Module.card_eq_pow_finrank`).  Hence

```
Nat.card (Set.range (parityVector S)) = 2 ^ finrank (ZMod 2) (range parityLinMap)
```

So the observer boundary for a parity-gate family is `2^rank`, not `2^k` — `2^k` exactly when the gates are
independent (rank `k`, e.g. disjoint supports), strictly smaller under linear dependence among the parity gates.

## What is proved (clean axioms, no `sorry`)

* `parityLinMap` — the F₂-linear realization of the parity statistic; `parityVector_eq_linMap`.
* `range_parityVector` — the reachable image equals `↑(LinearMap.range parityLinMap)` (the input embedding
  `Bool → ZMod 2` is surjective onto `Fin n → ZMod 2`).
* `parity_subspace_card` — `Fintype.card ↥(range parityLinMap) = 2 ^ finrank` (`Module.card_eq_pow_finrank`).
* `parity_reachable_card` — `Nat.card (Set.range (parityVector S)) = 2 ^ finrank` (the headline).

## Honest scope

This is the quantitative closure of the parity reachable-image story: the search boundary is exactly `2^rank`.  It is
the `MOD₂` case; general `MOD_q` is a `0/1`-feasibility problem over `ZMod q` (not free linear algebra).  Still the
cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization

variable {n k : ℕ}

/-- The F₂-linear map realizing the parity statistic vector. -/
def parityLinMap (S : Fin k → Finset (Fin n)) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun v := fun j => ∑ i ∈ S j, v i
  map_add' u v := by funext j; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- **The parity vector is the linear map applied to the embedded Boolean input (proved).** -/
theorem parityVector_eq_linMap (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) :
    parityVector S x = parityLinMap S (fun i => if x i then (1 : ZMod 2) else 0) := by
  funext j
  simp only [parityVector, modQStatOn_two_eq_sum, parityLinMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- Over `ZMod 2`, `if z = 1 then 1 else 0` recovers `z`. -/
theorem zmod2_ite (z : ZMod 2) : (if decide (z = 1) then (1 : ZMod 2) else 0) = z := by
  revert z; decide

/-- **The reachable parity image equals the linear-map range (proved).**  The Boolean-input embedding is surjective
onto `Fin n → ZMod 2`, so ranging over Boolean inputs covers the whole linear range. -/
theorem range_parityVector (S : Fin k → Finset (Fin n)) :
    Set.range (parityVector S) = ↑(LinearMap.range (parityLinMap S)) := by
  ext y
  simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => if x i then 1 else 0, (parityVector_eq_linMap S x).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨fun i => decide (v i = 1), ?_⟩
    rw [parityVector_eq_linMap]
    congr 1
    funext i
    exact zmod2_ite (v i)

/-- **A finite F₂-vector space has card `2^{finrank}` (proved): the parity range submodule.** -/
theorem parity_subspace_card (S : Fin k → Finset (Fin n)) :
    Fintype.card (LinearMap.range (parityLinMap S)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- **The reachable parity image has exactly `2^rank` cells (proved).**  The observer boundary for a parity-gate
family is `2^rank` — `2^k` exactly when the parity gates are independent. -/
theorem parity_reachable_card (S : Fin k → Finset (Fin n)) :
    Nat.card (Set.range (parityVector S)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S)) := by
  rw [range_parityVector]
  simp only [SetLike.coe_sort_coe]
  rw [Nat.card_eq_fintype_card]
  exact parity_subspace_card S

end PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality.range_parityVector
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityRankCardinality.parity_reachable_card
