import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank

/-!
# Exact dilution in the existing concrete Route B rate schedule

The concrete constructor in `RouteBBridgeAConcreteBudget` chooses
`rankLogRate = log (1 + theta * eta) / pocketRank` and assumes
`delta <= rankLogRate * kappa`.  Each concrete pocket has full rank, so
`pocketRank = kappa * gadgetN`.  This file calculates the resulting local
floor exactly: `rankLogRate * kappa = log (1 + theta * eta) / gadgetN`.

The invariant, concrete gadget, and requested lower-floor hypothesis are
unchanged.  No SAT correctness or runtime premise is discharged here.
Narrow imports keep this calculation independent of the broader Route B wrapper.
-/

namespace ConcreteRateDilution

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.PathB

/-- Exact rank of the existing positive-definite concrete gadget. -/
theorem compiled_rank_exact (alpha : ℝ) (gadgetN : ℕ)
    (halpha : 0 < alpha) (hgadgetN : 1 ≤ gadgetN) :
    (compiledGadget alpha gadgetN).rank = gadgetN := by
  have hd := (compiledGadget_posDef alpha gadgetN halpha hgadgetN).det_pos
  have hu : IsUnit (compiledGadget alpha gadgetN) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hd))
  simpa using Matrix.rank_of_isUnit _ hu

/-- Exact rank of the existing block-diagonal pocket family. -/
theorem pocket_rank_exact (alpha : ℝ) (kappa gadgetN : ℕ)
    (halpha : 0 < alpha) (hgadgetN : 1 ≤ gadgetN) :
    (pocketFamily alpha kappa gadgetN).rank = kappa * gadgetN := by
  rw [pocketFamily_rank, compiled_rank_exact alpha gadgetN halpha hgadgetN]

/-- Increasing `kappa` cancels out of the local floor in this rate schedule. -/
theorem concrete_rate_mul_kappa_eq_log_div_gadgetN
    (alpha theta eta : ℝ) (kappa gadgetN : ℕ)
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 1 ≤ gadgetN) :
    (Real.log (1 + theta * eta) /
        ((pocketFamily alpha kappa gadgetN).rank : ℝ)) * (kappa : ℝ) =
      Real.log (1 + theta * eta) / (gadgetN : ℝ) := by
  have hkappa_ne : (kappa : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkappa
  have hgadgetN_ne : (gadgetN : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : gadgetN ≠ 0)
  rw [pocket_rank_exact alpha kappa gadgetN halpha hgadgetN, Nat.cast_mul]
  field_simp

/-- The constructor's assumed local floor has this exact scalar meaning. -/
theorem concrete_local_floor_iff
    (alpha theta eta delta : ℝ) (kappa gadgetN : ℕ)
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 1 ≤ gadgetN) :
    (delta ≤ (Real.log (1 + theta * eta) /
        ((pocketFamily alpha kappa gadgetN).rank : ℝ)) * (kappa : ℝ)) ↔
      delta ≤ Real.log (1 + theta * eta) / (gadgetN : ℝ) := by
  rw [concrete_rate_mul_kappa_eq_log_div_gadgetN
    alpha theta eta kappa gadgetN halpha hkappa hgadgetN]

/-- A positive requested local floor bounds the size of each pocket when
`theta` and `eta` are fixed.  This is a condition on this constructor, not a
lower bound for SAT computations. -/
theorem gadgetN_le_log_div_delta_of_concrete_local_floor
    (alpha theta eta delta : ℝ) (kappa gadgetN : ℕ)
    (halpha : 0 < alpha) (hkappa : 0 < kappa) (hgadgetN : 1 ≤ gadgetN)
    (hdelta : 0 < delta)
    (hfloor : delta ≤ (Real.log (1 + theta * eta) /
        ((pocketFamily alpha kappa gadgetN).rank : ℝ)) * (kappa : ℝ)) :
    (gadgetN : ℝ) ≤ Real.log (1 + theta * eta) / delta := by
  have hgadgetN_pos : (0 : ℝ) < gadgetN := by
    exact_mod_cast (by omega : 0 < gadgetN)
  rw [concrete_rate_mul_kappa_eq_log_div_gadgetN
    alpha theta eta kappa gadgetN halpha hkappa hgadgetN] at hfloor
  apply (le_div_iff₀ hdelta).mpr
  simpa [mul_comm] using (le_div_iff₀ hgadgetN_pos).mp hfloor

end ConcreteRateDilution

#print axioms ConcreteRateDilution.compiled_rank_exact
#print axioms ConcreteRateDilution.pocket_rank_exact
#print axioms ConcreteRateDilution.concrete_rate_mul_kappa_eq_log_div_gadgetN
#print axioms ConcreteRateDilution.concrete_local_floor_iff
#print axioms ConcreteRateDilution.gadgetN_le_log_div_delta_of_concrete_local_floor
