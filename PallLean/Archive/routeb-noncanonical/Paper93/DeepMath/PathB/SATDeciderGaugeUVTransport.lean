import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Transporting `piPhi` to the flat SAT-decider gauge space

This file builds a concrete `SATDeciderGaugeMap` by embedding the existing flat
Cook-Levin polynomial space into the `u` side of a UV split, applying the
paper-faithful `piPhi`, and renaming back to the flat space.

The resulting flat endomorphism is the identity: the flat source has no
`v`-variables, so `piPhi` fixes its image.  This gives an honest transported
candidate and proves the structural/rank-monotonicity facts available without
claiming the missing P-side collapse or projected NP preservation.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-- UV split aligned to the existing flat Cook-Levin variable type.

The `u` count is the flat compilation's variable count, while the `v` count is
the paper-faithful tableau count from `cookLevinUVSplit`.  Since
`cook_levin_compilation` has `numVars = n`, this is numerically the same
u/v split as `cookLevinUVSplit M n`, but it avoids dependent casts in the
flat `SATDeciderGaugeSpace`. -/
noncomputable def satDeciderGaugeUVSplit
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    UVSplit where
  numU := (cook_levin_compilation M n hn2 htb hns).numVars
  numV := (cookLevinUVSplit M n).numV

/-- The transported split has the paper-faithful `u` count `n`. -/
theorem satDeciderGaugeUVSplit_numU_eq_n
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (satDeciderGaugeUVSplit M n hn2 htb hns).numU = n :=
  cook_levin_numVars M n hn2 htb hns

/-- The transported split keeps the paper-faithful tableau count. -/
theorem satDeciderGaugeUVSplit_numV_eq_cookLevinUVSplit
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (satDeciderGaugeUVSplit M n hn2 htb hns).numV =
      (cookLevinUVSplit M n).numV :=
  rfl

/-- Embed the flat SAT-decider polynomial space into the `u` side of the UV
split. -/
noncomputable def satDeciderGaugeFlatToUV
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns) :=
  (MvPolynomial.rename
    (satDeciderGaugeUVSplit M n hn2 htb hns).inlU).toLinearMap

/-- A concrete retraction from the transported UV ambient back to the flat
Cook-Levin variable type.  It is only required to be a left inverse on the
`u`-embedded flat image; `v` variables may be sent to any flat variable. -/
noncomputable def satDeciderGaugeUVToFlatIdx
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (k : (satDeciderGaugeUVSplit M n hn2 htb hns).Idx) :
    Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
  ⟨k.val % (cook_levin_compilation M n hn2 htb hns).numVars, by
    have hnum : (cook_levin_compilation M n hn2 htb hns).numVars = n :=
      cook_levin_numVars M n hn2 htb hns
    have hpos : 0 < (cook_levin_compilation M n hn2 htb hns).numVars := by
      omega
    exact Nat.mod_lt _ hpos⟩

/-- The UV-to-flat index map retracts the flat `u` inclusion. -/
theorem satDeciderGaugeUVToFlatIdx_inlU
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (i : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    satDeciderGaugeUVToFlatIdx M n hn2 htb hns
        ((satDeciderGaugeUVSplit M n hn2 htb hns).inlU i) = i := by
  apply Fin.ext
  simp [satDeciderGaugeUVToFlatIdx, UVSplit.inlU, Nat.mod_eq_of_lt i.isLt]

/-- Rename the transported UV ambient back to the flat SAT-decider polynomial
space. -/
noncomputable def satDeciderGaugeUVToFlat
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PMnPoly (satDeciderGaugeUVSplit M n hn2 htb hns) →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  (MvPolynomial.rename
    (satDeciderGaugeUVToFlatIdx M n hn2 htb hns)).toLinearMap

/-- The back-rename is a left inverse of the flat-to-UV embedding. -/
theorem satDeciderGaugeUVToFlat_flatToUV_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeUVToFlat M n hn2 htb hns
        (satDeciderGaugeFlatToUV M n hn2 htb hns p) = p := by
  change MvPolynomial.rename (satDeciderGaugeUVToFlatIdx M n hn2 htb hns)
      (MvPolynomial.rename
        (satDeciderGaugeUVSplit M n hn2 htb hns).inlU p) = p
  rw [MvPolynomial.rename_rename]
  have hcomp :
      satDeciderGaugeUVToFlatIdx M n hn2 htb hns ∘
          (satDeciderGaugeUVSplit M n hn2 htb hns).inlU = id := by
    funext i
    exact satDeciderGaugeUVToFlatIdx_inlU M n hn2 htb hns i
  rw [hcomp]
  exact MvPolynomial.rename_id_apply p

/-- `piPhi` fixes the UV image of every flat SAT-decider polynomial. -/
theorem piPhi_satDeciderGaugeFlatToUV_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    piPhi (satDeciderGaugeUVSplit M n hn2 htb hns)
        (satDeciderGaugeFlatToUV M n hn2 htb hns p) =
      satDeciderGaugeFlatToUV M n hn2 htb hns p := by
  change piPhi (satDeciderGaugeUVSplit M n hn2 htb hns)
      (CoupledSheetPoly.embed (satDeciderGaugeUVSplit M n hn2 htb hns) p) =
    CoupledSheetPoly.embed (satDeciderGaugeUVSplit M n hn2 htb hns) p
  exact piPhi_embed_eq (satDeciderGaugeUVSplit M n hn2 htb hns) p

/-- Concrete flat SAT-decider gauge obtained by transporting the UV-split
`piPhi` projection into the flat gauge space. -/
noncomputable def satDeciderGaugeUVTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  satDeciderGaugeUVToFlat M n hn2 htb hns ∘ₗ
    piPhi (satDeciderGaugeUVSplit M n hn2 htb hns) ∘ₗ
      satDeciderGaugeFlatToUV M n hn2 htb hns

/-- Applying the transported UV gauge to a flat polynomial leaves it fixed. -/
theorem satDeciderGaugeUVTransport_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    satDeciderGaugeUVTransport M n hn2 htb hns p = p := by
  unfold satDeciderGaugeUVTransport
  simp only [LinearMap.comp_apply]
  rw [piPhi_satDeciderGaugeFlatToUV_apply]
  exact satDeciderGaugeUVToFlat_flatToUV_apply M n hn2 htb hns p

/-- The transported UV gauge is the identity on the flat SAT-decider space. -/
theorem satDeciderGaugeUVTransport_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeUVTransport M n hn2 htb hns = LinearMap.id := by
  apply LinearMap.ext
  intro p
  exact satDeciderGaugeUVTransport_apply M n hn2 htb hns p

/-- The transported UV gauge is a projection gauge. -/
theorem satDeciderGaugeUVTransport_isProjectionGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugeUVTransport M n hn2 htb hns) := by
  rw [satDeciderGaugeUVTransport_eq_id]
  exact GaugeMonotonicity.IsProjectionGauge.id

/-- Rank monotonicity for the transported UV gauge in the generic
`GaugeMonotonicity` vocabulary. -/
theorem satDeciderGaugeUVTransport_isRankMonotoneGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugeUVTransport M n hn2 htb hns) := by
  rw [satDeciderGaugeUVTransport_eq_id]
  exact GaugeMonotonicity.IsRankMonotoneGauge.id
    (cook_levin_compilation M n hn2 htb hns).partition

/-- Rank monotonicity for the transported UV gauge, stated as the
SAT-decider gauge subgoal. -/
theorem satDeciderGaugeUVTransport_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugeUVTransport M n hn2 htb hns) :=
  satDeciderGaugeUVTransport_isRankMonotoneGauge M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugeUVSplit_numU_eq_n
#print axioms satDeciderGaugeUVSplit_numV_eq_cookLevinUVSplit
#print axioms satDeciderGaugeUVToFlatIdx_inlU
#print axioms satDeciderGaugeUVToFlat_flatToUV_apply
#print axioms piPhi_satDeciderGaugeFlatToUV_apply
#print axioms satDeciderGaugeUVTransport_apply
#print axioms satDeciderGaugeUVTransport_eq_id
#print axioms satDeciderGaugeUVTransport_isProjectionGauge
#print axioms satDeciderGaugeUVTransport_isRankMonotoneGauge
#print axioms satDeciderGaugeUVTransport_rankMonotonicity

end PallLean.Paper93.DeepMath.PathB
