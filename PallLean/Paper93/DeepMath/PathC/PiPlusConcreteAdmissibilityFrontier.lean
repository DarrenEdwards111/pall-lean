import PallLean.Paper93.DeepMath.PathC.PiPlusCookLevinCoordinates

/-!
# Concrete Pi+ admissibility frontier

The previous files constructed an actual SAT-scale `Pi+` transform by pairing the
Cook--Levin flat variable space into `block × Bool` coordinates.  This file now
plugs that concrete transform into the `PiPlusNFrameAdmissible` interface.

What is proved here is deliberately exact and honest:

* block-locality and unit preservation are already kernel-checked facts of the
  concrete transform;
* the remaining mathematical frontier is precisely the three Route-C fields:
  rank invariance, Width⇒Rank P-side, and identity-minor preservation.

Thus any future proof of those three fields immediately yields the full
admissibility package, constructive Route-C data, and the SAT-decider gauge
subgoals for this concrete `Pi+`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- The exact remaining Route-C obligations for the paired Cook--Levin `Pi+`
transform.  Block-locality and unit preservation are intentionally absent: they
are already proved for `cookLevinPiPlusSATTransformOfPair`. -/
structure CookLevinPairedPiPlusAdmissibilityFrontier
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) : Prop where
  rank_invariant :
    PiPlusRankInvariant M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)
  width_rank_p_side :
    PiPlusWidthRankPSide M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)
  identity_minor_preservation :
    PiPlusIdentityMinorPreservation M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)

/-- The paired Cook--Levin frontier fields give full `PiPlusNFrameAdmissible`
for the concrete transform. -/
theorem cookLevinPiPlusSATTransformOfPair_admissible_of_frontier
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2)
    (F : CookLevinPairedPiPlusAdmissibilityFrontier M n m hn2 htb hns hnpair) :
    PiPlusNFrameAdmissible M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair) where
  block_local :=
    cookLevinPiPlusSATTransformOfPair_blockLocal M n m hn2 htb hns hnpair
  unit_preserving :=
    cookLevinPiPlusSATTransformOfPair_unitPreserving M n m hn2 htb hns hnpair
  rank_invariant := F.rank_invariant
  width_rank_p_side := F.width_rank_p_side
  identity_minor_preservation := F.identity_minor_preservation

/-- The paired Cook--Levin frontier fields give constructive Route-C data. -/
theorem piPlusConstructiveData_of_paired_frontier
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2)
    (F : CookLevinPairedPiPlusAdmissibilityFrontier M n m hn2 htb hns hnpair) :
    PiPlusConstructiveSATGaugeData M n hn2 htb hns :=
  piPlusConstructiveData_of_admissible M n hn2 htb hns
    (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)
    (cookLevinPiPlusSATTransformOfPair_admissible_of_frontier
      M n m hn2 htb hns hnpair F)

/-- The paired Cook--Levin frontier fields discharge the existing SAT-decider
gauge subgoals for the concrete `Pi+` gauge. -/
theorem satDeciderGaugeSubgoals_of_paired_frontier
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2)
    (F : CookLevinPairedPiPlusAdmissibilityFrontier M n m hn2 htb hns hnpair) :
    SATDeciderGaugeSubgoals M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair).gauge :=
  satDeciderGaugeSubgoals_of_piPlusAdmissible M n hn2 htb hns
    (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)
    (cookLevinPiPlusSATTransformOfPair_admissible_of_frontier
      M n m hn2 htb hns hnpair F)

/-- Paper-scale abbreviation for the three remaining fields of concrete
`Pi+` admissibility. -/
abbrev PaperScalePiPlusAdmissibilityFrontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinPairedPiPlusAdmissibilityFrontier M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-- Paper-scale frontier fields give full `PiPlusNFrameAdmissible` for the
concrete paper-scale `Pi+` transform. -/
theorem cookLevinPiPlusSATTransform_paperScale_admissible_of_frontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (F : PaperScalePiPlusAdmissibilityFrontier M htb hns) :
    PiPlusNFrameAdmissible M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns) :=
  cookLevinPiPlusSATTransformOfPair_admissible_of_frontier
    M (2 ^ 804) (2 ^ 803) paperScale_ge_two htb hns
    paperScale_pairing_2_804 F

/-- Paper-scale frontier fields give Route-C constructive data. -/
theorem piPlusConstructiveData_paperScale_of_frontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (F : PaperScalePiPlusAdmissibilityFrontier M htb hns) :
    PiPlusConstructiveSATGaugeData M (2 ^ 804) paperScale_ge_two htb hns :=
  piPlusConstructiveData_of_paired_frontier M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804 F

/-- Paper-scale frontier fields discharge the SAT-decider gauge subgoals for the
concrete paper-scale `Pi+` gauge. -/
theorem satDeciderGaugeSubgoals_paperScale_of_frontier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (F : PaperScalePiPlusAdmissibilityFrontier M htb hns) :
    SATDeciderGaugeSubgoals M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns).gauge :=
  satDeciderGaugeSubgoals_of_paired_frontier M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804 F

/-! ## Axiom audit anchors -/

#print axioms cookLevinPiPlusSATTransformOfPair_admissible_of_frontier
#print axioms piPlusConstructiveData_of_paired_frontier
#print axioms satDeciderGaugeSubgoals_of_paired_frontier
#print axioms cookLevinPiPlusSATTransform_paperScale_admissible_of_frontier
#print axioms piPlusConstructiveData_paperScale_of_frontier
#print axioms satDeciderGaugeSubgoals_paperScale_of_frontier

end PallLean.Paper93.DeepMath.PathC
