import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageFinalBridge

/-!
# P-side transport for the corrected raw-image Boolean surface

This file connects the corrected raw-image P-side upper bound to a raw inclusive
rank budget for the post-`Pi+` raw polynomial, and then to the existing legacy
inclusive blocked-rank budget.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Inclusive corrected raw-image rank is bounded by inclusive raw rank. -/
theorem boolRawImageBlockedSpdpRankInc_le_rawBlockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpRankInc B κ ℓ q ≤ rawBlockedSpdpRankInc B κ ℓ q := by
  unfold boolRawImageBlockedSpdpRankInc boolRawImageBlockedSpdpSubspaceInc rawBlockedSpdpRankInc
  exact Submodule.finrank_map_le (liftToBoolLinearMap n) (rawBlockedSpdpSubspaceInc B κ ℓ q)

/-- A raw inclusive rank budget for the post-`Pi+` raw polynomial supplies the
corrected raw-image P-side one-zero bound. -/
theorem paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_rawIncBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : rawBlockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤
      (2 ^ 804) ^ 200) :
    PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero
  exact le_trans
    (boolRawImageBlockedSpdpRankInc_le_rawBlockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))))
    hraw

/-- A legacy inclusive unprojected blocked-rank budget for the post-`Pi+` raw
polynomial supplies the corrected raw-image P-side one-zero bound. -/
theorem paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_legacyPostGaugeIncBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlegacy : blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200) :
    PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_rawIncBound
    M htb hns
    (le_trans
      (rawBlockedSpdpRankInc_le_blockedSpdpRankInc_univ
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))))
      hlegacy)

/-- No-decider surface using a legacy post-gauge inclusive P-side budget rather
than the raw-image P-side bound directly. -/
theorem no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (HInv : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromDecider M htb hns
  · intro hdec
    exact paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_legacyPostGaugeIncBound
      M htb hns (HPlegacy hdec)
  · exact HInv
  · exact HrawNP
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms boolRawImageBlockedSpdpRankInc_le_rawBlockedSpdpRankInc
#print axioms paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_rawIncBound
#print axioms paperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero_of_legacyPostGaugeIncBound
#print axioms no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
