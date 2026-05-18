import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankLegacyBridge

/-!
# Paper-scale Boolean Pi+ rank bridges

This file specializes the Boolean-rank migration bridges to the concrete
paper-scale Cook-Levin `Pi+` transform.  Downstream Route-C closeout files should
be able to state assumptions over the concrete paper-scale object without
manually passing `cookLevinPiPlusSATTransform_paperScale` everywhere.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace BoolPoly

/-- Concrete paper-scale strict Boolean `Pi+` rank-invariance obligation. -/
abbrev PaperScaleCookLevinPiPlusBoolRankInvariant
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRankInvariant (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Concrete paper-scale inclusive Boolean `Pi+` rank-invariance obligation. -/
abbrev PaperScaleCookLevinPiPlusBoolRankInvariantInc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRankInvariantInc (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale strict raw-budget bridge for the concrete Cook-Levin `Pi+`. -/
theorem paperScaleCookLevinPiPlusBoolRank_le_of_rankInvariant_of_rawBudget
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars}
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns)
    (hraw : RawToBoolRankBudget
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ C p) :
    boolBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns) p) ≤ C := by
  exact piPlusBoolRank_le_of_rankInvariant_of_rawBudget
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hinv hraw

/-- Paper-scale inclusive raw-budget bridge for the concrete Cook-Levin `Pi+`. -/
theorem paperScaleCookLevinPiPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars}
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns)
    (hraw : RawToBoolRankBudgetInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ C p) :
    boolBlockedSpdpRankInc
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns) p) ≤ C := by
  exact piPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hinv hraw

/-- Paper-scale strict legacy blocked-rank bridge for the concrete Cook-Levin
`Pi+`. -/
theorem paperScaleCookLevinPiPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars}
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns)
    (hlegacy : blockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        (p : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)
        Finset.univ ≤ C) :
    boolBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns) p) ≤ C := by
  exact piPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hinv hlegacy

/-- Paper-scale inclusive legacy blocked-rank bridge for the concrete Cook-Levin
`Pi+`. -/
theorem paperScaleCookLevinPiPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars}
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns)
    (hlegacy : blockedSpdpRankInc
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        (p : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)
        Finset.univ ≤ C) :
    boolBlockedSpdpRankInc
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns) p) ≤ C := by
  exact piPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hinv hlegacy

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusBoolRank_le_of_rankInvariant_of_rawBudget
#print axioms paperScaleCookLevinPiPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget
#print axioms paperScaleCookLevinPiPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le
#print axioms paperScaleCookLevinPiPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
