import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPSideCertificate

/-!
# Final Boolean-ambient rank contradiction bridge

This file combines the Boolean P-side and NP-side certificates.  The key small
rank fact is that the base strict Boolean SPDP window is contained in the
one-zero enlarged inclusive Boolean SPDP window.  Therefore a post-`Pi+` Boolean
NP lower bound at `(log n, log n)` and a post-`Pi+` Boolean P upper bound at
`(log n + 1, log n)` force the same impossible arithmetic sandwich.
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

/-- Base strict Boolean row space is contained in any enlarged inclusive Boolean
row space with enough derivative/shift budget. -/
theorem boolBlockedSpdpSubspace_le_inc_of_le {n : ℕ}
    (B : BlockPartition n) {κ κ' ℓ ℓ' : ℕ} (hκ : κ ≤ κ') (hℓ : ℓ ≤ ℓ')
    (p : BoolPoly n) :
    boolBlockedSpdpSubspace B κ ℓ p ≤ boolBlockedSpdpSubspaceInc B κ' ℓ' p := by
  apply Submodule.span_mono
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact ⟨S, m, le_trans (le_of_eq hlen) hκ, le_trans hdeg hℓ, hvars, hadm, rfl⟩

/-- Corresponding rank comparison: base strict Boolean rank is bounded by the
enlarged inclusive Boolean rank. -/
theorem boolBlockedSpdpRank_le_rankInc_of_le {n : ℕ}
    (B : BlockPartition n) {κ κ' ℓ ℓ' : ℕ} (hκ : κ ≤ κ') (hℓ : ℓ ≤ ℓ')
    (p : BoolPoly n) :
    boolBlockedSpdpRank B κ ℓ p ≤ boolBlockedSpdpRankInc B κ' ℓ' p := by
  unfold boolBlockedSpdpRank boolBlockedSpdpRankInc
  exact Submodule.finrank_mono
    (boolBlockedSpdpSubspace_le_inc_of_le B hκ hℓ p)

/-- Paper-scale post-`Pi+` Boolean base NP rank is bounded by the one-zero
inclusive P-side rank for the same post-`Pi+` polynomial. -/
theorem paperScaleCookLevinPiPlusBoolNPWindowRank_le_oneZeroPSideRank
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    boolBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
        (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
          (paperScaleCompiledBoolPoly M htb hns)) ≤
      boolBlockedSpdpRankInc
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
        (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
          (paperScaleCompiledBoolPoly M htb hns)) := by
  exact boolBlockedSpdpRank_le_rankInc_of_le
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.le_add_right _ _) (by simp)
    (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
      (paperScaleCompiledBoolPoly M htb hns))

/-- Boolean P-side one-zero upper bound and Boolean NP-side lower bound are
arithmetically incompatible at paper scale. -/
theorem paperScaleCookLevinPiPlusBoolPSide_and_NPLower_incompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hP : PaperScaleCookLevinPiPlusBoolPSideRankBoundOneZero M htb hns)
    (hNP : PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns) :
    False := by
  unfold PaperScaleCookLevinPiPlusBoolPSideRankBoundOneZero
    PaperScaleCookLevinPiPlusBoolPSideRankBound at hP
  unfold PaperScaleCookLevinPiPlusBoolNPLowerBound at hNP
  have hchoose_le_rankInc := le_trans hNP
    (paperScaleCookLevinPiPlusBoolNPWindowRank_le_oneZeroPSideRank M htb hns)
  have hchoose_le_pow :
      Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤ (2 ^ 804) ^ 200 :=
    le_trans hchoose_le_rankInc hP
  exact not_lt_of_ge hchoose_le_pow
    (PaperFaithfulCompilation.arithmetic_gap_2pow804
      (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804))

/-- Bundled Boolean final certificate: P-side one-zero bound plus NP-side lower
bound. -/
structure PaperScaleCookLevinPiPlusBoolFinalCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  p_side : PaperScaleCookLevinPiPlusBoolPSideRankBoundOneZero M htb hns
  np_side : PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns

/-- The bundled Boolean final certificate is inconsistent. -/
theorem paperScaleCookLevinPiPlusBoolFinalCertificate_incompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScaleCookLevinPiPlusBoolFinalCertificate M htb hns) :
    False :=
  paperScaleCookLevinPiPlusBoolPSide_and_NPLower_incompatible
    M htb hns D.p_side D.np_side

/-- Closure constructor: legacy inclusive P-side source, Boolean source NP lower,
and Boolean rank invariance together imply the final inconsistent Boolean
certificate. -/
def PaperScaleCookLevinPiPlusBoolClosureInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns ∧
  PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns ∧
  PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns ∧
  PaperScaleCookLevinBoolSourceNPLowerBound M htb hns

/-- The explicit Boolean closure inputs imply contradiction. -/
theorem paperScaleCookLevinPiPlusBoolClosureInputs_incompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (H : PaperScaleCookLevinPiPlusBoolClosureInputs M htb hns) :
    False := by
  rcases H with ⟨hinvInc, hinv, hPlegacy, hNPsource⟩
  exact paperScaleCookLevinPiPlusBoolPSide_and_NPLower_incompatible M htb hns
    (paperScaleCookLevinPiPlusBoolPSideRankBoundOneZero_of_legacyBlockedInc
      M htb hns hinvInc hPlegacy)
    (paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_rankInvariant
      M htb hns hNPsource hinv)

/-! ## Axiom audit anchors -/

#print axioms boolBlockedSpdpSubspace_le_inc_of_le
#print axioms boolBlockedSpdpRank_le_rankInc_of_le
#print axioms paperScaleCookLevinPiPlusBoolNPWindowRank_le_oneZeroPSideRank
#print axioms paperScaleCookLevinPiPlusBoolPSide_and_NPLower_incompatible
#print axioms paperScaleCookLevinPiPlusBoolFinalCertificate_incompatible
#print axioms paperScaleCookLevinPiPlusBoolClosureInputs_incompatible

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
