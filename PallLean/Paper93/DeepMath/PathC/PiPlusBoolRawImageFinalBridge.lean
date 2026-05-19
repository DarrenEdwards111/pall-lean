import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRank

/-!
# Final contradiction bridge for the corrected raw-image Boolean SPDP surface

`PiPlusBoolRawImageRank` fixes the NP-side quotient issue by defining Boolean
SPDP rows as raw ordinary derivative rows mapped into `BoolPoly`.  This file
adds the corresponding final-rank bridge in that corrected surface.

The P-side upper bound is deliberately stated for the corrected raw-image
inclusive rank of the post-`Pi+` raw polynomial.  This avoids mixing it with the
old representative-derivative Boolean row space, whose NP-side interpretation is
blocked by the derivative obstruction.
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

/-- Corrected inclusive Boolean SPDP subspace: inclusive raw derivative rows
mapped into the Boolean ambient. -/
noncomputable def boolRawImageBlockedSpdpSubspaceInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (BoolPoly n) :=
  Submodule.map (liftToBoolLinearMap n) (rawBlockedSpdpSubspaceInc B κ ℓ q)

/-- Corrected inclusive Boolean SPDP rank. -/
noncomputable def boolRawImageBlockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) : ℕ :=
  Module.finrank ℚ (boolRawImageBlockedSpdpSubspaceInc B κ ℓ q)

instance boolRawImageBlockedSpdpSubspaceInc_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ (boolRawImageBlockedSpdpSubspaceInc B κ ℓ q) := by
  unfold boolRawImageBlockedSpdpSubspaceInc
  infer_instance

/-- Strict corrected raw-image rows are contained in enlarged inclusive
corrected raw-image rows. -/
theorem boolRawImageBlockedSpdpSubspace_le_inc_of_le {n : ℕ}
    (B : BlockPartition n) {κ κ' ℓ ℓ' : ℕ} (hκ : κ ≤ κ') (hℓ : ℓ ≤ ℓ')
    (q : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpSubspace B κ ℓ q ≤
      boolRawImageBlockedSpdpSubspaceInc B κ' ℓ' q := by
  unfold boolRawImageBlockedSpdpSubspace boolRawImageBlockedSpdpSubspaceInc
  apply Submodule.map_mono
  apply Submodule.span_mono
  intro r hr
  rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact ⟨S, m, le_trans (le_of_eq hlen) hκ, le_trans hdeg hℓ, hvars, hadm, rfl⟩

/-- Rank comparison between strict corrected raw-image rows and enlarged
inclusive corrected raw-image rows. -/
theorem boolRawImageBlockedSpdpRank_le_rankInc_of_le {n : ℕ}
    (B : BlockPartition n) {κ κ' ℓ ℓ' : ℕ} (hκ : κ ≤ κ') (hℓ : ℓ ≤ ℓ')
    (q : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpRank B κ ℓ q ≤
      boolRawImageBlockedSpdpRankInc B κ' ℓ' q := by
  unfold boolRawImageBlockedSpdpRank boolRawImageBlockedSpdpRankInc
  exact Submodule.finrank_mono
    (boolRawImageBlockedSpdpSubspace_le_inc_of_le B hκ hℓ q)

/-- Paper-scale corrected raw-image source rank is invariant under the concrete
`Pi+` raw gauge at the NP window. -/
def PaperScaleCookLevinPiPlusBoolRawImageRankInvariant
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  boolRawImageBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) =
    boolRawImageBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- P-side upper bound in the corrected raw-image inclusive surface for the
post-`Pi+` raw polynomial. -/
def PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  boolRawImageBlockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤
    (2 ^ 804) ^ 200

/-- Corrected raw-image P-side upper and corrected raw-image NP lower are
arithmetically incompatible at paper scale. -/
theorem paperScaleCookLevinPiPlusBoolRawImagePSide_and_NPLower_incompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hP : PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero M htb hns)
    (hInv : PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns)
    (hNP : Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
      paperScaleCookLevinBoolRawImageSourceNPRank M htb hns) :
    False := by
  unfold PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero at hP
  unfold PaperScaleCookLevinPiPlusBoolRawImageRankInvariant at hInv
  unfold paperScaleCookLevinBoolRawImageSourceNPRank at hNP
  let q := compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)
  let qplus := (cookLevinPiPlusSATTransform_paperScale M htb hns).gauge q
  let B := (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
  have hNPplus : Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
      boolRawImageBlockedSpdpRank B (Nat.log 2 (2 ^ 804))
        (Nat.log 2 (2 ^ 804)) qplus := by
    change Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
      boolRawImageBlockedSpdpRank B (Nat.log 2 (2 ^ 804))
        (Nat.log 2 (2 ^ 804)) qplus
    rw [hInv]
    exact hNP
  have hstrict_le_inc :
      boolRawImageBlockedSpdpRank B (Nat.log 2 (2 ^ 804))
          (Nat.log 2 (2 ^ 804)) qplus ≤
        boolRawImageBlockedSpdpRankInc B (Nat.log 2 (2 ^ 804) + 1)
          (Nat.log 2 (2 ^ 804) + 0) qplus :=
    boolRawImageBlockedSpdpRank_le_rankInc_of_le B
      (Nat.le_add_right _ _) (by simp) qplus
  have hchoose_le_pow :
      Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤ (2 ^ 804) ^ 200 :=
    le_trans (le_trans hNPplus hstrict_le_inc) hP
  exact not_lt_of_ge hchoose_le_pow
    (PaperFaithfulCompilation.arithmetic_gap_2pow804
      (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804))

/-- Final corrected raw-image no-decider surface. -/
theorem no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HP : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRawImagePSideRankBoundOneZero M htb hns)
    (HInv : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  exact paperScaleCookLevinPiPlusBoolRawImagePSide_and_NPLower_incompatible M htb hns
    (HP hdec) (HInv hdec)
    (paperScaleCookLevinBoolRawImageSourceNPRankLower_of_rawLower_of_kernelDisjoint
      M htb hns (HrawNP hdec) (Hker hdec))

/-! ## Axiom audit anchors -/

#print axioms boolRawImageBlockedSpdpSubspace_le_inc_of_le
#print axioms boolRawImageBlockedSpdpRank_le_rankInc_of_le
#print axioms paperScaleCookLevinPiPlusBoolRawImagePSide_and_NPLower_incompatible
#print axioms no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
