import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNormalizedGauge
import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPSideCertificate

/-!
# Boolean-normalized Pi+ identity-minor seam

The paper's NP-side preservation claim is about the Boolean/multilinearized
ambient: after applying `Pi+`, take the Boolean normal representative, and the
identity-minor lower bound is preserved because the multilinear representative
agrees with the Boolean function on `{0,1}^n`.

This file names that exact payload for the `BoolPoly` route.  It does not return
to raw fixedness.  The key mathematical socket is now either:

* a Boolean-normalized NP-window rank nondecrease theorem, or
* the stronger Boolean agreement statement that identifies the normalized
  post-`Pi+` compiled polynomial with the source Boolean representative.

Both are stated in the Boolean ambient and bridged to the existing Route-C
NP-side lower-bound package.
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

/-- Paper-scale source compiled polynomial in the Boolean/multilinear ambient. -/
noncomputable abbrev paperScaleCompiledBoolSource
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars :=
  paperScaleCompiledBoolPoly M htb hns

/-- Paper-scale Boolean-normalized `Pi+` image of the compiled polynomial. -/
noncomputable def paperScalePiPlusBoolNormalizedCompiled
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars :=
  piPlus_bool_normalized (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (paperScaleCompiledBoolSource M htb hns)

@[simp] theorem paperScalePiPlusBoolNormalizedCompiled_eq_piPlusBool
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    paperScalePiPlusBoolNormalizedCompiled M htb hns =
      piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
        (paperScaleCompiledBoolPoly M htb hns) := by
  unfold paperScalePiPlusBoolNormalizedCompiled paperScaleCompiledBoolSource
  exact piPlus_bool_normalized_eq_piPlusBool
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (paperScaleCompiledBoolPoly M htb hns)

/-- Boolean agreement socket for the identity-minor argument: the
Boolean-normalized post-`Pi+` compiled polynomial agrees with the source Boolean
compiled representative.  This is the formal Lemma 66 / Remark 21 style payload,
stated as equality in `BoolPoly`. -/
def PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  paperScalePiPlusBoolNormalizedCompiled M htb hns =
    paperScaleCompiledBoolSource M htb hns

/-- Boolean-normalized NP-window rank nondecrease for the concrete paper-scale
Cook--Levin `Pi+` map. -/
def PaperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScaleCompiledBoolSource M htb hns) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScalePiPlusBoolNormalizedCompiled M htb hns)

/-- The Boolean agreement payload implies NP-window rank nondecrease immediately:
the source and post-`Pi+` Boolean representatives are the same object. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing_of_compiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hagree : PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing
  rw [hagree]

/-- Boolean-normalized post-`Pi+` NP lower bound at the paper-scale NP window. -/
def PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScalePiPlusBoolNormalizedCompiled M htb hns)

/-- Source Boolean NP lower plus Boolean-normalized NP-window nondecrease gives
the post-`Pi+` Boolean-normalized NP lower bound. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_nondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hnondec : PaperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing
      M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinBoolSourceNPLowerBound
    PaperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing
    PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound at *
  exact le_trans hsource hnondec

/-- Source Boolean NP lower plus Boolean agreement gives the post-`Pi+`
Boolean-normalized NP lower bound. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_compiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hagree : PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_nondecreasing
    M htb hns hsource
    (paperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing_of_compiledAgreement
      M htb hns hagree)

/-- Decider-indexed identity-minor preservation for the Boolean-normalized `Pi+`
route.  This is the paper-faithful replacement for raw full-ring identity-minor
preservation. -/
def PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  DecidesSAT M → PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound M htb hns

/-- Decider-indexed source lower plus Boolean agreement gives the
Boolean-normalized identity-minor preservation field. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_compiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hagree : DecidesSAT M →
      PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation M htb hns := by
  intro hdec
  exact paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_compiledAgreement
    M htb hns (hsource hdec) (hagree hdec)

/-- The normalized lower-bound statement is definitionally the existing BoolPoly
post-`Pi+` lower-bound statement, after unfolding the paper-facing name. -/
theorem paperScaleCookLevinPiPlusBoolNPLowerBound_of_boolNormalizedNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlower : PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound M htb hns) :
    PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolNormalizedNPLowerBound at hlower
  unfold PaperScaleCookLevinPiPlusBoolNPLowerBound
  rwa [paperScalePiPlusBoolNormalizedCompiled_eq_piPlusBool] at hlower

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPWindowRankNondecreasing_of_compiledAgreement
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_nondecreasing
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPLowerBound_of_sourceLower_of_compiledAgreement
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_compiledAgreement
#print axioms paperScaleCookLevinPiPlusBoolNPLowerBound_of_boolNormalizedNPLowerBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
