import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNormalizedIdentityMinor

/-!
# Reducing Boolean-normalized compiled agreement to Boolean ambient equality

The previous seam named the identity-minor payload as equality in `BoolPoly`:
the Boolean-normalized post-`Pi+` compiled polynomial equals the source Boolean
compiled representative.

This file peels that payload down to the raw paper-ambient equality
`≈ᵦ`, i.e. equality after Boolean normalization.  This is the direct formal
version of Lemma 66 / Remark 21: what matters is the Boolean normal
representative, not raw polynomial equality.
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

/-- Raw Boolean-ambient compiled agreement for the already-normalized source
representative: applying raw `Pi+` to the Boolean representative of the compiled
polynomial gives a polynomial Boolean-equivalent to the original compiled
polynomial. -/
def PaperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  (cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      ((paperScaleCompiledBoolPoly M htb hns) :
        SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) ≈ᵦ
    compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)

/-- The raw Boolean-ambient agreement socket is exactly enough to close the
`BoolPoly` compiled-agreement socket. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_rawBooleanAmbientAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hagree : PaperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement M htb hns := by
  apply BoolPoly.ext
  unfold PaperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement at hagree
  unfold paperScalePiPlusBoolNormalizedCompiled paperScaleCompiledBoolSource
  change zeroProfileBooleanNormalize
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        ((paperScaleCompiledBoolPoly M htb hns) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) =
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
  exact hagree

/-- Even more concrete raw agreement: raw `Pi+` applied directly to the raw
compiled polynomial is Boolean-equivalent to the compiled polynomial.  To use
this against the paper source representative, the raw gauge must respect the
Boolean ambient. -/
def PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  (cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) ≈ᵦ
    compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)

/-- If the concrete raw `Pi+` gauge respects Boolean equivalence, then raw
compiled agreement implies agreement for the normalized source representative. -/
theorem paperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement_of_respects_of_rawCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrespect : PiPlusRespectsBooleanAmbient
      (cookLevinPiPlusSATTransform_paperScale M htb hns))
    (hraw : PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns) :
    PaperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement
    PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement at *
  exact booleanAmbientEq_trans
    (hrespect (p :=
      ((paperScaleCompiledBoolPoly M htb hns) :
        SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns))
      (q := compiledPoly
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
      (by
        change zeroProfileBooleanNormalize
            ((paperScaleCompiledBoolPoly M htb hns) :
              SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) =
          zeroProfileBooleanNormalize
            (compiledPoly
              (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
        exact normalize_idempotent_apply
          (compiledPoly
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))))
    hraw

/-- Raw compiled Boolean-ambient agreement plus respect for the Boolean quotient
closes the `BoolPoly` compiled-agreement socket. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_respects_of_rawCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrespect : PiPlusRespectsBooleanAmbient
      (cookLevinPiPlusSATTransform_paperScale M htb hns))
    (hraw : PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_rawBooleanAmbientAgreement
    M htb hns
    (paperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement_of_respects_of_rawCompiledAgreement
      M htb hns hrespect hraw)

/-- Full identity-minor bridge from source lower, Boolean-respect, and raw
Boolean-ambient compiled agreement. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_respects_of_rawCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hrespect : DecidesSAT M → PiPlusRespectsBooleanAmbient
      (cookLevinPiPlusSATTransform_paperScale M htb hns))
    (hraw : DecidesSAT M → PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_compiledAgreement
    M htb hns hsource
    (fun hdec =>
      paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_respects_of_rawCompiledAgreement
        M htb hns (hrespect hdec) (hraw hdec))

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_rawBooleanAmbientAgreement
#print axioms paperScaleCookLevinPiPlusRawBooleanAmbientCompiledAgreement_of_respects_of_rawCompiledAgreement
#print axioms paperScaleCookLevinPiPlusBoolNormalizedCompiledAgreement_of_respects_of_rawCompiledAgreement
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_respects_of_rawCompiledAgreement

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
