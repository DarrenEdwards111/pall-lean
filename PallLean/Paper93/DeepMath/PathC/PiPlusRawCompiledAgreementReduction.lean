import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanRespectReduction
import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteTransformLemmas

/-!
# Reducing raw compiled agreement to Boolean-projected compiled fixedness

The previous seams reduced Boolean-normalized identity-minor preservation to two
local obligations:

* the raw `Pi+` gauge respects the Boolean quotient, and
* raw `Pi+` preserves the compiled polynomial in the Boolean ambient.

This file peels the second obligation to the paper-faithful projected surface:
`zeroProfileBooleanNormalize (Pi+(compiledPoly)) = zeroProfileBooleanNormalize
compiledPoly`.  This is exactly the fixedness statement for the Boolean-projected
`Pi+ᵦ` action on the compiled polynomial, without returning to false raw
fixedness.
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

/-- Boolean-projected fixedness of the paper-scale compiled polynomial:
`Pi+ᵦ(compiledPoly)` has the same Boolean normal representative as
`compiledPoly`. -/
def PaperScaleCookLevinPiPlusBooleanProjectedCompiledFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  zeroProfileBooleanNormalize
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) =
    zeroProfileBooleanNormalize
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Boolean-projected compiled fixedness discharges raw compiled agreement in
the Boolean ambient. -/
theorem paperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement_of_booleanProjectedCompiledFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfixed : PaperScaleCookLevinPiPlusBooleanProjectedCompiledFixed M htb hns) :
    PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns :=
  hfixed

/-- Identity-minor bridge consuming Boolean-projected compiled fixedness instead
of the lower-level raw compiled Boolean-ambient agreement. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_booleanProjectedCompiledFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hcompat : DecidesSAT M → PaperScaleCookLevinPiPlusNormalizedInputCompatible M htb hns)
    (hfixed : DecidesSAT M → PaperScaleCookLevinPiPlusBooleanProjectedCompiledFixed M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_rawCompiledAgreement
    M htb hns hsource hcompat
    (fun hdec =>
      paperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement_of_booleanProjectedCompiledFixed
        M htb hns (hfixed hdec))

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement_of_booleanProjectedCompiledFixed
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_booleanProjectedCompiledFixed

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
