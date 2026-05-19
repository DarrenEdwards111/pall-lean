import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNormalizedAgreementReduction

/-!
# Reducing Boolean-ambient respect to normalized-input compatibility

`PiPlusRespectsBooleanAmbient` is the quotient-descent obligation for the raw
full-ring `Pi+` gauge.  This file peels it to a simpler normal-form socket:
applying the gauge after Boolean-normalizing the input is Boolean-equivalent to
applying the gauge to the raw input.

This is the right next payload because Boolean equivalence is equality of normal
forms.  A map descends to the Boolean quotient once it is insensitive, up to
`≈ᵦ`, to replacing an input by its Boolean normal representative.
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

/-- A full-ring map is compatible with Boolean normalization of its input if
normalizing before applying the map gives a Boolean-equivalent output. -/
def NormalizedInputCompatible {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ p : MvPolynomial (Fin n) ℚ, F (zeroProfileBooleanNormalize p) ≈ᵦ F p

/-- Normalized-input compatibility is enough for quotient descent: if two inputs
have the same Boolean normal form, their images have the same Boolean normal
form. -/
theorem respectsBooleanAmbient_of_normalizedInputCompatible {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ)
    (hcompat : NormalizedInputCompatible F) :
    RespectsBooleanAmbient F := by
  intro p q hpq
  exact booleanAmbientEq_trans
    (booleanAmbientEq_symm (hcompat p))
    (booleanAmbientEq_trans
      (booleanAmbientEq_of_eq (congrArg F hpq))
      (hcompat q))

/-- Specialized normalized-input compatibility for a concrete `Pi+` transform. -/
def PiPlusNormalizedInputCompatible
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  NormalizedInputCompatible (n := (cook_levin_compilation M n hn2 htb hns).numVars)
    piP.gauge

/-- Normalized-input compatibility discharges `PiPlusRespectsBooleanAmbient`. -/
theorem piPlusRespectsBooleanAmbient_of_normalizedInputCompatible
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hcompat : PiPlusNormalizedInputCompatible piP) :
    PiPlusRespectsBooleanAmbient piP :=
  respectsBooleanAmbient_of_normalizedInputCompatible piP.gauge hcompat

/-- Paper-scale normalized-input compatibility for the concrete Cook--Levin
`Pi+` gauge. -/
def PaperScaleCookLevinPiPlusNormalizedInputCompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusNormalizedInputCompatible (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale normalized-input compatibility discharges the paper-scale
Boolean-ambient respect obligation. -/
theorem paperScaleCookLevinPiPlusRespectsBooleanAmbient_of_normalizedInputCompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcompat : PaperScaleCookLevinPiPlusNormalizedInputCompatible M htb hns) :
    PiPlusRespectsBooleanAmbient (cookLevinPiPlusSATTransform_paperScale M htb hns) :=
  piPlusRespectsBooleanAmbient_of_normalizedInputCompatible
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hcompat

/-- The identity-minor seam can now consume normalized-input compatibility
instead of the more abstract Boolean-ambient respect predicate. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_rawCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hcompat : DecidesSAT M → PaperScaleCookLevinPiPlusNormalizedInputCompatible M htb hns)
    (hraw : DecidesSAT M → PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_respects_of_rawCompiledAgreement
    M htb hns hsource
    (fun hdec =>
      paperScaleCookLevinPiPlusRespectsBooleanAmbient_of_normalizedInputCompatible
        M htb hns (hcompat hdec))
    hraw

/-! ## Axiom audit anchors -/

#print axioms respectsBooleanAmbient_of_normalizedInputCompatible
#print axioms piPlusRespectsBooleanAmbient_of_normalizedInputCompatible
#print axioms paperScaleCookLevinPiPlusRespectsBooleanAmbient_of_normalizedInputCompatible
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_rawCompiledAgreement

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
