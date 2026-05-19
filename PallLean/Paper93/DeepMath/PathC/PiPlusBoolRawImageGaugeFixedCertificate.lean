import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageSameListDerivativeCertificate

/-!
# Gauge-fixed certificates for same-list raw-image derivative transport

The same-list derivative seam asks for every admissible derivative row to be
preserved by `Pi+`.  A still stronger, very concrete surface is that the whole
polynomial is fixed by the gauge:

`Pi+ q = q`.

This file packages that reduction.  Polynomial fixedness immediately gives
same-list derivative preservation, and it also gives the inverse same-list
certificate at the post-gauge polynomial because the inverse sends `Pi+ q` back
to `q`, which is the same polynomial under fixedness.
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

/-- Gauge-fixed certificate for a polynomial: the `Pi+` transform leaves `q`
unchanged. -/
def PiPlusRawRowGaugeFixedCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  piP.gauge q = q

/-- If the polynomial is fixed by `Pi+`, all same-list derivative rows are fixed. -/
theorem piPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfixed : PiPlusRawRowGaugeFixedCertificate piP q) :
    PiPlusRawRowSameListDerivativePreservationCertificate piP κ q := by
  intro S _ _
  unfold PiPlusRawRowGaugeFixedCertificate at hfixed
  rw [hfixed]

/-- Gauge fixedness for `q` also gives same-list derivative preservation for the
inverse transform at the post-gauge polynomial `Pi+ q`. -/
theorem piPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfixed : PiPlusRawRowGaugeFixedCertificate piP q) :
    PiPlusRawRowSameListDerivativePreservationCertificate
      (piPlusSATTransformInverse piP) κ (piP.gauge q) := by
  intro S _ _
  unfold PiPlusRawRowGaugeFixedCertificate at hfixed
  rw [piPlusSATTransformInverse_gauge_gauge piP q]
  rw [hfixed]

/-- Gauge fixedness implies corrected raw-image rank invariance through the
same-list derivative seam. -/
theorem piPlusBoolRawImageRankInvariant_of_gaugeFixed
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfixed : PiPlusRawRowGaugeFixedCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
    piP κ ℓ q
    (piPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
      piP κ q hfixed)
    (piPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
      piP κ q hfixed)

/-- Paper-scale fixedness certificate for the concrete `Pi+` at the compiled
Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGaugeFixedCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale gauge fixedness gives same-list derivative preservation for the
concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfixed : PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate M htb hns :=
  piPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hfixed

/-- Paper-scale gauge fixedness gives same-list derivative preservation for the
inverse concrete `Pi+` at the post-gauge compiled polynomial. -/
theorem paperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfixed : PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns) :
    PaperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate M htb hns :=
  piPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hfixed

/-- Paper-scale gauge fixedness implies corrected raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_gaugeFixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfixed : PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
    M htb hns
    (paperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
      M htb hns hfixed)
    (paperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
      M htb hns hfixed)

/-- No-decider surface using the strongest fixed-polynomial certificate for the
concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_gaugeFixedAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hfixed : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_sameListDerivativesInverseAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
        M htb hns (Hfixed hdec))
    (fun hdec =>
      paperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
        M htb hns (Hfixed hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
#print axioms piPlusInverseRawRowSameListDerivativePreservationCertificate_of_gaugeFixed
#print axioms piPlusBoolRawImageRankInvariant_of_gaugeFixed
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_gaugeFixed
#print axioms no_decidesSAT_at_paperScale_of_gaugeFixedAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
