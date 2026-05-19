import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRawRowCertificate

/-!
# Inverse-gauge bridge for raw-image row reflection

Raw-image rank invariance currently asks for two directions: preservation for
`Pi+`, and reflection back from the source rows into the post-`Pi+` rows.  Since
`Pi+` is an equivalence, the reflection direction is just preservation for the
inverse transform, applied to the post-gauge polynomial.

This file packages that symmetry.  The remaining algebra may now be stated as
one-sided row/certificate preservation for the concrete transform and its
inverse, rather than as a separate bespoke reflection proof.
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

/-- The inverse `Pi+` transform obtained by reversing the underlying linear
equivalence.  The block-local field is just carried as metadata; this file only
uses the linear inverse. -/
noncomputable def piPlusSATTransformInverse
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    PiPlusSATTransform M n hn2 htb hns where
  equiv := piP.equiv.symm
  block_local_hadamard_lift := piP.block_local_hadamard_lift

/-- The inverse transform pulls back the post-gauge polynomial to the source. -/
theorem piPlusSATTransformInverse_gauge_gauge
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) :
    (piPlusSATTransformInverse piP).gauge (piP.gauge q) = q := by
  exact piP.equiv.left_inv q

/-- Raw-row reflection for `piP` is raw-row preservation for the inverse
transform at the post-gauge polynomial. -/
theorem piPlusRawRowReflection_of_inverseRawRowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hinv : PiPlusRawRowPreservation (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    PiPlusRawRowReflection piP κ ℓ q := by
  unfold PiPlusRawRowReflection
  unfold PiPlusRawRowPreservation at hinv
  have hq := piPlusSATTransformInverse_gauge_gauge piP q
  rwa [hq] at hinv

/-- Generator-level reflection for `piP` is generator-level preservation for the
inverse transform at the post-gauge polynomial. -/
theorem piPlusRawRowGeneratorReflection_of_inverseGeneratorPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hinv : PiPlusRawRowGeneratorPreservation
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    PiPlusRawRowGeneratorReflection piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  have h := hinv S m hlen hdeg hvars hadm
  have hq := piPlusSATTransformInverse_gauge_gauge piP q
  rwa [hq] at h

/-- Certificate-level reflection for `piP` is certificate-level preservation for
the inverse transform at the post-gauge polynomial. -/
theorem piPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hinv : PiPlusRawRowGeneratorPreservationCertificate
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    PiPlusRawRowGeneratorReflectionCertificate piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hinv S m hlen hdeg hvars hadm with
    ⟨S', m', hS', hm', hvars', hadm', hrow⟩
  refine ⟨S', m', hS', hm', hvars', hadm', ?_⟩
  have hq := piPlusSATTransformInverse_gauge_gauge piP q
  rwa [hq] at hrow

/-- One-sided certificates for `Pi+` and its inverse imply the corrected
raw-image rank-invariance payload. -/
theorem piPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowGeneratorPreservationCertificate piP κ ℓ q)
    (hinv : PiPlusRawRowGeneratorPreservationCertificate
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_rawRowCertificates piP κ ℓ q hpres
    (piPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
      piP κ ℓ q hinv)

/-- Paper-scale inverse transform for the concrete Cook--Levin `Pi+`. -/
noncomputable abbrev cookLevinPiPlusSATTransformInverse_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PiPlusSATTransform M (2 ^ 804) paperScale_ge_two htb hns :=
  piPlusSATTransformInverse (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale preservation certificate for the inverse transform at the
post-gauge compiled polynomial. -/
def PaperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGeneratorPreservationCertificate
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- Paper-scale inverse preservation certificate supplies the reflection
certificate needed by the two-sided row certificate interface. -/
theorem paperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate
  exact piPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hinv

/-- Paper-scale one-sided preservation certificate for `Pi+` plus one-sided
preservation certificate for the inverse gives corrected raw-image rank
invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowCertificates
    M htb hns hpres
    (paperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
      M htb hns hinv)

/-- No-decider surface using one-sided preservation certificates for the concrete
`Pi+` and its inverse. -/
theorem no_decidesSAT_at_paperScale_of_preservationInverseCertificatesAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns)
    (Hinv : DecidesSAT M →
      PaperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  exact no_decidesSAT_at_paperScale_of_rawRowCertificatesAndLegacyPostGaugePBound
    M htb hns HPlegacy Hpres
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
        M htb hns (Hinv hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusSATTransformInverse_gauge_gauge
#print axioms piPlusRawRowReflection_of_inverseRawRowPreservation
#print axioms piPlusRawRowGeneratorReflection_of_inverseGeneratorPreservation
#print axioms piPlusRawRowGeneratorReflectionCertificate_of_inversePreservationCertificate
#print axioms piPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
#print axioms no_decidesSAT_at_paperScale_of_preservationInverseCertificatesAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
