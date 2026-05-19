import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageInverseRowBridge

/-!
# Derivative-factor certificates for raw-image row transport

The previous seam reduced corrected raw-image rank invariance to exact raw row
certificates.  This file peels one more algebraic layer: instead of certifying
an equality after multiplying by the SPDP row multiplier `m`, it is enough to
certify a factorization of the derivative row itself.

For every admissible derivative row of `Pi+ q`, we exhibit an admissible source
derivative row of `q` and a multiplier `r` such that

`iterDerivList S (Pi+ q) = r * iterDerivList S' q`,

with explicit budget checks showing the combined multiplier `m * r` still lies
inside the same `(κ, ℓ)` SPDP row window.  This is closer to the concrete
Leibniz/allocation algebra: prove derivative-factor transport, and exact row
certificates follow automatically.
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

/-- Derivative-factor certificate for one-sided raw-row generator preservation.
For each admissible derivative row of `gauge q`, exhibit a source derivative row
of `q` and a multiplier factor `r`; the side conditions assert that after
absorbing `r` into the incoming row multiplier `m`, the resulting row still fits
the same SPDP generator budget. -/
def PiPlusRawRowDerivativeFactorPreservationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
    ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (r : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S'.length = κ ∧
        (m * r).totalDegree ≤ ℓ ∧
          (m * r).vars ⊆ S'.toFinset ∧
            isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S' ∧
              iterDerivList S (piP.gauge q) = r * iterDerivList S' q

/-- Derivative-factor certificates imply exact raw row certificates by absorbing
`r` into the row multiplier. -/
theorem piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfactor : PiPlusRawRowDerivativeFactorPreservationCertificate piP κ ℓ q) :
    PiPlusRawRowGeneratorPreservationCertificate piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hfactor S m hlen hdeg hvars hadm with
    ⟨S', r, hlen', hdeg', hvars', hadm', hderiv⟩
  refine ⟨S', m * r, hlen', hdeg', hvars', hadm', ?_⟩
  rw [hderiv]
  rw [mul_assoc]

/-- One-sided derivative-factor certificates for `Pi+` and for the inverse
transform imply corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowDerivativeFactorPreservationCertificate piP κ ℓ q)
    (hinv : PiPlusRawRowDerivativeFactorPreservationCertificate
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
    piP κ ℓ q
    (piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
      piP κ ℓ q hpres)
    (piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q) hinv)

/-- Paper-scale derivative-factor certificate for the concrete Cook--Levin
`Pi+`. -/
def PaperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeFactorPreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale derivative-factor certificate for the inverse concrete `Pi+`, at
the post-gauge compiled polynomial. -/
def PaperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeFactorPreservationCertificate
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- Paper-scale derivative-factor preservation gives the exact row-certificate
preservation obligation. -/
theorem paperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactor : PaperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns :=
  piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hfactor

/-- Paper-scale inverse derivative-factor preservation gives the exact inverse
row-certificate preservation obligation. -/
theorem paperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate_of_derivativeFactor
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactor : PaperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate M htb hns :=
  piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    hfactor

/-- Paper-scale derivative-factor certificates for `Pi+` and its inverse imply
corrected raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate M htb hns)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_preservationCertificate_and_inverseCertificate
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
      M htb hns hpres)
    (paperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate_of_derivativeFactor
      M htb hns hinv)

/-- No-decider surface using derivative-factor certificates for `Pi+` and its
inverse. -/
theorem no_decidesSAT_at_paperScale_of_derivativeFactorsInverseAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate M htb hns)
    (Hinv : DecidesSAT M →
      PaperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_preservationInverseCertificatesAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec => paperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
      M htb hns (Hpres hdec))
    (fun hdec => paperScaleCookLevinPiPlusInverseRawRowGeneratorPreservationCertificate_of_derivativeFactor
      M htb hns (Hinv hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowGeneratorPreservationCertificate_of_derivativeFactor
#print axioms piPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
#print axioms no_decidesSAT_at_paperScale_of_derivativeFactorsInverseAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
