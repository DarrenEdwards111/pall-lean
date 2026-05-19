import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageDerivativeFactorCertificate

/-!
# Exact derivative-identity certificates for raw-image row transport

The derivative-factor seam allows a transported derivative row to be a multiplier
factor times a source derivative row.  This file peels to the cleaner exact
identity surface: the transported derivative row is itself a source derivative
row.

This is the algebraic target expected from a genuinely row-permuting/block-local
basis change: exhibit the source derivative list `S'` with the same window and
prove

`iterDerivList S (Pi+ q) = iterDerivList S' q`.

The previous factor certificate follows by taking the extra factor to be `1`.
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

/-- Exact derivative-identity certificate for one-sided raw-row generator
preservation.  Compared with the derivative-factor certificate, this fixes the
factor to `1`; the existing row multiplier `m` therefore remains within its
original budget. -/
def PiPlusRawRowDerivativeIdentityPreservationCertificate
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
    ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      S'.length = κ ∧
        m.totalDegree ≤ ℓ ∧
          m.vars ⊆ S'.toFinset ∧
            isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S' ∧
              iterDerivList S (piP.gauge q) = iterDerivList S' q

/-- Exact derivative identities imply derivative-factor certificates by taking
`r = 1`. -/
theorem piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hident : PiPlusRawRowDerivativeIdentityPreservationCertificate piP κ ℓ q) :
    PiPlusRawRowDerivativeFactorPreservationCertificate piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hident S m hlen hdeg hvars hadm with
    ⟨S', hlen', hdeg', hvars', hadm', hrow⟩
  refine ⟨S', 1, hlen', ?_, ?_, hadm', ?_⟩
  · simpa using hdeg'
  · simpa using hvars'
  · simpa using hrow

/-- One-sided exact derivative identities for `Pi+` and its inverse imply
corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowDerivativeIdentityPreservationCertificate piP κ ℓ q)
    (hinv : PiPlusRawRowDerivativeIdentityPreservationCertificate
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q)) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
    piP κ ℓ q
    (piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
      piP κ ℓ q hpres)
    (piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q) hinv)

/-- Paper-scale exact derivative-identity certificate for the concrete `Pi+`. -/
def PaperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeIdentityPreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale exact derivative-identity certificate for the inverse concrete
`Pi+`, at the post-gauge compiled polynomial. -/
def PaperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeIdentityPreservationCertificate
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- Paper-scale exact derivative identities imply derivative-factor preservation
for the concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hident : PaperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hident

/-- Paper-scale exact derivative identities imply derivative-factor preservation
for the inverse concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hident : PaperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    hident

/-- Paper-scale exact derivative identities for `Pi+` and its inverse imply
corrected raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate M htb hns)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeFactors_and_inverseDerivativeFactors
    M htb hns
    (paperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
      M htb hns hpres)
    (paperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
      M htb hns hinv)

/-- No-decider surface using exact derivative identities for `Pi+` and its
inverse. -/
theorem no_decidesSAT_at_paperScale_of_derivativeIdentitiesInverseAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate M htb hns)
    (Hinv : DecidesSAT M →
      PaperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_derivativeFactorsInverseAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
        M htb hns (Hpres hdec))
    (fun hdec =>
      paperScaleCookLevinPiPlusInverseRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
        M htb hns (Hinv hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowDerivativeFactorPreservationCertificate_of_derivativeIdentity
#print axioms piPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
#print axioms no_decidesSAT_at_paperScale_of_derivativeIdentitiesInverseAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
