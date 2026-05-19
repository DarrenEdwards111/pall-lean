import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageDerivativeIdentityCertificate

/-!
# Derivative-list transport certificates for raw-image row transport

The exact derivative-identity seam still mentions the SPDP row multiplier `m`,
only so its support can be rechecked after choosing the source derivative list.
This file removes that artefact.

It is enough to prove a pure derivative-list transport statement: for every
admissible derivative list `S`, exhibit an admissible source list `S'` with the
same length, with `S.toFinset ⊆ S'.toFinset`, and with the transported derivative
row exactly equal to the source derivative row.  Any multiplier supported on `S`
is then automatically supported on `S'`.
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

/-- Pure derivative-list transport certificate for one-sided raw-row generator
preservation.  This is the multiplier-free form of the exact derivative identity
obligation. -/
def PiPlusRawRowDerivativeListPreservationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = κ →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
    ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      S'.length = κ ∧
        S.toFinset ⊆ S'.toFinset ∧
          isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S' ∧
            iterDerivList S (piP.gauge q) = iterDerivList S' q

/-- Pure derivative-list transport implies exact derivative identities: the
incoming multiplier support transfers along `S.toFinset ⊆ S'.toFinset`. -/
theorem piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hlist : PiPlusRawRowDerivativeListPreservationCertificate piP κ q) :
    PiPlusRawRowDerivativeIdentityPreservationCertificate piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hlist S hlen hadm with ⟨S', hlen', hsub', hadm', hrow⟩
  refine ⟨S', hlen', hdeg, ?_, hadm', hrow⟩
  exact Finset.Subset.trans hvars hsub'

/-- One-sided derivative-list transport for `Pi+` and its inverse implies
corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowDerivativeListPreservationCertificate piP κ q)
    (hinv : PiPlusRawRowDerivativeListPreservationCertificate
      (piPlusSATTransformInverse piP) κ (piP.gauge q)) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
    piP κ ℓ q
    (piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
      piP κ ℓ q hpres)
    (piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
      (piPlusSATTransformInverse piP) κ ℓ (piP.gauge q) hinv)

/-- Paper-scale derivative-list certificate for the concrete `Pi+`. -/
def PaperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeListPreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale derivative-list certificate for the inverse concrete `Pi+`, at
the post-gauge compiled polynomial. -/
def PaperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowDerivativeListPreservationCertificate
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- Paper-scale derivative-list transport gives exact derivative identities for
the concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlist : PaperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hlist

/-- Paper-scale derivative-list transport gives exact derivative identities for
the inverse concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlist : PaperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    hlist

/-- Paper-scale derivative-list transport for `Pi+` and its inverse implies
corrected raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate M htb hns)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeIdentities_and_inverseDerivativeIdentities
    M htb hns
    (paperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
      M htb hns hpres)
    (paperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
      M htb hns hinv)

/-- No-decider surface using pure derivative-list transport for `Pi+` and its
inverse. -/
theorem no_decidesSAT_at_paperScale_of_derivativeListsInverseAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate M htb hns)
    (Hinv : DecidesSAT M →
      PaperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_derivativeIdentitiesInverseAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
        M htb hns (Hpres hdec))
    (fun hdec =>
      paperScaleCookLevinPiPlusInverseRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
        M htb hns (Hinv hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowDerivativeIdentityPreservationCertificate_of_derivativeList
#print axioms piPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
#print axioms no_decidesSAT_at_paperScale_of_derivativeListsInverseAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
