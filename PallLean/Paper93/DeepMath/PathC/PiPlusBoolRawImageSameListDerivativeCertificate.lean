import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageDerivativeListCertificate

/-!
# Same-list derivative certificates for raw-image row transport

The derivative-list seam allowed an admissible derivative list `S` for `Pi+ q` to
transport to some admissible source list `S'`.  This file records the strongest
and cleanest local target: the derivative row is preserved on the same list.

For a concrete row-preserving block-local transform, the next algebraic question
can now be phrased as the same-list derivative identity

`iterDerivList S (Pi+ q) = iterDerivList S q`.

The derivative-list transport certificate follows immediately by choosing
`S' = S`.
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

/-- Same-list derivative preservation certificate.  Every admissible derivative
row of `gauge q` is exactly the corresponding derivative row of `q`. -/
def PiPlusRawRowSameListDerivativePreservationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = κ →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      iterDerivList S (piP.gauge q) = iterDerivList S q

/-- Same-list derivative preservation implies derivative-list transport by
choosing the transported list to be `S` itself. -/
theorem piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hsame : PiPlusRawRowSameListDerivativePreservationCertificate piP κ q) :
    PiPlusRawRowDerivativeListPreservationCertificate piP κ q := by
  intro S hlen hadm
  refine ⟨S, hlen, ?_, hadm, hsame S hlen hadm⟩
  exact Finset.Subset.rfl

/-- Same-list derivative preservation for `Pi+` and for its inverse implies
corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowSameListDerivativePreservationCertificate piP κ q)
    (hinv : PiPlusRawRowSameListDerivativePreservationCertificate
      (piPlusSATTransformInverse piP) κ (piP.gauge q)) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
    piP κ ℓ q
    (piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
      piP κ q hpres)
    (piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
      (piPlusSATTransformInverse piP) κ (piP.gauge q) hinv)

/-- Paper-scale same-list derivative certificate for the concrete `Pi+`. -/
def PaperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowSameListDerivativePreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale same-list derivative certificate for the inverse concrete `Pi+`,
at the post-gauge compiled polynomial. -/
def PaperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowSameListDerivativePreservationCertificate
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- Paper-scale same-list derivatives imply derivative-list transport for the
concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsame : PaperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hsame

/-- Paper-scale same-list derivatives imply derivative-list transport for the
inverse concrete `Pi+`. -/
theorem paperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate_of_sameListDerivative
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsame : PaperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate M htb hns :=
  piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
    (cookLevinPiPlusSATTransformInverse_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804))
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
    hsame

/-- Paper-scale same-list derivative preservation for `Pi+` and its inverse
implies corrected raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate M htb hns)
    (hinv : PaperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_derivativeLists_and_inverseDerivativeLists
    M htb hns
    (paperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
      M htb hns hpres)
    (paperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate_of_sameListDerivative
      M htb hns hinv)

/-- No-decider surface using same-list derivative preservation for `Pi+` and its
inverse. -/
theorem no_decidesSAT_at_paperScale_of_sameListDerivativesInverseAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowSameListDerivativePreservationCertificate M htb hns)
    (Hinv : DecidesSAT M →
      PaperScaleCookLevinPiPlusInverseRawRowSameListDerivativePreservationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_derivativeListsInverseAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
        M htb hns (Hpres hdec))
    (fun hdec =>
      paperScaleCookLevinPiPlusInverseRawRowDerivativeListPreservationCertificate_of_sameListDerivative
        M htb hns (Hinv hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowDerivativeListPreservationCertificate_of_sameListDerivative
#print axioms piPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_sameListDerivatives_and_inverseSameListDerivatives
#print axioms no_decidesSAT_at_paperScale_of_sameListDerivativesInverseAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
