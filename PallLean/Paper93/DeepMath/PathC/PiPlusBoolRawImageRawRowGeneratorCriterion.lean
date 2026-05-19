import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRawRowEquivalence

/-!
# Generator criterion for raw-row Pi+ transport

The previous seam reduced corrected raw-image rank invariance to raw full-ring
row preservation/reflection.  Since raw row spaces are spans of explicit
SPDP derivative/shift generators, it is enough to check each generator.

This file packages that generator-level endpoint, both generally and at
paper scale.
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

/-- Generator-level raw-row preservation for a concrete `Pi+` gauge at one
strict SPDP window.  Every raw generator of `gauge q` is required to lie in the
raw row span of `q`. -/
def PiPlusRawRowGeneratorPreservation
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
    m * iterDerivList S (piP.gauge q) ∈
      rawBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q

/-- Generator-level raw-row reflection for a concrete `Pi+` gauge at one strict
SPDP window.  Every raw generator of `q` is required to lie in the raw row span
of `gauge q`. -/
def PiPlusRawRowGeneratorReflection
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
    m * iterDerivList S q ∈
      rawBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q)

/-- Generator-level preservation implies raw-row preservation. -/
theorem piPlusRawRowPreservation_of_generatorPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hgen : PiPlusRawRowGeneratorPreservation piP κ ℓ q) :
    PiPlusRawRowPreservation piP κ ℓ q := by
  unfold PiPlusRawRowPreservation rawBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro r hr
  rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact hgen S m hlen hdeg hvars hadm

/-- Generator-level reflection implies raw-row reflection. -/
theorem piPlusRawRowReflection_of_generatorReflection
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hgen : PiPlusRawRowGeneratorReflection piP κ ℓ q) :
    PiPlusRawRowReflection piP κ ℓ q := by
  unfold PiPlusRawRowReflection rawBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro r hr
  rcases hr with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact hgen S m hlen hdeg hvars hadm

/-- Generator-level raw-row equivalence implies corrected raw-image Boolean rank
invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowGeneratorPreservation piP κ ℓ q)
    (hreflect : PiPlusRawRowGeneratorReflection piP κ ℓ q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_rawRowEquivalence piP κ ℓ q
    (piPlusRawRowPreservation_of_generatorPreservation piP κ ℓ q hpres)
    (piPlusRawRowReflection_of_generatorReflection piP κ ℓ q hreflect)

/-- Paper-scale generator preservation at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowGeneratorPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGeneratorPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale generator reflection at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowGeneratorReflection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGeneratorReflection
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale generator preservation implies raw-row preservation. -/
theorem paperScaleCookLevinPiPlusRawRowPreservation_of_generatorPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hgen : PaperScaleCookLevinPiPlusRawRowGeneratorPreservation M htb hns) :
    PaperScaleCookLevinPiPlusRawRowPreservation M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowPreservation
  exact piPlusRawRowPreservation_of_generatorPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hgen

/-- Paper-scale generator reflection implies raw-row reflection. -/
theorem paperScaleCookLevinPiPlusRawRowReflection_of_generatorReflection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hgen : PaperScaleCookLevinPiPlusRawRowGeneratorReflection M htb hns) :
    PaperScaleCookLevinPiPlusRawRowReflection M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowReflection
  exact piPlusRawRowReflection_of_generatorReflection
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hgen

/-- Paper-scale generator equivalence gives the corrected raw-image rank
invariance payload. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowGeneratorPreservation M htb hns)
    (hreflect : PaperScaleCookLevinPiPlusRawRowGeneratorReflection M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowEquivalence
    M htb hns
    (paperScaleCookLevinPiPlusRawRowPreservation_of_generatorPreservation
      M htb hns hpres)
    (paperScaleCookLevinPiPlusRawRowReflection_of_generatorReflection
      M htb hns hreflect)

/-- No-decider surface where the corrected raw-image rank-invariance payload is
reduced to explicit generator preservation/reflection checks. -/
theorem no_decidesSAT_at_paperScale_of_rawRowGeneratorsAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M → PaperScaleCookLevinPiPlusRawRowGeneratorPreservation M htb hns)
    (Hreflect : DecidesSAT M → PaperScaleCookLevinPiPlusRawRowGeneratorReflection M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  exact no_decidesSAT_at_paperScale_of_rawRowsAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec => paperScaleCookLevinPiPlusRawRowPreservation_of_generatorPreservation
      M htb hns (Hpres hdec))
    (fun hdec => paperScaleCookLevinPiPlusRawRowReflection_of_generatorReflection
      M htb hns (Hreflect hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowPreservation_of_generatorPreservation
#print axioms piPlusRawRowReflection_of_generatorReflection
#print axioms piPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence
#print axioms no_decidesSAT_at_paperScale_of_rawRowGeneratorsAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
