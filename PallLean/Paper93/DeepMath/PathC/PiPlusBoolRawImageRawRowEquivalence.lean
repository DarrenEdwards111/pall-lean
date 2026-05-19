import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRowTransport

/-!
# Raw-row reduction for corrected raw-image Boolean row transport

`PiPlusBoolRawImageRowTransport` reduced corrected raw-image rank invariance to
row equivalence after mapping raw SPDP rows into the Boolean quotient.  This file
peels off the quotient map: it shows that ordinary full-ring raw-row inclusions
for the post-`Pi+` gauge imply the corrected raw-image Boolean row inclusions.

The remaining algebraic payload is now purely a raw full-ring SPDP row transport
statement; the Boolean quotient contributes only functoriality of `Submodule.map`.
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

/-- Raw full-ring row preservation for a concrete `Pi+` gauge at one strict
SPDP window. -/
def PiPlusRawRowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  rawBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) ≤
    rawBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q

/-- Reverse raw full-ring row preservation. -/
def PiPlusRawRowReflection
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  rawBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q ≤
    rawBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q)

/-- Full-ring raw-row preservation maps functorially to corrected raw-image
Boolean row preservation. -/
theorem piPlusBoolRawImageRowPreservation_of_rawRowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hraw : PiPlusRawRowPreservation piP κ ℓ q) :
    PiPlusBoolRawImageRowPreservation piP κ ℓ q := by
  unfold PiPlusBoolRawImageRowPreservation boolRawImageBlockedSpdpSubspace
  exact Submodule.map_mono hraw

/-- Full-ring raw-row reflection maps functorially to corrected raw-image
Boolean row reflection. -/
theorem piPlusBoolRawImageRowReflection_of_rawRowReflection
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hraw : PiPlusRawRowReflection piP κ ℓ q) :
    PiPlusBoolRawImageRowReflection piP κ ℓ q := by
  unfold PiPlusBoolRawImageRowReflection boolRawImageBlockedSpdpSubspace
  exact Submodule.map_mono hraw

/-- Two-sided raw full-ring row equivalence implies the corrected raw-image
Boolean rank-invariance payload. -/
theorem piPlusBoolRawImageRankInvariant_of_rawRowEquivalence
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowPreservation piP κ ℓ q)
    (hreflect : PiPlusRawRowReflection piP κ ℓ q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_rowEquivalence piP κ ℓ q
    (piPlusBoolRawImageRowPreservation_of_rawRowPreservation piP κ ℓ q hpres)
    (piPlusBoolRawImageRowReflection_of_rawRowReflection piP κ ℓ q hreflect)

/-- Paper-scale raw full-ring row preservation at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale reverse raw full-ring row preservation at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowReflection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowReflection
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale raw full-ring row preservation implies corrected raw-image row
preservation. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRowPreservation_of_rawRowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : PaperScaleCookLevinPiPlusRawRowPreservation M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRowPreservation M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolRawImageRowPreservation
  exact piPlusBoolRawImageRowPreservation_of_rawRowPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hraw

/-- Paper-scale raw full-ring row reflection implies corrected raw-image row
reflection. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRowReflection_of_rawRowReflection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : PaperScaleCookLevinPiPlusRawRowReflection M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRowReflection M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolRawImageRowReflection
  exact piPlusBoolRawImageRowReflection_of_rawRowReflection
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hraw

/-- Paper-scale raw full-ring row equivalence gives the corrected raw-image
rank-invariance payload. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowEquivalence
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowPreservation M htb hns)
    (hreflect : PaperScaleCookLevinPiPlusRawRowReflection M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns := by
  exact paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rowEquivalence
    M htb hns
    (paperScaleCookLevinPiPlusBoolRawImageRowPreservation_of_rawRowPreservation
      M htb hns hpres)
    (paperScaleCookLevinPiPlusBoolRawImageRowReflection_of_rawRowReflection
      M htb hns hreflect)

/-- No-decider surface where the corrected raw-image rank-invariance payload is
reduced all the way to raw full-ring row preservation/reflection. -/
theorem no_decidesSAT_at_paperScale_of_rawRowsAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M → PaperScaleCookLevinPiPlusRawRowPreservation M htb hns)
    (Hreflect : DecidesSAT M → PaperScaleCookLevinPiPlusRawRowReflection M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  exact no_decidesSAT_at_paperScale_of_boolRawImageRowsAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec => paperScaleCookLevinPiPlusBoolRawImageRowPreservation_of_rawRowPreservation
      M htb hns (Hpres hdec))
    (fun hdec => paperScaleCookLevinPiPlusBoolRawImageRowReflection_of_rawRowReflection
      M htb hns (Hreflect hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusBoolRawImageRowPreservation_of_rawRowPreservation
#print axioms piPlusBoolRawImageRowReflection_of_rawRowReflection
#print axioms piPlusBoolRawImageRankInvariant_of_rawRowEquivalence
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowEquivalence
#print axioms no_decidesSAT_at_paperScale_of_rawRowsAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
