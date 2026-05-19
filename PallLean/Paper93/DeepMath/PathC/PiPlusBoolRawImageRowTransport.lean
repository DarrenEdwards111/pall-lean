import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImagePSideTransport

/-!
# Row-preservation transport for the corrected raw-image Boolean surface

The corrected NP side uses raw ordinary derivative rows mapped into `BoolPoly`.
This file packages the matching `Pi+` rank-invariance seam as an explicit
row-space preservation statement on that corrected raw-image row span.
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

/-- Corrected raw-image row preservation for a full-ring `Pi+` gauge at one
strict SPDP window.  It says that the Boolean images of raw derivative rows of
`gauge q` lie in the Boolean images of raw derivative rows of `q`. -/
def PiPlusBoolRawImageRowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  boolRawImageBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) ≤
    boolRawImageBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q

/-- Reverse corrected raw-image row preservation.  Exact rank invariance needs
both inclusions; this keeps the mathematical seam honest. -/
def PiPlusBoolRawImageRowReflection
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  boolRawImageBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q ≤
    boolRawImageBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q)

/-- Two-sided corrected raw-image row preservation implies corrected raw-image
rank invariance for the same strict window. -/
theorem piPlusBoolRawImageRankInvariant_of_rowEquivalence
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusBoolRawImageRowPreservation piP κ ℓ q)
    (hreflect : PiPlusBoolRawImageRowReflection piP κ ℓ q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q := by
  unfold boolRawImageBlockedSpdpRank
  apply le_antisymm
  · exact Submodule.finrank_mono hpres
  · exact Submodule.finrank_mono hreflect

/-- Paper-scale corrected raw-image row preservation at the NP window. -/
def PaperScaleCookLevinPiPlusBoolRawImageRowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRawImageRowPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale corrected raw-image row reflection at the NP window. -/
def PaperScaleCookLevinPiPlusBoolRawImageRowReflection
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRawImageRowReflection
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale row equivalence gives the corrected raw-image rank-invariance
payload consumed by the final contradiction bridge. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rowEquivalence
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusBoolRawImageRowPreservation M htb hns)
    (hreflect : PaperScaleCookLevinPiPlusBoolRawImageRowReflection M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolRawImageRankInvariant
  exact piPlusBoolRawImageRankInvariant_of_rowEquivalence
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hpres hreflect

/-- No-decider surface where the corrected raw-image rank-invariance payload is
reduced to two explicit row-space inclusions. -/
theorem no_decidesSAT_at_paperScale_of_boolRawImageRowsAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRawImageRowPreservation M htb hns)
    (Hreflect : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRawImageRowReflection M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRawImagePayloadsFromLegacyPostGaugePBound
    M htb hns HPlegacy
  · intro hdec
    exact paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rowEquivalence
      M htb hns (Hpres hdec) (Hreflect hdec)
  · exact HrawNP
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusBoolRawImageRankInvariant_of_rowEquivalence
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rowEquivalence
#print axioms no_decidesSAT_at_paperScale_of_boolRawImageRowsAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
