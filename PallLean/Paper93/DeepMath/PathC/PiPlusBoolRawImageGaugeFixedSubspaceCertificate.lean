import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageGaugeFixedCertificate

/-!
# Fixed-subspace certificates for raw-image gauge fixedness

The previous seam used the point equality `Pi+ q = q`.  This file packages the
same obligation in the linear-algebraic form that is normally easier to discharge
from a coordinate calculation: membership in the kernel of `Pi+ - id`.

This exposes the remaining target as a fixed-subspace statement:

`q ∈ ker (Pi+ - id)`.

From that, pointwise gauge fixedness follows by `sub_eq_zero`, and all previous
raw-image rank-invariance/no-decider surfaces follow.
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

/-- Fixed-subspace certificate: `q` lies in the kernel of `Pi+ - id`. -/
def PiPlusRawRowGaugeFixedSubspaceCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  q ∈ LinearMap.ker
    (piP.gauge -
      (LinearMap.id :
        MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

/-- Fixed-subspace membership gives pointwise gauge fixedness. -/
theorem piPlusRawRowGaugeFixedCertificate_of_fixedSubspace
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hker : PiPlusRawRowGaugeFixedSubspaceCertificate piP q) :
    PiPlusRawRowGaugeFixedCertificate piP q := by
  unfold PiPlusRawRowGaugeFixedSubspaceCertificate at hker
  unfold PiPlusRawRowGaugeFixedCertificate
  have h0 := LinearMap.mem_ker.mp hker
  change piP.gauge q - q = 0 at h0
  exact sub_eq_zero.mp h0

/-- Fixed-subspace membership implies corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_fixedSubspace
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hker : PiPlusRawRowGaugeFixedSubspaceCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_gaugeFixed piP κ ℓ q
    (piPlusRawRowGaugeFixedCertificate_of_fixedSubspace piP q hker)

/-- Paper-scale fixed-subspace certificate for the concrete `Pi+` at the
compiled Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGaugeFixedSubspaceCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale fixed-subspace membership gives pointwise gauge fixedness. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedCertificate_of_fixedSubspace
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hker : PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns :=
  piPlusRawRowGaugeFixedCertificate_of_fixedSubspace
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hker

/-- Paper-scale fixed-subspace membership implies corrected raw-image rank
invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSubspace
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hker : PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_gaugeFixed
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGaugeFixedCertificate_of_fixedSubspace
      M htb hns hker)

/-- No-decider surface using fixed-subspace membership for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_fixedSubspaceAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (HkerFixed : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_gaugeFixedAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowGaugeFixedCertificate_of_fixedSubspace
        M htb hns (HkerFixed hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowGaugeFixedCertificate_of_fixedSubspace
#print axioms piPlusBoolRawImageRankInvariant_of_fixedSubspace
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSubspace
#print axioms no_decidesSAT_at_paperScale_of_fixedSubspaceAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
