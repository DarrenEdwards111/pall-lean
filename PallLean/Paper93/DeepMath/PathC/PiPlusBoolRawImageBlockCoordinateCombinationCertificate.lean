import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImagePointwiseFixedCombinationCertificate
import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteTransformLemmas

/-!
# Block-coordinate fixed-combination certificates for raw-image gauge fixedness

The pointwise fixed-combination seam states fixedness using the abstract
`PiPlusSATTransform.gauge`.  For the concrete Cook--Levin `Pi+`, that gauge is
just the linear shadow of the block-coordinate algebra equivalence.

This file exposes the next coordinate-level target: list fixed pieces by proving
that the concrete block algebra equivalence fixes them.  The abstract pointwise
certificate follows by the existing definitional bridge
`piPlusSATTransform_of_blockCoordinates_gauge_apply`.
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

/-- Coordinate-level pointwise fixed finite-combination certificate: exhibit an
explicit finite decomposition whose pieces are fixed by the concrete
`piPlusSATBlockAlgEquiv` built from block coordinates. -/
def PiPlusRawRowBlockCoordinateFixedCombinationCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  ∃ (F : Finset (SATDeciderGaugeSpace M n hn2 htb hns))
    (c : SATDeciderGaugeSpace M n hn2 htb hns → ℚ),
    q = F.sum (fun g => c g • g) ∧
      ∀ g ∈ F, piPlusSATBlockAlgEquiv M n hn2 htb hns D g = g

/-- Coordinate-level fixed-combination certificates give abstract pointwise
fixed-combination certificates for the coordinate-built `Pi+` transform. -/
theorem piPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : SATDeciderGaugeSpace M n hn2 htb hns)
    (hcoord : PiPlusRawRowBlockCoordinateFixedCombinationCertificate
      M n hn2 htb hns D q) :
    PiPlusRawRowPointwiseFixedCombinationCertificate
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) q := by
  rcases hcoord with ⟨F, c, hsum, hF⟩
  refine ⟨F, c, hsum, ?_⟩
  intro g hg
  rw [piPlusSATTransform_of_blockCoordinates_gauge_apply]
  exact hF g hg

/-- Coordinate-level fixed combinations imply corrected raw-image rank invariance
for the coordinate-built `Pi+` transform. -/
theorem piPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : SATDeciderGaugeSpace M n hn2 htb hns)
    (hcoord : PiPlusRawRowBlockCoordinateFixedCombinationCertificate
      M n hn2 htb hns D q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        ((piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) κ ℓ q
    (piPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
      M n hn2 htb hns D q hcoord)

/-- Paper-scale coordinate-level pointwise fixed finite-combination certificate
for the concrete Cook--Levin block coordinates. -/
def PaperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowBlockCoordinateFixedCombinationCertificate
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale coordinate-level fixed-combination certificates give the abstract
pointwise fixed-combination certificate for `cookLevinPiPlusSATTransform_paperScale`. -/
theorem paperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcoord : PaperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate
      M htb hns) :
    PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate
  exact piPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hcoord

/-- Paper-scale coordinate-level fixed-combination certificates imply corrected
raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcoord : PaperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate
      M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
    M htb hns
    (paperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
      M htb hns hcoord)

/-- No-decider surface using block-coordinate fixed-combination decomposition
for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_blockCoordinateFixedCombinationAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hcoord : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_pointwiseFixedCombinationAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
        M htb hns (Hcoord hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowPointwiseFixedCombinationCertificate_of_blockCoordinateFixedCombination
#print axioms piPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
#print axioms no_decidesSAT_at_paperScale_of_blockCoordinateFixedCombinationAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
