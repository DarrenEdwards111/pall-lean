import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageBlockCoordinateCombinationCertificate

/-!
# Coordinate-renamed fixed-combination certificates for raw-image gauge fixedness

The block-coordinate fixed-combination seam asked each listed SAT-side piece to
be fixed by the conjugated SAT-scale block algebra equivalence.  This file peels
that one step closer to the actual coordinate calculation: rename each piece into
`blockIndex × Bool` coordinates and prove it is fixed by the raw block-local
Hadamard algebra equivalence there.

The SAT-scale fixedness then follows by conjugating through
`MvPolynomial.renameEquiv`.
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

/-- Coordinate-renamed fixed-combination certificate.  The finite decomposition
is still on the SAT variable ring, but each piece is certified fixed only after
renaming to the explicit `blockIndex × Bool` coordinate ring. -/
def PiPlusRawRowCoordinateRenamedFixedCombinationCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : SATDeciderGaugeSpace M n hn2 htb hns) : Prop :=
  ∃ (F : Finset (SATDeciderGaugeSpace M n hn2 htb hns))
    (c : SATDeciderGaugeSpace M n hn2 htb hns → ℚ),
    q = F.sum (fun g => c g • g) ∧
      ∀ g ∈ F,
        blockPiPlusAlgEquiv D.blockIndex (MvPolynomial.renameEquiv ℚ D.coord g) =
          MvPolynomial.renameEquiv ℚ D.coord g

/-- If a SAT-side piece is fixed after renaming into block coordinates, then it
is fixed by the conjugated SAT-scale block algebra equivalence. -/
theorem piPlusSATBlockAlgEquiv_fixed_of_coordinateRenamed_fixed
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (g : SATDeciderGaugeSpace M n hn2 htb hns)
    (hfixed : blockPiPlusAlgEquiv D.blockIndex (MvPolynomial.renameEquiv ℚ D.coord g) =
      MvPolynomial.renameEquiv ℚ D.coord g) :
    piPlusSATBlockAlgEquiv M n hn2 htb hns D g = g := by
  have h := congrArg (fun p => (MvPolynomial.renameEquiv ℚ D.coord.symm) p) hfixed
  simpa [piPlusSATBlockAlgEquiv, AlgEquiv.trans_apply] using h

/-- Coordinate-renamed fixed-combination certificates give the previous
block-coordinate fixed-combination certificates. -/
theorem piPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (q : SATDeciderGaugeSpace M n hn2 htb hns)
    (hcoord : PiPlusRawRowCoordinateRenamedFixedCombinationCertificate
      M n hn2 htb hns D q) :
    PiPlusRawRowBlockCoordinateFixedCombinationCertificate M n hn2 htb hns D q := by
  rcases hcoord with ⟨F, c, hsum, hF⟩
  refine ⟨F, c, hsum, ?_⟩
  intro g hg
  exact piPlusSATBlockAlgEquiv_fixed_of_coordinateRenamed_fixed
    M n hn2 htb hns D g (hF g hg)

/-- Coordinate-renamed fixed-combination certificates imply corrected raw-image
rank invariance for the coordinate-built `Pi+` transform. -/
theorem piPlusBoolRawImageRankInvariant_of_coordinateRenamedFixedCombination
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : SATDeciderGaugeSpace M n hn2 htb hns)
    (hcoord : PiPlusRawRowCoordinateRenamedFixedCombinationCertificate
      M n hn2 htb hns D q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        ((piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
    M n hn2 htb hns D κ ℓ q
    (piPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
      M n hn2 htb hns D q hcoord)

/-- Paper-scale coordinate-renamed fixed-combination certificate for the concrete
Cook--Levin block coordinates. -/
def PaperScaleCookLevinPiPlusRawRowCoordinateRenamedFixedCombinationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowCoordinateRenamedFixedCombinationCertificate
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale coordinate-renamed fixed-combination certificates give the
block-coordinate fixed-combination certificate. -/
theorem paperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcoord : PaperScaleCookLevinPiPlusRawRowCoordinateRenamedFixedCombinationCertificate
      M htb hns) :
    PaperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate M htb hns :=
  piPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hcoord

/-- Paper-scale coordinate-renamed fixed-combination certificates imply corrected
raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_coordinateRenamedFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcoord : PaperScaleCookLevinPiPlusRawRowCoordinateRenamedFixedCombinationCertificate
      M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_blockCoordinateFixedCombination
    M htb hns
    (paperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
      M htb hns hcoord)

/-- No-decider surface using coordinate-renamed fixed-combination decomposition
for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_coordinateRenamedFixedCombinationAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hcoord : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowCoordinateRenamedFixedCombinationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_blockCoordinateFixedCombinationAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
        M htb hns (Hcoord hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusSATBlockAlgEquiv_fixed_of_coordinateRenamed_fixed
#print axioms piPlusRawRowBlockCoordinateFixedCombinationCertificate_of_coordinateRenamed
#print axioms piPlusBoolRawImageRankInvariant_of_coordinateRenamedFixedCombination
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_coordinateRenamedFixedCombination
#print axioms no_decidesSAT_at_paperScale_of_coordinateRenamedFixedCombinationAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
