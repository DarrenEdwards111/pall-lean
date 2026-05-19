import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageGaugeFixedSubspaceCertificate

/-!
# Fixed-span certificates for raw-image gauge fixedness

The fixed-subspace seam states that the compiled polynomial lies in
`ker (Pi+ - id)`.  This file peels that linear-algebraic obligation to a
basis/span-style certificate: exhibit a set of fixed generators whose span
contains the compiled polynomial.

This is the natural shape for a concrete coordinate proof: decompose the
Cook--Levin polynomial into local pieces, prove each local piece is fixed by the
block-local `Pi+` action, and conclude fixedness by linearity.
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

/-- Fixed-span certificate: exhibit a set `G` of fixed vectors whose linear span
contains `q`. -/
def PiPlusRawRowGaugeFixedSpanCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∃ G : Set (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    q ∈ Submodule.span ℚ G ∧
      ∀ g ∈ G,
        g ∈ LinearMap.ker
          (piP.gauge -
            (LinearMap.id :
              MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
                MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

/-- A fixed-span certificate gives fixed-subspace membership by monotonicity of
linear span. -/
theorem piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hspan : PiPlusRawRowGaugeFixedSpanCertificate piP q) :
    PiPlusRawRowGaugeFixedSubspaceCertificate piP q := by
  rcases hspan with ⟨G, hq, hG⟩
  unfold PiPlusRawRowGaugeFixedSubspaceCertificate
  exact (Submodule.span_le.mpr hG) hq

/-- Fixed-span certificates imply pointwise gauge fixedness. -/
theorem piPlusRawRowGaugeFixedCertificate_of_fixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hspan : PiPlusRawRowGaugeFixedSpanCertificate piP q) :
    PiPlusRawRowGaugeFixedCertificate piP q :=
  piPlusRawRowGaugeFixedCertificate_of_fixedSubspace piP q
    (piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan piP q hspan)

/-- Fixed-span certificates imply corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_fixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hspan : PiPlusRawRowGaugeFixedSpanCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_fixedSubspace piP κ ℓ q
    (piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan piP q hspan)

/-- Paper-scale fixed-span certificate for the concrete `Pi+` at the compiled
Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGaugeFixedSpanCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale fixed-span certificate gives fixed-subspace membership. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate M htb hns :=
  piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hspan

/-- Paper-scale fixed-span certificate gives pointwise gauge fixedness. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedCertificate_of_fixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedCertificate M htb hns :=
  paperScaleCookLevinPiPlusRawRowGaugeFixedCertificate_of_fixedSubspace
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
      M htb hns hspan)

/-- Paper-scale fixed-span certificate implies corrected raw-image rank
invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hspan : PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSubspace
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
      M htb hns hspan)

/-- No-decider surface using fixed-span decomposition for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_fixedSpanAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hspan : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_fixedSubspaceAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
        M htb hns (Hspan hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
#print axioms piPlusRawRowGaugeFixedCertificate_of_fixedSpan
#print axioms piPlusBoolRawImageRankInvariant_of_fixedSpan
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSpan
#print axioms no_decidesSAT_at_paperScale_of_fixedSpanAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
