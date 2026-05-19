import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageGaugeFixedSpanCertificate

/-!
# Finite fixed-family certificates for raw-image gauge fixedness

The fixed-span seam allowed an arbitrary set `G` of fixed vectors.  This file
peels that to the more concrete finite-family form used by local Cook--Levin
coordinate arguments: exhibit a finite set of fixed polynomial pieces whose
span contains the compiled polynomial.

The set-level fixed-span certificate follows by taking `G = ↑F`.
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

/-- Finite fixed-family certificate: exhibit a finite family `F` of fixed vectors
whose linear span contains `q`. -/
def PiPlusRawRowFiniteFixedSpanCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∃ F : Finset (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    q ∈ Submodule.span ℚ (F : Set (MvPolynomial
        (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) ∧
      ∀ g ∈ F,
        g ∈ LinearMap.ker
          (piP.gauge -
            (LinearMap.id :
              MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
                MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

/-- A finite fixed-family certificate gives the set-level fixed-span certificate. -/
theorem piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfinite : PiPlusRawRowFiniteFixedSpanCertificate piP q) :
    PiPlusRawRowGaugeFixedSpanCertificate piP q := by
  rcases hfinite with ⟨F, hq, hF⟩
  refine ⟨(F : Set (MvPolynomial
    (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)), hq, ?_⟩
  intro g hg
  exact hF g hg

/-- Finite fixed-family certificates imply fixed-subspace membership. -/
theorem piPlusRawRowGaugeFixedSubspaceCertificate_of_finiteFixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfinite : PiPlusRawRowFiniteFixedSpanCertificate piP q) :
    PiPlusRawRowGaugeFixedSubspaceCertificate piP q :=
  piPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan piP q
    (piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan piP q hfinite)

/-- Finite fixed-family certificates imply corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_finiteFixedSpan
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfinite : PiPlusRawRowFiniteFixedSpanCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_fixedSpan piP κ ℓ q
    (piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan piP q hfinite)

/-- Paper-scale finite fixed-family certificate for the concrete `Pi+` at the
compiled Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowFiniteFixedSpanCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale finite fixed-family certificate gives fixed-span membership. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfinite : PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns :=
  piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hfinite

/-- Paper-scale finite fixed-family certificate gives fixed-subspace membership. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_finiteFixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfinite : PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate M htb hns :=
  paperScaleCookLevinPiPlusRawRowGaugeFixedSubspaceCertificate_of_fixedSpan
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
      M htb hns hfinite)

/-- Paper-scale finite fixed-family certificate implies corrected raw-image rank
invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfinite : PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_fixedSpan
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
      M htb hns hfinite)

/-- No-decider surface using finite fixed-family decomposition for the concrete
`Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_finiteFixedSpanAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hfinite : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_fixedSpanAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
        M htb hns (Hfinite hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
#print axioms piPlusRawRowGaugeFixedSubspaceCertificate_of_finiteFixedSpan
#print axioms piPlusBoolRawImageRankInvariant_of_finiteFixedSpan
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedSpan
#print axioms no_decidesSAT_at_paperScale_of_finiteFixedSpanAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
