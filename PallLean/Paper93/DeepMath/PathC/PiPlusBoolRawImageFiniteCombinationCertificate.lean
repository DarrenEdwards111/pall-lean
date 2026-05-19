import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageFiniteFixedSpanCertificate

/-!
# Finite linear-combination certificates for raw-image gauge fixedness

The finite fixed-family seam still used abstract span membership.  This file
peels that to an explicit linear-combination certificate: exhibit a finite family
of fixed polynomial pieces and coefficients whose finite sum is the compiled
polynomial.

This is the form closest to a Cook--Levin decomposition calculation: list the
local fixed pieces, give their coefficients, and prove their weighted sum equals
the target polynomial.
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

/-- Finite linear-combination certificate: exhibit a finite set `F` of fixed
vectors and coefficients `c` whose weighted sum is `q`. -/
def PiPlusRawRowFiniteFixedCombinationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∃ (F : Finset (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (c : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ → ℚ),
    q = F.sum (fun g => c g • g) ∧
      ∀ g ∈ F,
        g ∈ LinearMap.ker
          (piP.gauge -
            (LinearMap.id :
              MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
                MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

/-- An explicit finite fixed linear combination gives finite fixed-span
membership. -/
theorem piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hcomb : PiPlusRawRowFiniteFixedCombinationCertificate piP q) :
    PiPlusRawRowFiniteFixedSpanCertificate piP q := by
  rcases hcomb with ⟨F, c, hsum, hF⟩
  refine ⟨F, ?_, hF⟩
  rw [hsum]
  exact Submodule.sum_mem _ (fun g hg =>
    Submodule.smul_mem _ (c g) (Submodule.subset_span hg))

/-- Finite fixed-combination certificates imply fixed-span certificates. -/
theorem piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hcomb : PiPlusRawRowFiniteFixedCombinationCertificate piP q) :
    PiPlusRawRowGaugeFixedSpanCertificate piP q :=
  piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan piP q
    (piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination piP q hcomb)

/-- Finite fixed-combination certificates imply corrected raw-image rank
invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_finiteFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hcomb : PiPlusRawRowFiniteFixedCombinationCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_finiteFixedSpan piP κ ℓ q
    (piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination piP q hcomb)

/-- Paper-scale finite fixed-combination certificate for the concrete `Pi+` at
the compiled Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowFiniteFixedCombinationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale finite fixed-combination certificate gives finite fixed-span
membership. -/
theorem paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomb : PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns :=
  piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hcomb

/-- Paper-scale finite fixed-combination certificate gives fixed-span
membership. -/
theorem paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomb : PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate M htb hns :=
  paperScaleCookLevinPiPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedSpan
    M htb hns
    (paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
      M htb hns hcomb)

/-- Paper-scale finite fixed-combination certificate implies corrected raw-image
rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomb : PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedSpan
    M htb hns
    (paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
      M htb hns hcomb)

/-- No-decider surface using an explicit finite fixed linear-combination
decomposition for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_finiteFixedCombinationAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hcomb : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_finiteFixedSpanAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
        M htb hns (Hcomb hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
#print axioms piPlusRawRowGaugeFixedSpanCertificate_of_finiteFixedCombination
#print axioms piPlusBoolRawImageRankInvariant_of_finiteFixedCombination
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedCombination
#print axioms no_decidesSAT_at_paperScale_of_finiteFixedCombinationAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
