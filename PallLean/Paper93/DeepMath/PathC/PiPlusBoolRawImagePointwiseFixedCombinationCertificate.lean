import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageFiniteCombinationCertificate

/-!
# Pointwise fixed finite-combination certificates for raw-image gauge fixedness

The explicit finite-combination seam required each listed piece to lie in the
kernel of `Pi+ - id`.  This file peels that to the more direct pointwise equality
used in coordinate calculations:

`Pi+ g = g` for every listed piece `g`.

Kernel membership follows by rewriting the difference to zero, and the existing
finite-combination closeout then applies.
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

/-- Pointwise fixed finite-combination certificate: exhibit a finite set `F`,
coefficients `c`, and an explicit weighted-sum decomposition of `q`, with every
listed piece pointwise fixed by `Pi+`. -/
def PiPlusRawRowPointwiseFixedCombinationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∃ (F : Finset (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    (c : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ → ℚ),
    q = F.sum (fun g => c g • g) ∧
      ∀ g ∈ F, piP.gauge g = g

/-- Pointwise fixedness of a listed piece gives kernel membership for `Pi+ - id`. -/
theorem piPlus_fixedPiece_mem_kernel_of_pointwiseFixed
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (g : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hfixed : piP.gauge g = g) :
    g ∈ LinearMap.ker
      (piP.gauge -
        (LinearMap.id :
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
            MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) := by
  apply LinearMap.mem_ker.mpr
  change piP.gauge g - g = 0
  exact sub_eq_zero.mpr hfixed

/-- A pointwise fixed finite-combination certificate gives the previous kernel
finite-combination certificate. -/
theorem piPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpoint : PiPlusRawRowPointwiseFixedCombinationCertificate piP q) :
    PiPlusRawRowFiniteFixedCombinationCertificate piP q := by
  rcases hpoint with ⟨F, c, hsum, hF⟩
  refine ⟨F, c, hsum, ?_⟩
  intro g hg
  exact piPlus_fixedPiece_mem_kernel_of_pointwiseFixed piP g (hF g hg)

/-- Pointwise fixed finite-combination certificates imply finite fixed-span
membership. -/
theorem piPlusRawRowFiniteFixedSpanCertificate_of_pointwiseFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpoint : PiPlusRawRowPointwiseFixedCombinationCertificate piP q) :
    PiPlusRawRowFiniteFixedSpanCertificate piP q :=
  piPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination piP q
    (piPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination piP q hpoint)

/-- Pointwise fixed finite-combination certificates imply corrected raw-image
rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpoint : PiPlusRawRowPointwiseFixedCombinationCertificate piP q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_finiteFixedCombination piP κ ℓ q
    (piPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination piP q hpoint)

/-- Paper-scale pointwise fixed finite-combination certificate for the concrete
`Pi+` at the compiled Cook--Levin polynomial. -/
def PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowPointwiseFixedCombinationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale pointwise fixed finite-combination certificate gives the kernel
finite-combination certificate. -/
theorem paperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoint : PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate M htb hns :=
  piPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hpoint

/-- Paper-scale pointwise fixed finite-combination certificate gives finite
fixed-span membership. -/
theorem paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_pointwiseFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoint : PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate M htb hns :=
  paperScaleCookLevinPiPlusRawRowFiniteFixedSpanCertificate_of_finiteFixedCombination
    M htb hns
    (paperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
      M htb hns hpoint)

/-- Paper-scale pointwise fixed finite-combination certificate implies corrected
raw-image rank invariance. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoint : PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_finiteFixedCombination
    M htb hns
    (paperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
      M htb hns hpoint)

/-- No-decider surface using a pointwise fixed explicit finite-combination
decomposition for the concrete `Pi+`. -/
theorem no_decidesSAT_at_paperScale_of_pointwiseFixedCombinationAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpoint : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowPointwiseFixedCombinationCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_finiteFixedCombinationAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec =>
      paperScaleCookLevinPiPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
        M htb hns (Hpoint hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlus_fixedPiece_mem_kernel_of_pointwiseFixed
#print axioms piPlusRawRowFiniteFixedCombinationCertificate_of_pointwiseFixedCombination
#print axioms piPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_pointwiseFixedCombination
#print axioms no_decidesSAT_at_paperScale_of_pointwiseFixedCombinationAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
