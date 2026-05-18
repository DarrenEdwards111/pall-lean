import PallLean.Paper93.DeepMath.PathC.PiPlusGeneratorAllocationCertificate

/-!
# Criterion for the normalized derivative span

The P-side normalization payload is currently:

`iterDerivList S (booleanNormalize transformedProduct) ∈ span(distributed derivatives)`.

This file splits it into two concrete local facts:

1. derivatives commute with the final Boolean normal representative for the
   transformed product at the relevant rows;
2. the distributed Leibniz generator span is stable under Boolean
   normalization.

Together with the ordinary Leibniz theorem already proved for the unnormalized
transformed product, these imply the existing normalized derivative span.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open LeibnizProduct

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Local criterion for the normalized transformed-product derivative span. -/
def PiPlusBooleanProjectedNormalizedDerivativeCriterion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      let L := piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D
      let G := distribDerivProds Finset.univ
        (fun i : Fin L.length => L[i.val]) S
      iterDerivList S (zeroProfileBooleanNormalize L.prod) =
        zeroProfileBooleanNormalize (iterDerivList S L.prod) ∧
      (∀ q ∈ G, zeroProfileBooleanNormalize q ∈ Submodule.span ℚ G)

/-- The normalized derivative criterion implies the polynomial-level normalized
Leibniz span. -/
theorem normalizedDerivativePolynomialSpan_of_criterion
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hcrit : PiPlusBooleanProjectedNormalizedDerivativeCriterion
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M n hn2 htb hns D := by
  intro S hSlen hadm
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  let G := distribDerivProds Finset.univ (fun i : Fin L.length => L[i.val]) S
  have hraw : iterDerivList S L.prod ∈ Submodule.span ℚ G := by
    simpa [L, G] using
      iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
        M n hn2 htb hns D S
  have hpair := hcrit S hSlen hadm
  have hcomm : iterDerivList S (zeroProfileBooleanNormalize L.prod) =
      zeroProfileBooleanNormalize (iterDerivList S L.prod) := by
    simpa [L, G] using hpair.1
  have hstable : ∀ q ∈ G, zeroProfileBooleanNormalize q ∈ Submodule.span ℚ G := by
    intro q hq
    simpa [L, G] using hpair.2 q hq
  have hmap_le :
      Submodule.map (zeroProfileBooleanNormalizeLinearMap
          (n := (cook_levin_compilation M n hn2 htb hns).numVars))
        (Submodule.span ℚ G) ≤ Submodule.span ℚ G := by
    rw [Submodule.map_span_le]
    intro q hq
    exact hstable q hq
  have hnorm : zeroProfileBooleanNormalize (iterDerivList S L.prod) ∈
      Submodule.span ℚ G := by
    change zeroProfileBooleanNormalizeLinearMap
        (n := (cook_levin_compilation M n hn2 htb hns).numVars)
        (iterDerivList S L.prod) ∈ Submodule.span ℚ G
    exact hmap_le (Submodule.mem_map_of_mem hraw)
  rw [hcomm]
  exact hnorm

/-- Paper-scale normalized derivative criterion. -/
abbrev PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNormalizedDerivativeCriterion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale normalized derivative span from the criterion. -/
theorem paperScale_normalizedDerivativePolynomialSpan_of_criterion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan M htb hns :=
  normalizedDerivativePolynomialSpan_of_criterion
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hcrit

/-- P-side classifier from the normalized derivative criterion plus the
allocation-level generator pullback certificate. -/
theorem paperScale_factoredRowSpanClassifierOneZero_of_normalizedCriterion_and_allocationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (halloc : PaperScalePiPlusBooleanProjectedTransformedLeibnizGeneratorAllocationCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneZero M htb hns :=
  paperScale_factoredRowSpanClassifierOneZero_of_polynomialSpan_and_allocationCertificate
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_criterion M htb hns hcrit)
    halloc

/-! ## Axiom audit anchors -/

#print axioms normalizedDerivativePolynomialSpan_of_criterion
#print axioms paperScale_normalizedDerivativePolynomialSpan_of_criterion
#print axioms paperScale_factoredRowSpanClassifierOneZero_of_normalizedCriterion_and_allocationCertificate

end PallLean.Paper93.DeepMath.PathC
