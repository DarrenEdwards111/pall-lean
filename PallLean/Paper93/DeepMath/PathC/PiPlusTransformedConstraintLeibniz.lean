import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteTransformLemmas

/-!
# Leibniz surface for transformed Cook--Levin constraint products

The concrete Boolean-projected `Pi+` target is now exposed as the Boolean normal
form of a product of transformed local Cook--Levin constraint factors.  This file
adds the next axiom-free surface needed by the P-side assembly: ordinary
Leibniz expansion for that transformed local-factor product, plus the SPDP-row
image form after multiplying by a row multiplier and applying `mlProj`.

This still does not commute derivatives through Boolean normalization.  It pins
that remaining problem to a concrete generator set: distributed derivatives of
transformed local constraint factors.
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

/-- The local Cook--Levin constraint factors after applying the concrete
Boolean-projected `Pi+` gauge. -/
noncomputable def piPlusBooleanProjectedTransformedConstraintFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    List (SATDeciderGaugeSpace M n hn2 htb hns) :=
  ((cook_levin_compilation M n hn2 htb hns).constraints.map
    (fun c => (1 : SATDeciderGaugeSpace M n hn2 htb hns) - c.poly)).map
    (piPlusBooleanProjectedGauge M n hn2 htb hns
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D))

/-- Paper-scale specialization of the transformed local constraint factor list. -/
noncomputable abbrev cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    List (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :=
  piPlusBooleanProjectedTransformedConstraintFactors
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Leibniz expansion for the product of transformed local Cook--Levin
constraint factors. -/
theorem iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod ∈
      Submodule.span ℚ
        (distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S) := by
  classical
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  change iterDerivList S L.prod ∈
      Submodule.span ℚ
        (distribDerivProds Finset.univ
          (fun i : Fin L.length => L[i.val]) S)
  have hprod : L.prod = Finset.univ.prod (fun i : Fin L.length => L[i.val]) := by
    rw [← Fin.prod_univ_getElem]
  rw [hprod]
  exact iterDerivList_finset_prod_mem_span Finset.univ
    (fun i : Fin L.length => L[i.val]) S

/-- SPDP-row image form of the transformed constraint-product Leibniz expansion.
After multiplying by a fixed row multiplier and applying `mlProj`, the row lies
in the span of the corresponding projected distributed-derivative generators. -/
theorem mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlProj (m * iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈
      Submodule.span ℚ
        ((fun q => mlProj (m * q)) ''
          distribDerivProds Finset.univ
            (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D).length =>
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) S) := by
  classical
  exact SymmetricPower.mlProj_mul_mem_span_image m _ _
    (iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
      M n hn2 htb hns D S)

/-- Paper-scale Leibniz expansion for the product of transformed local
Cook--Levin constraint factors. -/
theorem paperScale_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)) :
    iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod ∈
      Submodule.span ℚ
        (distribDerivProds Finset.univ
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val]) S) := by
  exact iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S

/-- Paper-scale SPDP-row image form of the transformed constraint-product
Leibniz expansion. -/
theorem paperScale_mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    mlProj (m * iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈
      Submodule.span ℚ
        ((fun q => mlProj (m * q)) ''
          distribDerivProds Finset.univ
            (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns).length =>
              (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns)[i.val]) S) := by
  exact mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S m

/-! ## Axiom audit anchors -/

#print axioms iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
#print axioms mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms paperScale_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
#print axioms paperScale_mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image

end PallLean.Paper93.DeepMath.PathC
