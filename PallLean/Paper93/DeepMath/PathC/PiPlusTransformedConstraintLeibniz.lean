import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteTransformLemmas
import PallLean.Paper93.DeepMath.PathC.PiPlusBoolLinear

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


/-! ## Boolean-ambient Leibniz image -/

/-- Boolean-ambient image of the finite-product Leibniz rule.  Applying
`liftToBool` after differentiating a product lands in the span of the Boolean
lifts of the distributed Leibniz products.  This is the direct product-rule
layer needed by the paper Boolean ambient: no derivative-erasure or
normalization-commutation identity is used. -/
theorem liftToBool_iterDerivList_finset_prod_mem_span_image
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) (S : List (Fin n)) :
    BoolPoly.liftToBool (iterDerivList S (s.prod f)) ∈
      Submodule.span ℚ
        (BoolPoly.liftToBool '' distribDerivProds s f S) := by
  have hraw : iterDerivList S (s.prod f) ∈
      Submodule.span ℚ (distribDerivProds s f S) :=
    iterDerivList_finset_prod_mem_span s f S
  have hmap : BoolPoly.liftToBoolLinearMap n (iterDerivList S (s.prod f)) ∈
      Submodule.map (BoolPoly.liftToBoolLinearMap n)
        (Submodule.span ℚ (distribDerivProds s f S)) :=
    Submodule.mem_map_of_mem hraw
  rw [Submodule.map_span] at hmap
  exact hmap


/-- Boolean-ambient row image of the finite-product Leibniz rule, with a fixed
left multiplier.  This is the exact `liftToBool (m * ·)` analogue of the SPDP
`mlProj (m * ·)` Leibniz image theorem. -/
theorem liftToBool_mul_iterDerivList_finset_prod_mem_span_image
    {n : Nat} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℚ) (S : List (Fin n))
    (m : MvPolynomial (Fin n) ℚ) :
    BoolPoly.liftToBool (m * iterDerivList S (s.prod f)) ∈
      Submodule.span ℚ
        ((fun q => BoolPoly.liftToBool (m * q)) '' distribDerivProds s f S) := by
  have hraw : iterDerivList S (s.prod f) ∈
      Submodule.span ℚ (distribDerivProds s f S) :=
    iterDerivList_finset_prod_mem_span s f S
  let mulm : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ :=
    { toFun := fun q => m * q
      map_add' := fun x y => mul_add m x y
      map_smul' := fun c x => by
        change m * (c • x) = c • (m * x)
        rw [Algebra.mul_smul_comm] }
  let φ : MvPolynomial (Fin n) ℚ →ₗ[ℚ] BoolPoly n :=
    (BoolPoly.liftToBoolLinearMap n).comp mulm
  have hmap : φ (iterDerivList S (s.prod f)) ∈
      Submodule.map φ (Submodule.span ℚ (distribDerivProds s f S)) :=
    Submodule.mem_map_of_mem hraw
  rw [Submodule.map_span] at hmap
  exact hmap

/-- Boolean-ambient Leibniz decomposition for the concrete transformed
Cook--Levin local-factor product. -/
theorem liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    BoolPoly.liftToBool (iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈
      Submodule.span ℚ
        (BoolPoly.liftToBool ''
          distribDerivProds Finset.univ
            (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D).length =>
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) S) := by
  classical
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  change BoolPoly.liftToBool (iterDerivList S L.prod) ∈
      Submodule.span ℚ
        (BoolPoly.liftToBool ''
          distribDerivProds Finset.univ (fun i : Fin L.length => L[i.val]) S)
  have hprod : L.prod = Finset.univ.prod (fun i : Fin L.length => L[i.val]) := by
    rw [← Fin.prod_univ_getElem]
  rw [hprod]
  exact liftToBool_iterDerivList_finset_prod_mem_span_image Finset.univ
    (fun i : Fin L.length => L[i.val]) S


/-- Boolean-ambient row Leibniz decomposition for the concrete transformed
Cook--Levin local-factor product, with a fixed left multiplier. -/
theorem liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns) :
    BoolPoly.liftToBool (m * iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈
      Submodule.span ℚ
        ((fun q => BoolPoly.liftToBool (m * q)) ''
          distribDerivProds Finset.univ
            (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D).length =>
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) S) := by
  classical
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  change BoolPoly.liftToBool (m * iterDerivList S L.prod) ∈
      Submodule.span ℚ
        ((fun q => BoolPoly.liftToBool (m * q)) ''
          distribDerivProds Finset.univ (fun i : Fin L.length => L[i.val]) S)
  have hprod : L.prod = Finset.univ.prod (fun i : Fin L.length => L[i.val]) := by
    rw [← Fin.prod_univ_getElem]
  rw [hprod]
  exact liftToBool_mul_iterDerivList_finset_prod_mem_span_image Finset.univ
    (fun i : Fin L.length => L[i.val]) S m

/-- Boolean-ambient absorption form of the transformed constraint-product
Leibniz rule.  If every distributed derivative factor has Boolean lift in a
Boolean-ambient target space `W`, then the Boolean lift of the whole derivative
product lies in `W`. -/
theorem liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (W : Submodule ℚ (BoolPoly n))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S,
        BoolPoly.liftToBool q ∈ W) :
    BoolPoly.liftToBool (iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈ W := by
  classical
  have hrow :=
    liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
      M n hn2 htb hns D S
  exact (Submodule.span_le.mpr (by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact hgen q hq)) hrow

/-- Boolean-ambient row absorption form, with a fixed left multiplier.  This is
parallel to the `mlProj` absorption theorem but targets the Boolean quotient
ambient. -/
theorem liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns)
    (W : Submodule ℚ (BoolPoly n))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S,
        BoolPoly.liftToBool (m * q) ∈ W) :
    BoolPoly.liftToBool (m * iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈ W := by
  classical
  have hrow :=
    liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
      M n hn2 htb hns D S m
  exact (Submodule.span_le.mpr (by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact hgen q hq)) hrow

/-- Paper-scale Boolean-ambient Leibniz decomposition for the transformed
Cook--Levin local-factor product. -/
theorem paperScale_liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars)) :
    BoolPoly.liftToBool (iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈
      Submodule.span ℚ
        (BoolPoly.liftToBool ''
          distribDerivProds Finset.univ
            (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns).length =>
              (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns)[i.val]) S) := by
  exact liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S


/-- Paper-scale Boolean-ambient row Leibniz decomposition for the transformed
Cook--Levin local-factor product, with a fixed left multiplier. -/
theorem paperScale_liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    BoolPoly.liftToBool (m * iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈
      Submodule.span ℚ
        ((fun q => BoolPoly.liftToBool (m * q)) ''
          distribDerivProds Finset.univ
            (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns).length =>
              (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
                M htb hns)[i.val]) S) := by
  exact liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S m

/-- Paper-scale Boolean-ambient absorption form of the transformed
constraint-product Leibniz rule. -/
theorem paperScale_liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (W : Submodule ℚ (BoolPoly (2 ^ 804)))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val]) S,
        BoolPoly.liftToBool q ∈ W) :
    BoolPoly.liftToBool (iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈ W := by
  exact liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S W hgen

/-- Paper-scale Boolean-ambient row absorption form, with a fixed left
multiplier. -/
theorem paperScale_liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (W : Submodule ℚ (BoolPoly (2 ^ 804)))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val]) S,
        BoolPoly.liftToBool (m * q) ∈ W) :
    BoolPoly.liftToBool (m * iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈ W := by
  exact liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S m W hgen

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

/-- Submodule absorption form of the transformed constraint-product Leibniz
expansion.  To prove the projected product row lies in a target row space `W`,
it suffices to prove that every distributed Leibniz generator row lies in `W`.
This is the exact assembly rule needed after local Booleanity/rest certificates
classify the distributed factors. -/
theorem mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns)
    (W : Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S,
        mlProj (m * q) ∈ W) :
    mlProj (m * iterDerivList S
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).prod) ∈ W := by
  classical
  have hrow :=
    mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
      M n hn2 htb hns D S m
  exact (Submodule.span_le.mpr (by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact hgen q hq)) hrow

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

/-- Paper-scale submodule absorption form of the transformed constraint-product
Leibniz expansion. -/
theorem paperScale_mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (m : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)
    (W : Submodule ℚ (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns))
    (hgen : ∀ q ∈ distribDerivProds Finset.univ
          (fun i : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns).length =>
            (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
              M htb hns)[i.val]) S,
        mlProj (m * q) ∈ W) :
    mlProj (m * iterDerivList S
        (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
          M htb hns).prod) ∈ W := by
  exact mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) S m W hgen

/-! ## Axiom audit anchors -/

#print axioms liftToBool_iterDerivList_finset_prod_mem_span_image
#print axioms liftToBool_mul_iterDerivList_finset_prod_mem_span_image
#print axioms liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms paperScale_liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms paperScale_liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
#print axioms liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
#print axioms paperScale_liftToBool_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
#print axioms paperScale_liftToBool_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
#print axioms iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
#print axioms mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows
#print axioms paperScale_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan
#print axioms paperScale_mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_distribSpan_image
#print axioms paperScale_mlProj_mul_iterDerivList_piPlusBooleanProjectedTransformedConstraintFactors_prod_mem_of_distribRows

end PallLean.Paper93.DeepMath.PathC
