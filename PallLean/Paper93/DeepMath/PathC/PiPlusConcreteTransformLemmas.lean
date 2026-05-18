import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanNormalizeProductLemmas

/-!
# Concrete transform bridge lemmas

Small definitional bridges exposing that the paper-scale `PiPlusSATTransform`
constructed from block coordinates is the linear shadow of the concrete
`piPlusSATBlockAlgEquiv`.  These let later Route-C proofs use the algebra
homomorphism facts (`map_mul`, coordinate formulas) and then rewrite back to the
`PiPlusSATTransform` interface.
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

/-- The forward gauge map of the coordinate-built `Pi+` transform is exactly the
underlying function of the concrete block algebra equivalence. -/
theorem piPlusSATTransform_of_blockCoordinates_gauge_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).gauge p =
      piPlusSATBlockAlgEquiv M n hn2 htb hns D p := by
  rfl

/-- The inverse map of the coordinate-built `Pi+` transform is exactly the
inverse of the concrete block algebra equivalence. -/
theorem piPlusSATTransform_of_blockCoordinates_symm_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).equiv.symm p =
      (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm p := by
  rfl

/-- Concrete form of the Boolean-projected gauge for coordinate-built `Pi+`. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) p =
      zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D p) := by
  rfl

/-- Paper-scale forward gauge as the concrete block algebra equivalence. -/
theorem cookLevinPiPlusSATTransform_paperScale_gauge_apply
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).gauge p =
      piPlusSATBlockAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p := by
  rfl

/-- Paper-scale inverse gauge as the inverse concrete block algebra equivalence. -/
theorem cookLevinPiPlusSATTransform_paperScale_symm_apply
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm p =
      (piPlusSATBlockAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)).symm p := by
  rfl

/-- Paper-scale Boolean-projected gauge as normalization after the concrete block
algebra equivalence. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_apply
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns p =
      zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p) := by
  rfl

/-- Concrete product law for the Boolean-projected gauge: for the coordinate-built
`Pi+`, projected transport commutes with multiplication up to the final Boolean
normal form.  This is the global quotient-product commutation needed by the
factored Cook--Levin assembly. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_mul
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p q : SATDeciderGaugeSpace M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) (p * q) =
      zeroProfileBooleanNormalize
        (piPlusBooleanProjectedGauge M n hn2 htb hns
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) p *
          piPlusBooleanProjectedGauge M n hn2 htb hns
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) q) := by
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_apply]
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_apply]
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_apply]
  rw [map_mul]
  exact (zeroProfileBooleanNormalize_mul_normalized
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D p)
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D q)).symm

/-- Concrete list-product law for the Boolean-projected gauge: the image of a
finite product is the Boolean normal form of the product of the individual
Boolean-projected images. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_list_prod
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (L : List (SATDeciderGaugeSpace M n hn2 htb hns)) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) L.prod =
      zeroProfileBooleanNormalize
        ((L.map (piPlusBooleanProjectedGauge M n hn2 htb hns
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D))).prod) := by
  induction L with
  | nil =>
      simp [piPlusBooleanProjectedGauge_of_blockCoordinates_apply]
  | cons p rest ih =>
      simp only [List.prod_cons, List.map_cons]
      rw [piPlusBooleanProjectedGauge_of_blockCoordinates_mul]
      rw [ih]
      exact zeroProfileBooleanNormalize_mul_right_normalized
        (piPlusBooleanProjectedGauge M n hn2 htb hns
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) p)
        ((rest.map (piPlusBooleanProjectedGauge M n hn2 htb hns
          (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D))).prod)

/-- Paper-scale product law for the concrete Boolean-projected Cook--Levin
`Pi+` transform. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_mul
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p q : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns (p * q) =
      zeroProfileBooleanNormalize
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns p *
          cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns q) := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_mul
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) p q

/-- Paper-scale list-product law for the concrete Boolean-projected Cook--Levin
`Pi+` transform. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_list_prod
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (L : List (SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns L.prod =
      zeroProfileBooleanNormalize
        ((L.map (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)).prod) := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_list_prod
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) L

/-- Generic Booleanity-product transport through a coordinate-built concrete
Boolean-projected `Pi+` transform. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_booleanFactorProd
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
        (cookLevinBooleanFactorProd n) =
      zeroProfileBooleanNormalize
        (((List.finRange n).map
          (fun v => piPlusBooleanProjectedGauge M n hn2 htb hns
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
            (cookLevinBooleanFactor n v))).prod) := by
  rw [cookLevinBooleanFactorProd_eq_finRange]
  have h := piPlusBooleanProjectedGauge_of_blockCoordinates_list_prod
    M n hn2 htb hns D
    ((List.finRange n).map (fun v => cookLevinBooleanFactor n v))
  simpa [List.map_map] using h

/-- Paper-scale Booleanity-product transport through the concrete
Boolean-projected Cook--Levin `Pi+` transform. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_booleanFactorProd
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        (cookLevinBooleanFactorProd (2 ^ 804)) =
      zeroProfileBooleanNormalize
        (((List.finRange (2 ^ 804)).map
          (fun v => cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
            (cookLevinBooleanFactor (2 ^ 804) v))).prod) := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_booleanFactorProd
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Generic compiled Cook--Levin constraint-product transport through a
coordinate-built concrete Boolean-projected `Pi+` transform.  This is the raw
local-factor surface for the derivative/Leibniz assembly: the target compiled
polynomial is the Boolean normal form of the product of transformed individual
constraint factors. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_compiledPoly_constraints
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      zeroProfileBooleanNormalize
        ((((cook_levin_compilation M n hn2 htb hns).constraints.map
          (fun c => (1 : SATDeciderGaugeSpace M n hn2 htb hns) - c.poly)).map
          (piPlusBooleanProjectedGauge M n hn2 htb hns
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D))).prod) := by
  let L : List (SATDeciderGaugeSpace M n hn2 htb hns) :=
    (cook_levin_compilation M n hn2 htb hns).constraints.map
      (fun c => (1 : SATDeciderGaugeSpace M n hn2 htb hns) - c.poly)
  change piPlusBooleanProjectedGauge M n hn2 htb hns
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) L.prod =
    zeroProfileBooleanNormalize
      ((L.map (piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D))).prod)
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_list_prod
    M n hn2 htb hns D L

/-- Paper-scale compiled Cook--Levin constraint-product transport through the
concrete Boolean-projected `Pi+` transform. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_compiledPoly_constraints
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) =
      zeroProfileBooleanNormalize
        ((((cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).constraints.map
          (fun c => (1 : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) - c.poly)).map
          (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)).prod) := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_compiledPoly_constraints
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Generic factored Cook--Levin-product transport through a coordinate-built
concrete Boolean-projected `Pi+` transform. -/
theorem piPlusBooleanProjectedGauge_of_blockCoordinates_cookLevinFactoredPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns
        (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
        (cookLevinFactoredPoly M n) =
      zeroProfileBooleanNormalize
        (zeroProfileBooleanNormalize
          (((List.finRange n).map
            (fun v => piPlusBooleanProjectedGauge M n hn2 htb hns
              (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
              (cookLevinBooleanFactor n v))).prod) *
          piPlusBooleanProjectedGauge M n hn2 htb hns
            (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D)
            (restFactorProd' M n)) := by
  unfold cookLevinFactoredPoly
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_mul]
  rw [piPlusBooleanProjectedGauge_of_blockCoordinates_booleanFactorProd]

/-- Paper-scale factored Cook--Levin-product transport through the concrete
Boolean-projected `Pi+` transform.  This exposes the global product as the
Boolean normal form of the transported Booleanity side times the transported
rest side. -/
theorem cookLevinPiPlusBooleanProjectedGauge_paperScale_cookLevinFactoredPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        (cookLevinFactoredPoly M (2 ^ 804)) =
      zeroProfileBooleanNormalize
        (zeroProfileBooleanNormalize
          (((List.finRange (2 ^ 804)).map
            (fun v => cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
              (cookLevinBooleanFactor (2 ^ 804) v))).prod) *
          cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
            (restFactorProd' M (2 ^ 804))) := by
  exact piPlusBooleanProjectedGauge_of_blockCoordinates_cookLevinFactoredPoly
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale coordinate atom, rewritten entirely through the public
`cookLevinPiPlusSATTransform_paperScale` / `cookLevinPiPlusBooleanProjectedGauge_paperScale`
interfaces. -/
theorem cookLevinPiPlusSATTransform_paperScale_symm_booleanProjected_mixed
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        ((X (satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) *
          (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) =
      (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
            (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i) :
        SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) := by
  rw [cookLevinPiPlusBooleanProjectedGauge_paperScale_apply,
    cookLevinPiPlusSATTransform_paperScale_symm_apply]
  exact piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i

/-- Paper-scale membership form of the coordinate atom using the public concrete
`Pi+` interfaces. -/
theorem cookLevinPiPlusSATTransform_paperScale_symm_booleanProjected_mixed_mem_inc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex)
    (B : SPDP.BlockPartition (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hadm : SPDP.isBlockAdmissible B
      [satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i]) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        ((X (satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) *
          (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) ∈
      mlBlockedSpdpSubspaceInc B 1 0
        (((X (satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) *
          (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) := by
  rw [cookLevinPiPlusBooleanProjectedGauge_paperScale_apply,
    cookLevinPiPlusSATTransform_paperScale_symm_apply]
  exact piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_mem_inc
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i B hadm

/-! ## Axiom audit anchors -/

#print axioms piPlusSATTransform_of_blockCoordinates_gauge_apply
#print axioms piPlusSATTransform_of_blockCoordinates_symm_apply
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_apply
#print axioms cookLevinPiPlusSATTransform_paperScale_gauge_apply
#print axioms cookLevinPiPlusSATTransform_paperScale_symm_apply
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_apply
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_mul
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_list_prod
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_mul
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_list_prod
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_booleanFactorProd
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_booleanFactorProd
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_compiledPoly_constraints
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_compiledPoly_constraints
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_cookLevinFactoredPoly
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_cookLevinFactoredPoly
#print axioms cookLevinPiPlusSATTransform_paperScale_symm_booleanProjected_mixed
#print axioms cookLevinPiPlusSATTransform_paperScale_symm_booleanProjected_mixed_mem_inc

end PallLean.Paper93.DeepMath.PathC
