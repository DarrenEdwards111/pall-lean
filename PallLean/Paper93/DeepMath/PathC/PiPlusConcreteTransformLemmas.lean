import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCoordinateAtom

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

/-! ## Axiom audit anchors -/

#print axioms piPlusSATTransform_of_blockCoordinates_gauge_apply
#print axioms piPlusSATTransform_of_blockCoordinates_symm_apply
#print axioms piPlusBooleanProjectedGauge_of_blockCoordinates_apply
#print axioms cookLevinPiPlusSATTransform_paperScale_gauge_apply
#print axioms cookLevinPiPlusSATTransform_paperScale_symm_apply
#print axioms cookLevinPiPlusBooleanProjectedGauge_paperScale_apply

end PallLean.Paper93.DeepMath.PathC
