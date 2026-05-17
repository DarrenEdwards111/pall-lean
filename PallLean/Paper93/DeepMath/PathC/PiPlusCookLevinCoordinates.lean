import PallLean.Paper93.DeepMath.PathC.PiPlusBlockPolynomialLift

/-!
# Cook--Levin block coordinates for Pi+

This file instantiates the generic block-coordinate `Pi+` lift for Cook--Levin
ambient spaces whose variable count is even.  Since this repository's
`cook_levin_compilation` has `numVars = n`, the only real arithmetic needed is a
pairing witness `n = m * 2`.

At the paper scale `n = 2^804`, this witness is immediate with
`m = 2^803`.  Thus the SAT-scale `PiPlusSATTransform` and its unit-preservation
field are now concrete at the final contradiction scale.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Canonical pairing of `Fin (m*2)` into block index and Boolean side. -/
noncomputable def finPairBoolEquiv (m : Nat) : Fin (m * 2) ≃ Fin m × Bool :=
  (finProdFinEquiv.symm).trans ((Equiv.refl (Fin m)).prodCongr finTwoEquiv)

/-- Cook--Levin `Pi+` block-coordinate data whenever `n` is explicitly paired
as `m*2`.  This is the real SAT-scale coordinate bridge needed by Route C. -/
noncomputable def cookLevinPiPlusBlockCoordinateDataOfPair
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) :
    PiPlusSATBlockCoordinateData M n hn2 htb hns where
  blockIndex := Fin m
  coord :=
    (finCongr (cook_levin_numVars M n hn2 htb hns)).trans
      ((finCongr hnpair).trans (finPairBoolEquiv m))

/-- The concrete Cook--Levin `Pi+` SAT transform for paired variable count. -/
noncomputable def cookLevinPiPlusSATTransformOfPair
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) :
    PiPlusSATTransform M n hn2 htb hns :=
  piPlusSATTransform_of_blockCoordinates M n hn2 htb hns
    (cookLevinPiPlusBlockCoordinateDataOfPair M n m hn2 htb hns hnpair)

/-- The paired Cook--Levin `Pi+` transform is block-local by construction. -/
theorem cookLevinPiPlusSATTransformOfPair_blockLocal
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) :
    (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair).block_local_hadamard_lift :=
  piPlusSATTransform_of_blockCoordinates_blockLocal M n hn2 htb hns
    (cookLevinPiPlusBlockCoordinateDataOfPair M n m hn2 htb hns hnpair)

/-- The paired Cook--Levin `Pi+` transform preserves the constant polynomial
`1`.  This discharges the first concrete SAT-scale admissibility field. -/
theorem cookLevinPiPlusSATTransformOfPair_unitPreserving
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) :
    PiPlusUnitPreserving M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair) :=
  piPlusSATTransform_of_blockCoordinates_unitPreserving M n hn2 htb hns
    (cookLevinPiPlusBlockCoordinateDataOfPair M n m hn2 htb hns hnpair)

/-- Paper-scale size lower bound. -/
theorem paperScale_ge_two : 2 ^ 804 ≥ 2 := by
  exact @Nat.le_self_pow 804 (by norm_num : 804 ≠ 0) 2

/-- Paper-scale pairing witness: `2^804 = 2^803 * 2`. -/
theorem paperScale_pairing_2_804 : 2 ^ 804 = 2 ^ 803 * 2 := by
  rw [pow_succ]

/-- Paper-scale Cook--Levin `Pi+` block-coordinate data. -/
noncomputable def cookLevinPiPlusBlockCoordinateData_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PiPlusSATBlockCoordinateData M (2 ^ 804)
      paperScale_ge_two htb hns :=
  cookLevinPiPlusBlockCoordinateDataOfPair M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-- Paper-scale Cook--Levin `Pi+` SAT transform. -/
noncomputable def cookLevinPiPlusSATTransform_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PiPlusSATTransform M (2 ^ 804) paperScale_ge_two htb hns :=
  cookLevinPiPlusSATTransformOfPair M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-- Paper-scale `Pi+` is block-local. -/
theorem cookLevinPiPlusSATTransform_paperScale_blockLocal
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).block_local_hadamard_lift :=
  cookLevinPiPlusSATTransformOfPair_blockLocal M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-- Paper-scale `Pi+` preserves the constant polynomial `1`. -/
theorem cookLevinPiPlusSATTransform_paperScale_unitPreserving
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PiPlusUnitPreserving M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns) :=
  cookLevinPiPlusSATTransformOfPair_unitPreserving M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-! ## Axiom audit anchors -/

#print axioms finPairBoolEquiv
#print axioms cookLevinPiPlusBlockCoordinateDataOfPair
#print axioms cookLevinPiPlusSATTransformOfPair
#print axioms cookLevinPiPlusSATTransformOfPair_blockLocal
#print axioms cookLevinPiPlusSATTransformOfPair_unitPreserving
#print axioms paperScale_ge_two
#print axioms paperScale_pairing_2_804
#print axioms cookLevinPiPlusBlockCoordinateData_paperScale
#print axioms cookLevinPiPlusSATTransform_paperScale
#print axioms cookLevinPiPlusSATTransform_paperScale_blockLocal
#print axioms cookLevinPiPlusSATTransform_paperScale_unitPreserving

end PallLean.Paper93.DeepMath.PathC
