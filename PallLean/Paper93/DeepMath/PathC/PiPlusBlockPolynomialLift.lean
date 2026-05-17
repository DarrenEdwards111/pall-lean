import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteHadamard

/-!
# Block-coordinate polynomial lift for Pi+

This is the next lift after the local two-variable calculation: for variables
indexed by `ι × Bool`, apply the same unnormalised Hadamard/Fourier transform
on every `Bool` fibre.

The result is an algebra equivalence of polynomial rings, hence a linear
equivalence.  This is the reusable object needed to instantiate the SAT-scale
`PiPlusSATTransform` once the Cook--Levin variables are coordinated as
block-local pairs.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

variable (ι : Type*)

/-- The block-local Pi+ linear form on variables indexed by `ι × Bool`. -/
noncomputable def blockPiPlusLinearForm (v : ι × Bool) :
    MvPolynomial (ι × Bool) ℚ :=
  if v.2 = false then
    X (v.1, false) + X (v.1, true)
  else
    X (v.1, false) - X (v.1, true)

/-- The inverse half-Hadamard linear form. -/
noncomputable def blockPiPlusInvLinearForm (v : ι × Bool) :
    MvPolynomial (ι × Bool) ℚ :=
  if v.2 = false then
    (1 / 2 : ℚ) • (X (v.1, false) + X (v.1, true))
  else
    (1 / 2 : ℚ) • (X (v.1, false) - X (v.1, true))

/-- The block-local Pi+ algebra homomorphism. -/
noncomputable def blockPiPlusAlgHom :
    MvPolynomial (ι × Bool) ℚ →ₐ[ℚ] MvPolynomial (ι × Bool) ℚ :=
  aeval (blockPiPlusLinearForm ι)

/-- The inverse half-Hadamard algebra homomorphism. -/
noncomputable def blockPiPlusInvAlgHom :
    MvPolynomial (ι × Bool) ℚ →ₐ[ℚ] MvPolynomial (ι × Bool) ℚ :=
  aeval (blockPiPlusInvLinearForm ι)

@[simp] theorem blockPiPlusAlgHom_X_false (i : ι) :
    blockPiPlusAlgHom ι (X (i, false)) =
      (X (i, false) + X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusAlgHom, blockPiPlusLinearForm]

@[simp] theorem blockPiPlusAlgHom_X_true (i : ι) :
    blockPiPlusAlgHom ι (X (i, true)) =
      (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusAlgHom, blockPiPlusLinearForm]

@[simp] theorem blockPiPlusInvAlgHom_X_false (i : ι) :
    blockPiPlusInvAlgHom ι (X (i, false)) =
      ((1 / 2 : ℚ) • (X (i, false) + X (i, true)) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusInvAlgHom, blockPiPlusInvLinearForm]

@[simp] theorem blockPiPlusInvAlgHom_X_true (i : ι) :
    blockPiPlusInvAlgHom ι (X (i, true)) =
      ((1 / 2 : ℚ) • (X (i, false) - X (i, true)) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusInvAlgHom, blockPiPlusInvLinearForm]

/-- The inverse after Pi+ is identity. -/
theorem blockPiPlusInv_comp_blockPiPlus :
    (blockPiPlusInvAlgHom ι).comp (blockPiPlusAlgHom ι) =
      AlgHom.id ℚ (MvPolynomial (ι × Bool) ℚ) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, b⟩
  cases b <;>
    simp [AlgHom.comp_apply, map_add, map_sub] <;> module

/-- Pi+ after the inverse is identity. -/
theorem blockPiPlus_comp_blockPiPlusInv :
    (blockPiPlusAlgHom ι).comp (blockPiPlusInvAlgHom ι) =
      AlgHom.id ℚ (MvPolynomial (ι × Bool) ℚ) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, b⟩
  cases b <;>
    simp [AlgHom.comp_apply, map_add, map_sub] <;> module

/-- The block-local Pi+ polynomial algebra equivalence. -/
noncomputable def blockPiPlusAlgEquiv :
    MvPolynomial (ι × Bool) ℚ ≃ₐ[ℚ] MvPolynomial (ι × Bool) ℚ where
  toFun := blockPiPlusAlgHom ι
  invFun := blockPiPlusInvAlgHom ι
  left_inv p := by
    exact congrArg (fun f : MvPolynomial (ι × Bool) ℚ →ₐ[ℚ]
      MvPolynomial (ι × Bool) ℚ => f p) (blockPiPlusInv_comp_blockPiPlus ι)
  right_inv p := by
    exact congrArg (fun f : MvPolynomial (ι × Bool) ℚ →ₐ[ℚ]
      MvPolynomial (ι × Bool) ℚ => f p) (blockPiPlus_comp_blockPiPlusInv ι)
  map_mul' p q := map_mul (blockPiPlusAlgHom ι) p q
  map_add' p q := map_add (blockPiPlusAlgHom ι) p q
  commutes' c := by simp [blockPiPlusAlgHom]

/-- The associated linear equivalence. -/
noncomputable def blockPiPlusLinearEquiv :
    MvPolynomial (ι × Bool) ℚ ≃ₗ[ℚ] MvPolynomial (ι × Bool) ℚ :=
  (blockPiPlusAlgEquiv ι).toLinearEquiv

@[simp] theorem blockPiPlusLinearEquiv_one :
    blockPiPlusLinearEquiv ι (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
  simp [blockPiPlusLinearEquiv, blockPiPlusAlgEquiv]

@[simp] theorem blockPiPlusLinearEquiv_X_false (i : ι) :
    blockPiPlusLinearEquiv ι (X (i, false)) =
      (X (i, false) + X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusLinearEquiv, blockPiPlusAlgEquiv]

@[simp] theorem blockPiPlusLinearEquiv_X_true (i : ι) :
    blockPiPlusLinearEquiv ι (X (i, true)) =
      (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  simp [blockPiPlusLinearEquiv, blockPiPlusAlgEquiv]

/-- Concrete block-polynomial admissibility core. -/
def BlockPiPlusPolynomialAdmissibilityCore : Prop :=
  blockPiPlusLinearEquiv ι (1 : MvPolynomial (ι × Bool) ℚ) = 1 ∧
    (∀ i : ι,
      blockPiPlusLinearEquiv ι (X (i, false)) =
        (X (i, false) + X (i, true) : MvPolynomial (ι × Bool) ℚ)) ∧
    (∀ i : ι,
      blockPiPlusLinearEquiv ι (X (i, true)) =
        (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ))

theorem blockPiPlusPolynomialAdmissibilityCore :
    BlockPiPlusPolynomialAdmissibilityCore ι := by
  exact ⟨by simp, by intro i; simp, by intro i; simp⟩

/-! ## SAT-scale coordinate lift interface -/

/-- Block-coordinate data for a SAT-decider instance: a concrete equivalence
between the flat Cook--Levin variable index type and block-local `ι × Bool`
coordinates.  Supplying this is the remaining bookkeeping step before the
block-polynomial `Pi+` transform becomes a concrete `PiPlusSATTransform`. -/
structure PiPlusSATBlockCoordinateData
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  blockIndex : Type
  coord : Fin (cook_levin_compilation M n hn2 htb hns).numVars ≃ blockIndex × Bool

/-- The SAT-scale algebra equivalence obtained by conjugating the block-local
Hadamard transform through a Cook--Levin block-coordinate equivalence. -/
noncomputable def piPlusSATBlockAlgEquiv
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    SATDeciderGaugeSpace M n hn2 htb hns ≃ₐ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  ((MvPolynomial.renameEquiv ℚ D.coord).trans
    (blockPiPlusAlgEquiv D.blockIndex)).trans
      (MvPolynomial.renameEquiv ℚ D.coord.symm)

/-- The SAT-scale `PiPlusSATTransform` induced by block coordinates. -/
noncomputable def piPlusSATTransform_of_blockCoordinates
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    PiPlusSATTransform M n hn2 htb hns where
  equiv := (piPlusSATBlockAlgEquiv M n hn2 htb hns D).toLinearEquiv
  block_local_hadamard_lift := True

/-- The coordinate-lifted SAT `Pi+` transform is block-local by construction. -/
theorem piPlusSATTransform_of_blockCoordinates_blockLocal
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D).block_local_hadamard_lift :=
  trivial

/-- The coordinate-lifted SAT `Pi+` transform preserves the constant `1`. -/
theorem piPlusSATTransform_of_blockCoordinates_unitPreserving
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    PiPlusUnitPreserving M n hn2 htb hns
      (piPlusSATTransform_of_blockCoordinates M n hn2 htb hns D) := by
  unfold PiPlusUnitPreserving piPlusSATTransform_of_blockCoordinates PiPlusSATTransform.gauge
  simp [piPlusSATBlockAlgEquiv]

/-! ## Axiom audit anchors -/

#print axioms blockPiPlusInv_comp_blockPiPlus
#print axioms blockPiPlus_comp_blockPiPlusInv
#print axioms blockPiPlusAlgEquiv
#print axioms blockPiPlusLinearEquiv_one
#print axioms blockPiPlusLinearEquiv_X_false
#print axioms blockPiPlusLinearEquiv_X_true
#print axioms blockPiPlusPolynomialAdmissibilityCore
#print axioms piPlusSATBlockAlgEquiv
#print axioms piPlusSATTransform_of_blockCoordinates
#print axioms piPlusSATTransform_of_blockCoordinates_blockLocal
#print axioms piPlusSATTransform_of_blockCoordinates_unitPreserving

end PallLean.Paper93.DeepMath.PathC
