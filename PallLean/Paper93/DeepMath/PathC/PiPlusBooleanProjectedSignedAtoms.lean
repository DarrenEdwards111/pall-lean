import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAtomClassifier

/-!
# Signed cross-block atom certificates for Boolean-projected Pi+

The first adjacency/transition certificates handled the false/false endpoint
skeleton.  This file removes that endpoint convention: for any Boolean endpoint
choices `bi bj`, a cross-block atom

`1 - c • X(i,bi) * X(j,bj)`

is fixed by Boolean-projected `Pi+` after inverse pullback and is therefore a
zero-derivative source row.  This is the local algebra needed before mapping
arbitrary signed block-coordinate Cook--Levin factors into the atom classifier.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Generic signed cross-block atom.  `c = 1` is adjacency; arbitrary `c` is the
transition skeleton. -/
noncomputable def blockSignedCrossAtom {ι : Type*}
    (c : ℚ) (i j : ι) (bi bj : Bool) : MvPolynomial (ι × Bool) ℚ :=
  (1 : MvPolynomial (ι × Bool) ℚ) -
    c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ)

/-- A transformed signed cross-block quadratic is already Boolean-normal. -/
theorem blockBooleanNormalize_blockPiPlusAlgHom_mul_signed_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (bi bj : Bool) :
    blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, bi)) * (X (j, bj)) : MvPolynomial (ι × Bool) ℚ)) =
      blockPiPlusAlgHom ι
          ((X (i, bi)) * (X (j, bj)) : MvPolynomial (ι × Bool) ℚ) := by
  cases bi <;> cases bj
  · exact blockBooleanNormalize_blockPiPlusAlgHom_mul_false_false_distinct_blocks
      (hij := hij)
  · rw [map_mul]
    simp only [blockPiPlusAlgHom_X_false, blockPiPlusAlgHom_X_true]
    have hprod :
        ((X (i, false) + X (i, true)) * (X (j, false) - X (j, true)) :
            MvPolynomial (ι × Bool) ℚ) =
          X (i, false) * X (j, false) - X (i, false) * X (j, true) +
            X (i, true) * X (j, false) - X (i, true) * X (j, true) := by
      ring
    rw [hprod]
    simp only [blockBooleanNormalize_add, blockBooleanNormalize_sub]
    have hff : (i, false) ≠ (j, false) := by intro h; exact hij (by injection h)
    have hft : (i, false) ≠ (j, true) := by intro h; exact hij (by injection h)
    have htf : (i, true) ≠ (j, false) := by intro h; exact hij (by injection h)
    have htt : (i, true) ≠ (j, true) := by intro h; exact hij (by injection h)
    rw [blockBooleanNormalize_X_mul_X_ne hff,
      blockBooleanNormalize_X_mul_X_ne hft,
      blockBooleanNormalize_X_mul_X_ne htf,
      blockBooleanNormalize_X_mul_X_ne htt]
  · rw [map_mul]
    simp only [blockPiPlusAlgHom_X_false, blockPiPlusAlgHom_X_true]
    have hprod :
        ((X (i, false) - X (i, true)) * (X (j, false) + X (j, true)) :
            MvPolynomial (ι × Bool) ℚ) =
          X (i, false) * X (j, false) + X (i, false) * X (j, true) -
            X (i, true) * X (j, false) - X (i, true) * X (j, true) := by
      ring
    rw [hprod]
    simp only [blockBooleanNormalize_add, blockBooleanNormalize_sub]
    have hff : (i, false) ≠ (j, false) := by intro h; exact hij (by injection h)
    have hft : (i, false) ≠ (j, true) := by intro h; exact hij (by injection h)
    have htf : (i, true) ≠ (j, false) := by intro h; exact hij (by injection h)
    have htt : (i, true) ≠ (j, true) := by intro h; exact hij (by injection h)
    rw [blockBooleanNormalize_X_mul_X_ne hff,
      blockBooleanNormalize_X_mul_X_ne hft,
      blockBooleanNormalize_X_mul_X_ne htf,
      blockBooleanNormalize_X_mul_X_ne htt]
  · rw [map_mul]
    simp only [blockPiPlusAlgHom_X_true]
    have hprod :
        ((X (i, false) - X (i, true)) * (X (j, false) - X (j, true)) :
            MvPolynomial (ι × Bool) ℚ) =
          X (i, false) * X (j, false) - X (i, false) * X (j, true) -
            X (i, true) * X (j, false) + X (i, true) * X (j, true) := by
      ring
    rw [hprod]
    simp only [blockBooleanNormalize_add, blockBooleanNormalize_sub]
    have hff : (i, false) ≠ (j, false) := by intro h; exact hij (by injection h)
    have hft : (i, false) ≠ (j, true) := by intro h; exact hij (by injection h)
    have htf : (i, true) ≠ (j, false) := by intro h; exact hij (by injection h)
    have htt : (i, true) ≠ (j, true) := by intro h; exact hij (by injection h)
    rw [blockBooleanNormalize_X_mul_X_ne hff,
      blockBooleanNormalize_X_mul_X_ne hft,
      blockBooleanNormalize_X_mul_X_ne htf,
      blockBooleanNormalize_X_mul_X_ne htt]

/-- Scalar version of signed cross-block Boolean-normality. -/
theorem blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_signed_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (c : ℚ) (bi bj : Bool) :
    blockBooleanNormalize
        (c • blockPiPlusAlgHom ι
          ((X (i, bi)) * (X (j, bj)) : MvPolynomial (ι × Bool) ℚ)) =
      c • blockPiPlusAlgHom ι
          ((X (i, bi)) * (X (j, bj)) : MvPolynomial (ι × Bool) ℚ) := by
  rw [blockBooleanNormalize_smul]
  rw [blockBooleanNormalize_blockPiPlusAlgHom_mul_signed_distinct_blocks
    (hij := hij)]

/-- Boolean-projected `Pi+` pullback fixes every signed cross-block atom. -/
theorem blockPiPlusInvAlgHom_booleanProjected_signedCrossAtom_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (c : ℚ) (bi bj : Bool) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockSignedCrossAtom c i j bi bj))) =
      blockSignedCrossAtom c i j bi bj := by
  unfold blockSignedCrossAtom
  rw [map_sub, map_one, map_smul, blockBooleanNormalize_sub]
  have hone : blockBooleanNormalize (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.C 1 by rfl]
    rw [MvPolynomial.C_apply, blockBooleanNormalize_monomial]
    rfl
  rw [hone]
  rw [blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_signed_distinct_blocks
    (hij := hij)]
  have hpre :
      (1 : MvPolynomial (ι × Bool) ℚ) -
          c • blockPiPlusAlgHom ι (X (i, bi) * X (j, bj)) =
        blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ)) := by
    rw [map_sub, map_one, map_smul]
  rw [hpre]
  exact
    congrArg (fun f : MvPolynomial (ι × Bool) ℚ →ₐ[ℚ]
        MvPolynomial (ι × Bool) ℚ =>
      f ((1 : MvPolynomial (ι × Bool) ℚ) -
        c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ)))
      (blockPiPlusInv_comp_blockPiPlus ι)

/-- `mlProj` fixes a square-free quadratic monomial. -/
theorem mlProj_X_mul_X_ne {σ : Type*} [DecidableEq σ]
    {a b : σ} (hab : a ≠ b) :
    mlProj (X a * X b : MvPolynomial σ ℚ) =
      (X a * X b : MvPolynomial σ ℚ) := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, mlProj_monomial]
  have hsquarefree : Finsupp.IsMultilinear
      (Finsupp.single a 1 + Finsupp.single b 1 : σ →₀ ℕ) := by
    intro x
    by_cases hxa : x = a
    · subst x
      simp [hab]
    · by_cases hxb : x = b
      · subst x
        simp [hxa]
      · simp [hxa, hxb]
  rw [if_pos hsquarefree]

/-- Signed cross-block atoms are multilinear, so `mlProj` fixes them. -/
theorem mlProj_blockSignedCrossAtom
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (c : ℚ) (bi bj : Bool) :
    mlProj (blockSignedCrossAtom c i j bi bj : MvPolynomial (ι × Bool) ℚ) =
      blockSignedCrossAtom c i j bi bj := by
  unfold blockSignedCrossAtom
  have hidx : (i, bi) ≠ (j, bj) := by
    intro h
    exact hij (by injection h)
  have hmul := mlProj_X_mul_X_ne (σ := ι × Bool) (a := (i, bi)) (b := (j, bj)) hidx
  rw [sub_eq_add_neg, mlProj_add]
  have hone : mlProj (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.monomial 0 1 by rfl,
      mlProj_monomial]
    have h0 : Finsupp.IsMultilinear (0 : ι × Bool →₀ ℕ) := by intro x; simp
    rw [if_pos h0]
  have hneg :
      mlProj (-(c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ))) =
        -(c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ)) := by
    rw [← neg_one_smul ℚ (c • (X (i, bi) * X (j, bj) : MvPolynomial (ι × Bool) ℚ)),
      mlProj_smul, mlProj_smul, hmul]
  rw [hone, hneg]

/-- Every signed cross-block atom gives a zero-derivative source row. -/
theorem blockPiPlus_booleanProjected_signedCrossAtom_pullback_zeroDerivativeRow
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (c : ℚ) (bi bj : Bool) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockSignedCrossAtom c i j bi bj))) =
      mlProj
        ((1 : MvPolynomial (ι × Bool) ℚ) *
          blockIterDerivList [] (blockSignedCrossAtom c i j bi bj)) := by
  rw [blockPiPlusInvAlgHom_booleanProjected_signedCrossAtom_distinct_blocks
    (hij := hij)]
  simp [blockIterDerivList]
  exact (mlProj_blockSignedCrossAtom (hij := hij) c bi bj).symm

/-- Budgeted signed atom certificate. -/
def BlockPiPlusBooleanProjectedSignedCrossAtomRowCertificate
    {ι : Type*} [DecidableEq ι] (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
    S.length ≤ 0 ∧ m.totalDegree ≤ 0 ∧
      blockPiPlusInvAlgHom ι
          (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
        mlProj (m * blockIterDerivList S p)

/-- Unconditional signed cross-block certificate. -/
theorem blockPiPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (c : ℚ) (bi bj : Bool) :
    BlockPiPlusBooleanProjectedSignedCrossAtomRowCertificate
      (blockSignedCrossAtom c i j bi bj) := by
  refine ⟨[], 1, by simp, by simp, ?_⟩
  exact blockPiPlus_booleanProjected_signedCrossAtom_pullback_zeroDerivativeRow
    (hij := hij) c bi bj

/-! ## Axiom audit anchors -/

#print axioms blockBooleanNormalize_blockPiPlusAlgHom_mul_signed_distinct_blocks
#print axioms blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_signed_distinct_blocks
#print axioms blockPiPlusInvAlgHom_booleanProjected_signedCrossAtom_distinct_blocks
#print axioms mlProj_blockSignedCrossAtom
#print axioms blockPiPlus_booleanProjected_signedCrossAtom_pullback_zeroDerivativeRow
#print axioms blockPiPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
