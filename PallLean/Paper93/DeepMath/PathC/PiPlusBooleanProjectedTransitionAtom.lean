import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAdjacencyAtom

/-!
# Boolean-projected transition atom certificate for Pi+

This is the coefficient-weighted analogue of the local adjacency atom.  A
transition skeleton factor has shape

`1 - c * X(i,false) * X(j,false)`

for a scalar coefficient `c`.  Since the transformed cross-block quadratic is
already Boolean-normal and Boolean normalization is linear, the coefficient does
not change the argument: Boolean-projected `Pi+` pulls the atom back to the
original source factor, hence it is a zero-derivative source row.
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

/-- Boolean normalization commutes with rational scalar multiplication. -/
theorem blockBooleanNormalize_smul {σ : Type*}
    (c : ℚ) (p : MvPolynomial σ ℚ) :
    blockBooleanNormalize (c • p) = c • blockBooleanNormalize p := by
  exact map_smul blockBooleanNormalizeLinearMap c p

/-- Scalar-multiple form of the cross-block adjacency normalization theorem. -/
theorem blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_false_false_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : ℚ) :
    blockBooleanNormalize
        (c • blockPiPlusAlgHom ι
          ((X (i, false)) * (X (j, false)) : MvPolynomial (ι × Bool) ℚ)) =
      c • blockPiPlusAlgHom ι
          ((X (i, false)) * (X (j, false)) : MvPolynomial (ι × Bool) ℚ) := by
  rw [blockBooleanNormalize_smul]
  rw [blockBooleanNormalize_blockPiPlusAlgHom_mul_false_false_distinct_blocks
    (hij := hij)]

/-- Local false/false transition atom over two distinct `Pi+` blocks. -/
noncomputable def blockTransitionAtomFF {ι : Type*}
    (c : ℚ) (i j : ι) : MvPolynomial (ι × Bool) ℚ :=
  (1 : MvPolynomial (ι × Bool) ℚ) -
    c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)

/-- The Boolean-projected `Pi+` pullback fixes a coefficient-weighted transition
atom whose endpoints belong to distinct `Pi+` blocks. -/
theorem blockPiPlusInvAlgHom_booleanProjected_transitionAtomFF_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : ℚ) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockTransitionAtomFF c i j))) =
      blockTransitionAtomFF c i j := by
  unfold blockTransitionAtomFF
  rw [map_sub, map_one, map_smul, blockBooleanNormalize_sub]
  have hone : blockBooleanNormalize (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.C 1 by rfl]
    rw [MvPolynomial.C_apply, blockBooleanNormalize_monomial]
    rfl
  rw [hone]
  rw [blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_false_false_distinct_blocks
    (hij := hij)]
  have hpre :
      (1 : MvPolynomial (ι × Bool) ℚ) -
          c • blockPiPlusAlgHom ι (X (i, false) * X (j, false)) =
        blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)) := by
    rw [map_sub, map_one, map_smul]
  rw [hpre]
  exact
    congrArg (fun f : MvPolynomial (ι × Bool) ℚ →ₐ[ℚ]
        MvPolynomial (ι × Bool) ℚ =>
      f ((1 : MvPolynomial (ι × Bool) ℚ) -
        c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)))
      (blockPiPlusInv_comp_blockPiPlus ι)

/-- The transition atom is multilinear, so `mlProj` fixes it. -/
theorem mlProj_blockTransitionAtomFF
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : ℚ) :
    mlProj (blockTransitionAtomFF c i j : MvPolynomial (ι × Bool) ℚ) =
      blockTransitionAtomFF c i j := by
  unfold blockTransitionAtomFF
  have hmul :
      mlProj (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ) =
        (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ) := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, mlProj_monomial]
    have hsquarefree : Finsupp.IsMultilinear
        (Finsupp.single (i, false) 1 + Finsupp.single (j, false) 1 : ι × Bool →₀ ℕ) := by
      intro x
      by_cases hxi : x = (i, false)
      · subst x
        simp [hij]
      · by_cases hxj : x = (j, false)
        · subst x
          simp [hxi]
        · simp [hxi, hxj]
    rw [if_pos hsquarefree]
  rw [sub_eq_add_neg]
  rw [mlProj_add]
  have hone : mlProj (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.monomial 0 1 by rfl,
      mlProj_monomial]
    have h0 : Finsupp.IsMultilinear (0 : ι × Bool →₀ ℕ) := by
      intro x
      simp
    rw [if_pos h0]
  have hneg :
      mlProj (-(c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ))) =
        -(c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)) := by
    rw [← neg_one_smul ℚ (c • (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)),
      mlProj_smul, mlProj_smul, hmul]
  rw [hone, hneg]

/-- The transition atom as a zero-extra-derivative row certificate. -/
theorem blockPiPlus_booleanProjected_transitionAtomFF_pullback_zeroDerivativeRow
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : ℚ) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockTransitionAtomFF c i j))) =
      mlProj
        ((1 : MvPolynomial (ι × Bool) ℚ) *
          blockIterDerivList [] (blockTransitionAtomFF c i j)) := by
  rw [blockPiPlusInvAlgHom_booleanProjected_transitionAtomFF_distinct_blocks
    (hij := hij)]
  simp [blockIterDerivList]
  exact (mlProj_blockTransitionAtomFF (hij := hij) c).symm

/-- Budgeted local transition certificate.  This is also a `(0,0)` row and hence
fits the paper's one-window `(1,0)` budget. -/
def BlockPiPlusBooleanProjectedTransitionAtomRowCertificate
    {ι : Type*} [DecidableEq ι] (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
    S.length ≤ 0 ∧ m.totalDegree ≤ 0 ∧
      blockPiPlusInvAlgHom ι
          (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
        mlProj (m * blockIterDerivList S p)

/-- Unconditional local transition certificate for two distinct `Pi+` blocks. -/
theorem blockPiPlusBooleanProjectedTransitionAtomRowCertificate_unconditional
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : ℚ) :
    BlockPiPlusBooleanProjectedTransitionAtomRowCertificate
      (blockTransitionAtomFF c i j) := by
  refine ⟨[], 1, by simp, by simp, ?_⟩
  exact blockPiPlus_booleanProjected_transitionAtomFF_pullback_zeroDerivativeRow
    (hij := hij) c

/-! ## Axiom audit anchors -/

#print axioms blockBooleanNormalize_smul
#print axioms blockBooleanNormalize_smul_blockPiPlusAlgHom_mul_false_false_distinct_blocks
#print axioms blockPiPlusInvAlgHom_booleanProjected_transitionAtomFF_distinct_blocks
#print axioms mlProj_blockTransitionAtomFF
#print axioms blockPiPlus_booleanProjected_transitionAtomFF_pullback_zeroDerivativeRow
#print axioms blockPiPlusBooleanProjectedTransitionAtomRowCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
