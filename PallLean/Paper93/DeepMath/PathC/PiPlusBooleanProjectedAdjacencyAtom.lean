import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanNormalizedMixedAtomCertificate

/-!
# Boolean-projected adjacency atom certificate for Pi+

This is the first adjacency analogue of the repaired mixed-Booleanity atom.  For
an adjacency edge joining two distinct `Pi+` blocks, the transformed quadratic
expands into square-free cross-block monomials.  Boolean normalization therefore
leaves the transformed product unchanged, and the inverse `Pi+` pullback returns
the original adjacency factor as a zero-derivative source row.
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

/-- Boolean normalization fixes a square-free quadratic monomial. -/
theorem blockBooleanNormalize_X_mul_X_ne {σ : Type*} [DecidableEq σ]
    {a b : σ} (hab : a ≠ b) :
    blockBooleanNormalize
        (MvPolynomial.X a * MvPolynomial.X b : MvPolynomial σ ℚ) =
      (MvPolynomial.X a * MvPolynomial.X b : MvPolynomial σ ℚ) := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]
  simp only [blockBooleanNormalize_monomial]
  have hexp :
      blockBooleanExponent (Finsupp.single a 1 + Finsupp.single b 1 : σ →₀ ℕ) =
        (Finsupp.single a 1 + Finsupp.single b 1 : σ →₀ ℕ) := by
    unfold blockBooleanExponent
    rw [Finsupp.support_single_add_single hab (by norm_num) (by norm_num)]
    ext x
    by_cases hxa : x = a
    · subst x
      simp [hab]
    · by_cases hxb : x = b
      · subst x
        simp [hab, hxa]
      · simp [hxa, hxb]
  rw [hexp]

/-- Boolean normalization is linear over addition. -/
theorem blockBooleanNormalize_add {σ : Type*}
    (p q : MvPolynomial σ ℚ) :
    blockBooleanNormalize (p + q) =
      blockBooleanNormalize p + blockBooleanNormalize q := by
  exact map_add blockBooleanNormalizeLinearMap p q

/-- Local false/false adjacency atom over two distinct `Pi+` blocks.  The other
sign choices are the same calculation; this is the concrete adjacency skeleton
used as the first certificate. -/
noncomputable def blockAdjacencyAtomFF {ι : Type*}
    (i j : ι) : MvPolynomial (ι × Bool) ℚ :=
  (1 : MvPolynomial (ι × Bool) ℚ) - X (i, false) * X (j, false)

/-- The transformed cross-block false/false product is already Boolean-normal. -/
theorem blockBooleanNormalize_blockPiPlusAlgHom_mul_false_false_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, false)) * (X (j, false)) : MvPolynomial (ι × Bool) ℚ)) =
      blockPiPlusAlgHom ι
          ((X (i, false)) * (X (j, false)) : MvPolynomial (ι × Bool) ℚ) := by
  rw [map_mul]
  simp only [blockPiPlusAlgHom_X_false]
  have hprod :
      ((X (i, false) + X (i, true)) * (X (j, false) + X (j, true)) :
          MvPolynomial (ι × Bool) ℚ) =
        X (i, false) * X (j, false) + X (i, false) * X (j, true) +
          X (i, true) * X (j, false) + X (i, true) * X (j, true) := by
    ring
  rw [hprod]
  repeat rw [blockBooleanNormalize_add]
  have hff : (i, false) ≠ (j, false) := by
    intro h; exact hij (by injection h)
  have hft : (i, false) ≠ (j, true) := by
    intro h; exact hij (by injection h)
  have htf : (i, true) ≠ (j, false) := by
    intro h; exact hij (by injection h)
  have htt : (i, true) ≠ (j, true) := by
    intro h; exact hij (by injection h)
  rw [blockBooleanNormalize_X_mul_X_ne hff,
    blockBooleanNormalize_X_mul_X_ne hft,
    blockBooleanNormalize_X_mul_X_ne htf,
    blockBooleanNormalize_X_mul_X_ne htt]

/-- The Boolean-projected `Pi+` pullback fixes a false/false adjacency atom whose
endpoints belong to distinct `Pi+` blocks. -/
theorem blockPiPlusInvAlgHom_booleanProjected_adjacencyAtomFF_distinct_blocks
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockAdjacencyAtomFF i j))) =
      blockAdjacencyAtomFF i j := by
  unfold blockAdjacencyAtomFF
  rw [map_sub, map_one, blockBooleanNormalize_sub]
  have hone : blockBooleanNormalize (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
    rw [show (1 : MvPolynomial (ι × Bool) ℚ) = MvPolynomial.C 1 by rfl]
    rw [MvPolynomial.C_apply, blockBooleanNormalize_monomial]
    rfl
  rw [hone]
  rw [blockBooleanNormalize_blockPiPlusAlgHom_mul_false_false_distinct_blocks
    (hij := hij)]
  have hpre :
      (1 : MvPolynomial (ι × Bool) ℚ) -
          blockPiPlusAlgHom ι (X (i, false) * X (j, false)) =
        blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) - X (i, false) * X (j, false)) := by
    rw [map_sub, map_one]
  rw [hpre]
  exact
    congrArg (fun f : MvPolynomial (ι × Bool) ℚ →ₐ[ℚ]
        MvPolynomial (ι × Bool) ℚ =>
      f ((1 : MvPolynomial (ι × Bool) ℚ) - X (i, false) * X (j, false)))
      (blockPiPlusInv_comp_blockPiPlus ι)

/-- The adjacency atom is multilinear, so `mlProj` fixes it. -/
theorem mlProj_blockAdjacencyAtomFF
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    mlProj (blockAdjacencyAtomFF i j : MvPolynomial (ι × Bool) ℚ) =
      blockAdjacencyAtomFF i j := by
  unfold blockAdjacencyAtomFF
  have hmul :
      mlProj (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ) =
        (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ) := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, mlProj_monomial]
    have hsquarefree : ∀ x,
        (Finsupp.single (i, false) 1 + Finsupp.single (j, false) 1 : ι × Bool →₀ ℕ) x ≤ 1 := by
      intro x
      by_cases hxi : x = (i, false)
      · subst x
        simp [hij]
      · by_cases hxj : x = (j, false)
        · subst x
          simp [hxi]
        · simp [hxi, hxj]
    rw [if_pos (show Finsupp.IsMultilinear
      (Finsupp.single (i, false) 1 + Finsupp.single (j, false) 1 : ι × Bool →₀ ℕ) from hsquarefree)]
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
      mlProj (-(X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ)) =
        -(X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ) := by
    rw [← neg_one_smul ℚ (X (i, false) * X (j, false) : MvPolynomial (ι × Bool) ℚ),
      mlProj_smul, hmul]
  rw [hone, hneg]

/-- The same fixedness as a zero-extra-derivative row certificate. -/
theorem blockPiPlus_booleanProjected_adjacencyAtomFF_pullback_zeroDerivativeRow
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι (blockAdjacencyAtomFF i j))) =
      mlProj
        ((1 : MvPolynomial (ι × Bool) ℚ) *
          blockIterDerivList [] (blockAdjacencyAtomFF i j)) := by
  rw [blockPiPlusInvAlgHom_booleanProjected_adjacencyAtomFF_distinct_blocks
    (hij := hij)]
  simp [blockIterDerivList]
  exact (mlProj_blockAdjacencyAtomFF (hij := hij)).symm

/-- Budgeted local adjacency certificate.  It is a `(0,0)` row, hence fits the
paper's one-window `(1,0)` route. -/
def BlockPiPlusBooleanProjectedAdjacencyAtomRowCertificate
    {ι : Type*} [DecidableEq ι] (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
    S.length ≤ 0 ∧ m.totalDegree ≤ 0 ∧
      blockPiPlusInvAlgHom ι
          (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
        mlProj (m * blockIterDerivList S p)

/-- Unconditional local adjacency certificate for two distinct `Pi+` blocks. -/
theorem blockPiPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    BlockPiPlusBooleanProjectedAdjacencyAtomRowCertificate
      (blockAdjacencyAtomFF i j) := by
  refine ⟨[], 1, by simp, by simp, ?_⟩
  exact blockPiPlus_booleanProjected_adjacencyAtomFF_pullback_zeroDerivativeRow
    (hij := hij)

/-! ## Axiom audit anchors -/

#print axioms blockBooleanNormalize_X_mul_X_ne
#print axioms blockBooleanNormalize_blockPiPlusAlgHom_mul_false_false_distinct_blocks
#print axioms blockPiPlusInvAlgHom_booleanProjected_adjacencyAtomFF_distinct_blocks
#print axioms mlProj_blockAdjacencyAtomFF
#print axioms blockPiPlus_booleanProjected_adjacencyAtomFF_pullback_zeroDerivativeRow
#print axioms blockPiPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
