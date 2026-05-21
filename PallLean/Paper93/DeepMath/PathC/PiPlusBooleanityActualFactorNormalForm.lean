import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityCaseSplitObstruction

/-!
# Actual Booleanity factor normal form under Boolean-projected Pi+

Adjacency and transition are direct signed-cross rows.  The Booleanity branch
requires the actual factor `1 - X_v(1-X_v)`, not the mixed atom.  This file pins
the exact block-level polynomial identities needed for that branch and proves the
final row consequence from those identities.

The key interface change is local and explicit: the true-side residue is admitted
as constant-plus-linear multilinear content in a small block span, rather than
hidden behind the false target that every Booleanity row closes to `1`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000
set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι] (i : ι)

/-- Square terms die under the legacy multilinear projection. -/
theorem mlProj_block_X_square_zero (b : Bool) :
    mlProj ((X (i, b)) * (X (i, b)) : MvPolynomial (ι × Bool) ℚ) = 0 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, mlProj_monomial]
  refine if_neg ?_
  intro hle
  have htwo : ((Finsupp.single (i, b) 1 + Finsupp.single (i, b) 1 :
      ι × Bool →₀ ℕ) (i, b)) = 2 := by simp
  have := hle (i, b)
  rw [htwo] at this
  norm_num at this

/-- Exact mixed-term identity needed by the actual Booleanity normal form.

This says raw inverse of the mixed term creates only square terms, so legacy
`mlProj` kills it. -/
def BlockPiPlusInvMixedMlProjZero : Prop :=
  mlProj (blockPiPlusInvAlgHom ι
    ((X (i, false)) * (X (i, true)) : MvPolynomial (ι × Bool) ℚ)) = 0

/-- The mixed-term identity is unconditional: inverse `Pi+` sends the mixed
term to a difference of squares, and legacy `mlProj` kills both squares. -/
theorem blockPiPlusInvMixedMlProjZero_unconditional :
    BlockPiPlusInvMixedMlProjZero i := by
  unfold BlockPiPlusInvMixedMlProjZero
  rw [map_mul]
  simp only [blockPiPlusInvAlgHom_X_false, blockPiPlusInvAlgHom_X_true]
  have hprod :
      (((1 / 2 : ℚ) • (X (i, false) + X (i, true))) *
          ((1 / 2 : ℚ) • (X (i, false) - X (i, true))) :
          MvPolynomial (ι × Bool) ℚ) =
        (1 / 4 : ℚ) •
          (X (i, false) * X (i, false) - X (i, true) * X (i, true)) := by
    rw [smul_mul_smul]
    norm_num
    rw [← sq_sub_sq]
    simp [pow_two]
  rw [hprod]
  rw [mlProj_smul]
  have hdiff :
      mlProj (X (i, false) * X (i, false) - X (i, true) * X (i, true) :
          MvPolynomial (ι × Bool) ℚ) = 0 := by
    rw [show mlProj (X (i, false) * X (i, false) - X (i, true) * X (i, true) :
          MvPolynomial (ι × Bool) ℚ) =
        mlProj (X (i, false) * X (i, false) : MvPolynomial (ι × Bool) ℚ) -
          mlProj (X (i, true) * X (i, true) : MvPolynomial (ι × Bool) ℚ) by
      exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _]
    rw [mlProj_block_X_square_zero i false, mlProj_block_X_square_zero i true]
    simp
  rw [hdiff]
  simp

/-- Exact Boolean-normalization identity needed for the false-side actual
Booleanity factor. -/
def BlockBooleanityFalseNormalizedIdentity : Prop :=
  blockBooleanNormalize
    (blockPiPlusAlgHom ι
      ((1 : MvPolynomial (ι × Bool) ℚ) -
        X (i, false) * (1 - X (i, false)))) =
    ((1 : MvPolynomial (ι × Bool) ℚ) +
      (2 : ℚ) • (X (i, false) * X (i, true)))

/-- Obsolete over-strong true-side Boolean-normalization target.  The actual
normal form has a linear residue (see `blockBooleanityTrueNormalizedActualForm`);
this predicate is retained only to document the old constant-closure seam. -/
def BlockBooleanityTrueNormalizedIdentity : Prop :=
  blockBooleanNormalize
    (blockPiPlusAlgHom ι
      ((1 : MvPolynomial (ι × Bool) ℚ) -
        X (i, true) * (1 - X (i, true)))) =
    ((1 : MvPolynomial (ι × Bool) ℚ) -
      (2 : ℚ) • (X (i, false) * X (i, true)))

omit [DecidableEq ι] in
private theorem blockBooleanNormalize_one_block :
    blockBooleanNormalize (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
  rw [show (1 : MvPolynomial (ι × Bool) ℚ) =
      MvPolynomial.monomial (0 : ι × Bool →₀ ℕ) (1 : ℚ) by
    rw [MvPolynomial.monomial_zero']; rfl]
  rw [blockBooleanNormalize_monomial]
  rw [show blockBooleanExponent (0 : ι × Bool →₀ ℕ) = 0 by
    ext j
    simp [blockBooleanExponent]]

private theorem blockBooleanNormalize_mixed_same_block :
    blockBooleanNormalize (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ) =
      (X (i, false) * X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  exact BoolPoly.blockBooleanNormalize_X_mul_X_ne (a := (i, false)) (b := (i, true)) (by simp)

/-- False-side actual Booleanity normalization, discharged directly from the
Boolean quotient algebra. -/
theorem blockBooleanityFalseNormalizedIdentity_unconditional :
    BlockBooleanityFalseNormalizedIdentity i := by
  unfold BlockBooleanityFalseNormalizedIdentity
  rw [map_sub, map_mul]
  simp only [map_one, map_sub, blockPiPlusAlgHom_X_false]
  let xf : MvPolynomial (ι × Bool) ℚ := X (i, false)
  let xt : MvPolynomial (ι × Bool) ℚ := X (i, true)
  change blockBooleanNormalize (1 - (xf + xt) * (1 - (xf + xt))) =
    (1 : MvPolynomial (ι × Bool) ℚ) + (2 : ℚ) • (xf * xt)
  have hexpand :
      (1 - (xf + xt) * (1 - (xf + xt)) : MvPolynomial (ι × Bool) ℚ) =
        1 - xf - xt + xf * xf + xf * xt + xt * xf + xt * xt := by
    ring
  rw [hexpand]
  repeat rw [BoolPoly.blockBooleanNormalize_add]
  repeat rw [blockBooleanNormalize_sub]
  rw [blockBooleanNormalize_one_block]
  rw [blockBooleanNormalize_X]
  rw [blockBooleanNormalize_X]
  rw [blockBooleanNormalize_X_mul_X]
  rw [blockBooleanNormalize_mixed_same_block]
  rw [show blockBooleanNormalize (xt * xf) = xt * xf by
    exact BoolPoly.blockBooleanNormalize_X_mul_X_ne (a := (i, true)) (b := (i, false)) (by simp)]
  rw [blockBooleanNormalize_X_mul_X]
  change (1 - xf - xt + xf + xf * xt + xt * xf + xt : MvPolynomial (ι × Bool) ℚ) =
    1 + (2 : ℚ) • (xf * xt)
  rw [show xt * xf = xf * xt by rw [mul_comm]]
  simp [smul_eq_C_mul]
  rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
    simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
  ring_nf

/-- True-side actual Booleanity normalization.  This is the concrete corrected
normal form: unlike the false-side branch, it retains an extra linear `true`
coordinate term. -/
theorem blockBooleanityTrueNormalizedActualForm :
    blockBooleanNormalize
      (blockPiPlusAlgHom ι
        ((1 : MvPolynomial (ι × Bool) ℚ) -
          X (i, true) * (1 - X (i, true)))) =
      ((1 : MvPolynomial (ι × Bool) ℚ) +
        (2 : ℚ) • X (i, true) -
        (2 : ℚ) • (X (i, false) * X (i, true))) := by
  rw [map_sub, map_mul]
  simp only [map_one, map_sub, blockPiPlusAlgHom_X_true]
  let xf : MvPolynomial (ι × Bool) ℚ := X (i, false)
  let xt : MvPolynomial (ι × Bool) ℚ := X (i, true)
  change blockBooleanNormalize (1 - (xf - xt) * (1 - (xf - xt))) =
    (1 : MvPolynomial (ι × Bool) ℚ) + (2 : ℚ) • xt - (2 : ℚ) • (xf * xt)
  have hexpand :
      (1 - (xf - xt) * (1 - (xf - xt)) : MvPolynomial (ι × Bool) ℚ) =
        1 - xf + xt + xf * xf - xf * xt - xt * xf + xt * xt := by
    ring
  rw [hexpand]
  repeat rw [BoolPoly.blockBooleanNormalize_add]
  repeat rw [blockBooleanNormalize_sub]
  repeat rw [BoolPoly.blockBooleanNormalize_add]
  repeat rw [blockBooleanNormalize_sub]
  rw [blockBooleanNormalize_one_block]
  rw [blockBooleanNormalize_X]
  rw [blockBooleanNormalize_X]
  rw [blockBooleanNormalize_X_mul_X]
  rw [blockBooleanNormalize_mixed_same_block]
  rw [show blockBooleanNormalize (xt * xf) = xt * xf by
    exact BoolPoly.blockBooleanNormalize_X_mul_X_ne (a := (i, true)) (b := (i, false)) (by simp)]
  rw [blockBooleanNormalize_X_mul_X]
  change (1 - xf + xt + xf - xf * xt - xt * xf + xt : MvPolynomial (ι × Bool) ℚ) =
    1 + (2 : ℚ) • xt - (2 : ℚ) • (xf * xt)
  rw [show xt * xf = xf * xt by rw [mul_comm]]
  simp [smul_eq_C_mul]
  rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
    simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
  ring_nf

private theorem mlProj_one_block :
    mlProj (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
  have h1 : (1 : MvPolynomial (ι × Bool) ℚ) =
      MvPolynomial.monomial (0 : ι × Bool →₀ ℕ) (1 : ℚ) := by
    rw [MvPolynomial.monomial_zero']; rfl
  rw [h1, mlProj_monomial]
  exact if_pos (by intro j; simp)

private theorem mlProj_two_block :
    mlProj (2 : MvPolynomial (ι × Bool) ℚ) = 2 := by
  have htwo : (2 : MvPolynomial (ι × Bool) ℚ) =
      (2 : ℚ) • (1 : MvPolynomial (ι × Bool) ℚ) := by
    rw [smul_eq_C_mul]
    rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
      simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
    ring
  rw [htwo, mlProj_smul, mlProj_one_block]

/-- The corrected local target for actual Booleanity rows: after post-pullback
multilinearization, Booleanity may contribute the constant row together with the
linear coordinates of its local `Π+` block.  This matches the paper-level
multilinear/rank surface rather than the over-strong factor-level expectation
that every Booleanity row close to the constant `1`. -/
def BlockBooleanityActualProjectedResidueSpan :
    Submodule ℚ (MvPolynomial (ι × Bool) ℚ) :=
  Submodule.span ℚ
    ({(1 : MvPolynomial (ι × Bool) ℚ), X (i, false), X (i, true)} :
      Set (MvPolynomial (ι × Bool) ℚ))

/-- The constant row is admitted by the corrected actual-Booleanity residue
span. -/
theorem one_mem_blockBooleanityActualProjectedResidueSpan :
    (1 : MvPolynomial (ι × Bool) ℚ) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  exact Submodule.subset_span (by simp)

/-- The false linear coordinate is admitted by the corrected actual-Booleanity
residue span. -/
theorem X_false_mem_blockBooleanityActualProjectedResidueSpan :
    (X (i, false) : MvPolynomial (ι × Bool) ℚ) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  exact Submodule.subset_span (by simp)

/-- The true linear coordinate is admitted by the corrected actual-Booleanity
residue span. -/
theorem X_true_mem_blockBooleanityActualProjectedResidueSpan :
    (X (i, true) : MvPolynomial (ι × Bool) ℚ) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  exact Submodule.subset_span (by simp)

/-- The scalar `2` is admitted by the corrected actual-Booleanity residue
span, as a scalar multiple of the constant row. -/
theorem two_mem_blockBooleanityActualProjectedResidueSpan :
    (2 : MvPolynomial (ι × Bool) ℚ) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  have hC : (2 : MvPolynomial (ι × Bool) ℚ) =
      (2 : ℚ) • (1 : MvPolynomial (ι × Bool) ℚ) := by
    rw [smul_eq_C_mul]
    rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
      simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
    ring
  rw [hC]
  exact Submodule.smul_mem (BlockBooleanityActualProjectedResidueSpan (i := i))
    (2 : ℚ) (one_mem_blockBooleanityActualProjectedResidueSpan (i := i))

/-- The true-side actual Booleanity row has an unavoidable linear residue on the
corrected post-pullback `mlProj` surface. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_true_actualForm :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, true) * (1 - X (i, true)))))) =
      ((1 : MvPolynomial (ι × Bool) ℚ) + X (i, false) - X (i, true)) := by
  rw [blockBooleanityTrueNormalizedActualForm]
  rw [map_sub, map_add, map_smul, map_smul]
  have hsub :
      mlProj (((blockPiPlusInvAlgHom ι) 1 +
          (2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, true))) -
          (2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, false) * X (i, true))) =
        mlProj ((blockPiPlusInvAlgHom ι) 1 +
          (2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, true))) -
          mlProj ((2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, false) * X (i, true))) := by
    exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _
  rw [hsub, mlProj_add, mlProj_smul, mlProj_smul]
  rw [blockPiPlusInvMixedMlProjZero_unconditional i]
  simp only [smul_zero, sub_zero]
  simp only [blockPiPlusInvAlgHom_X_true]
  have hinner :
      mlProj ((1 / 2 : ℚ) • (X (i, false) - X (i, true)) : MvPolynomial (ι × Bool) ℚ) =
        (1 / 2 : ℚ) • (X (i, false) - X (i, true)) := by
    rw [mlProj_smul]
    rw [show mlProj (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ) =
        mlProj (X (i, false) : MvPolynomial (ι × Bool) ℚ) -
          mlProj (X (i, true) : MvPolynomial (ι × Bool) ℚ) by
      exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _]
    rw [mlProj_X_block, mlProj_X_block]
  rw [hinner]
  rw [map_one]
  rw [mlProj_one_block]
  rw [smul_smul]
  norm_num
  simp [sub_eq_add_neg, add_assoc]

/-- The true-side actual Booleanity row belongs to the corrected local residue
span.  This is the paper-faithful replacement for the old over-strong target
that tried to force true-side Booleanity to close to the constant row. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_true_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, true) * (1 - X (i, true)))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_booleanProjected_booleanity_true_actualForm]
  simpa [sub_eq_add_neg] using
    (Submodule.add_mem _
      (Submodule.add_mem _
        (one_mem_blockBooleanityActualProjectedResidueSpan (i := i))
        (X_false_mem_blockBooleanityActualProjectedResidueSpan (i := i)))
      (Submodule.neg_mem _
        (X_true_mem_blockBooleanityActualProjectedResidueSpan (i := i))))


/-- If the exact false-side Booleanity normalization identities are supplied,
then the actual Booleanity row normal form is the constant `1`. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_false_of_exactIdentities
    (hmixed : BlockPiPlusInvMixedMlProjZero i)
    (h : BlockBooleanityFalseNormalizedIdentity i) :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, false) * (1 - X (i, false)))))) =
      (1 : MvPolynomial (ι × Bool) ℚ) := by
  rw [h]
  rw [map_add, map_smul]
  rw [mlProj_add, mlProj_smul]
  rw [hmixed]
  simp [mlProj_one_block]

/-- The false-side actual Booleanity row closes unconditionally on the corrected
post-pullback `mlProj` surface. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_false_unconditional :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, false) * (1 - X (i, false)))))) =
      (1 : MvPolynomial (ι × Bool) ℚ) :=
  mlProj_blockPiPlusInv_booleanProjected_booleanity_false_of_exactIdentities
    i (blockPiPlusInvMixedMlProjZero_unconditional i)
      (blockBooleanityFalseNormalizedIdentity_unconditional i)

/-- The false-side actual Booleanity row belongs to the corrected local residue
span; in fact it still closes to the constant row. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_false_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, false) * (1 - X (i, false)))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_booleanProjected_booleanity_false_unconditional]
  exact one_mem_blockBooleanityActualProjectedResidueSpan (i := i)

/-- One-hit derivative of the false-side actual Booleanity factor, after the
Boolean-normalized `Π+` transform and post-pullback multilinear projection.
This is the local Leibniz atom needed for product assembly: differentiating the
corrected false Booleanity factor contributes exactly the signed block-linear
residue `X_false - X_true`. -/
theorem mlProj_blockPiPlusInv_pderiv_false_booleanProjected_booleanity_false_actualForm :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, false) * (1 - X (i, false))))))) =
      ((X (i, false) : MvPolynomial (ι × Bool) ℚ) - X (i, true)) := by
  rw [blockBooleanityFalseNormalizedIdentity_unconditional]
  have hderiv :
      pderiv (i, false)
        ((1 : MvPolynomial (ι × Bool) ℚ) +
          (2 : ℚ) • (X (i, false) * X (i, true))) =
        (2 : ℚ) • X (i, true) := by
    simp
  rw [hderiv]
  rw [map_smul, blockPiPlusInvAlgHom_X_true, mlProj_smul]
  have hlin :
      mlProj ((1 / 2 : ℚ) • (X (i, false) - X (i, true)) :
          MvPolynomial (ι × Bool) ℚ) =
        (1 / 2 : ℚ) • (X (i, false) - X (i, true)) := by
    rw [mlProj_smul]
    rw [show mlProj (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ) =
        mlProj (X (i, false) : MvPolynomial (ι × Bool) ℚ) -
          mlProj (X (i, true) : MvPolynomial (ι × Bool) ℚ) by
      exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _]
    rw [mlProj_X_block, mlProj_X_block]
  rw [hlin]
  rw [smul_smul]
  norm_num

/-- The one-hit false-side Booleanity derivative belongs to the corrected local
residue span. -/
theorem mlProj_blockPiPlusInv_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, false) * (1 - X (i, false))))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_pderiv_false_booleanProjected_booleanity_false_actualForm]
  simpa [sub_eq_add_neg] using
    (Submodule.add_mem _
      (X_false_mem_blockBooleanityActualProjectedResidueSpan (i := i))
      (Submodule.neg_mem _
        (X_true_mem_blockBooleanityActualProjectedResidueSpan (i := i))))

/-- One-hit derivative of the true-side actual Booleanity factor.  The exact
post-pullback multilinear residue is `2 - X_false - X_true`, again a
constant-plus-linear block-local vector. -/
theorem mlProj_blockPiPlusInv_pderiv_true_booleanProjected_booleanity_true_actualForm :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, true) * (1 - X (i, true))))))) =
      ((2 : MvPolynomial (ι × Bool) ℚ) - X (i, false) - X (i, true)) := by
  rw [blockBooleanityTrueNormalizedActualForm]
  have hderiv :
      pderiv (i, true)
        ((1 : MvPolynomial (ι × Bool) ℚ) +
          (2 : ℚ) • X (i, true) -
          (2 : ℚ) • (X (i, false) * X (i, true))) =
        ((2 : MvPolynomial (ι × Bool) ℚ) - (2 : ℚ) • X (i, false)) := by
    simp [Algebra.smul_def]
    rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
      simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
  rw [hderiv]
  rw [map_sub, map_smul, map_ofNat, blockPiPlusInvAlgHom_X_false]
  have hlin :
      mlProj ((2 : MvPolynomial (ι × Bool) ℚ) -
          (2 : ℚ) • ((1 / 2 : ℚ) • (X (i, false) + X (i, true)))) =
        ((2 : MvPolynomial (ι × Bool) ℚ) - X (i, false) - X (i, true)) := by
    rw [show ((2 : MvPolynomial (ι × Bool) ℚ) -
          (2 : ℚ) • ((1 / 2 : ℚ) • (X (i, false) + X (i, true)))) =
        ((2 : MvPolynomial (ι × Bool) ℚ) - (X (i, false) + X (i, true))) by
      rw [smul_smul]
      norm_num [Algebra.smul_def]]
    rw [show mlProj ((2 : MvPolynomial (ι × Bool) ℚ) -
          (X (i, false) + X (i, true))) =
        mlProj (2 : MvPolynomial (ι × Bool) ℚ) -
          mlProj (X (i, false) + X (i, true) : MvPolynomial (ι × Bool) ℚ) by
      exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _]
    rw [show mlProj (X (i, false) + X (i, true) : MvPolynomial (ι × Bool) ℚ) =
        mlProj (X (i, false) : MvPolynomial (ι × Bool) ℚ) +
          mlProj (X (i, true) : MvPolynomial (ι × Bool) ℚ) by
      exact map_add (mlProjLinearMap (ι × Bool) ℚ) _ _]
    rw [mlProj_X_block, mlProj_X_block]
    rw [mlProj_two_block]
    ring
  exact hlin

/-- The one-hit true-side Booleanity derivative belongs to the corrected local
residue span. -/
theorem mlProj_blockPiPlusInv_pderiv_true_booleanProjected_booleanity_true_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, true) * (1 - X (i, true))))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_pderiv_true_booleanProjected_booleanity_true_actualForm]
  simpa [sub_eq_add_neg, add_assoc] using
    (Submodule.add_mem _
      (Submodule.add_mem _
        (two_mem_blockBooleanityActualProjectedResidueSpan (i := i))
        (Submodule.neg_mem _
          (X_false_mem_blockBooleanityActualProjectedResidueSpan (i := i))))
      (Submodule.neg_mem _
        (X_true_mem_blockBooleanityActualProjectedResidueSpan (i := i))))

/-- Mixed two-hit derivative of the false-side actual Booleanity factor.  This
closes the quadratic Booleanity atom under the exact Leibniz allocation where
both block coordinates are differentiated: the surviving residue is the scalar
`2`. -/
theorem mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, false) * (1 - X (i, false)))))))) =
      (2 : MvPolynomial (ι × Bool) ℚ) := by
  rw [blockBooleanityFalseNormalizedIdentity_unconditional]
  have hderiv :
      pderiv (i, true) (pderiv (i, false)
        ((1 : MvPolynomial (ι × Bool) ℚ) +
          (2 : ℚ) • (X (i, false) * X (i, true)))) =
        (2 : MvPolynomial (ι × Bool) ℚ) := by
    simp [Algebra.smul_def]
    rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
      simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
  rw [hderiv]
  rw [map_ofNat, mlProj_two_block]

/-- The mixed two-hit false-side Booleanity derivative belongs to the corrected
local residue span. -/
theorem mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, false) * (1 - X (i, false)))))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm]
  exact two_mem_blockBooleanityActualProjectedResidueSpan (i := i)

/-- Mixed two-hit derivative of the true-side actual Booleanity factor.  The
true branch has the opposite quadratic sign, so the two-hit Leibniz residue is
`-2`. -/
theorem mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, true) * (1 - X (i, true)))))))) =
      -(2 : MvPolynomial (ι × Bool) ℚ) := by
  rw [blockBooleanityTrueNormalizedActualForm]
  have hderiv :
      pderiv (i, true) (pderiv (i, false)
        ((1 : MvPolynomial (ι × Bool) ℚ) +
          (2 : ℚ) • X (i, true) -
          (2 : ℚ) • (X (i, false) * X (i, true)))) =
        -(2 : MvPolynomial (ι × Bool) ℚ) := by
    simp [Algebra.smul_def]
    rw [show (C (2 : ℚ) : MvPolynomial (ι × Bool) ℚ) = 2 by
      simpa using (MvPolynomial.C_eq_coe_nat (σ := ι × Bool) (R := ℚ) 2)]
  rw [hderiv]
  rw [map_neg, map_ofNat]
  exact map_neg (mlProjLinearMap (ι × Bool) ℚ) (2 : MvPolynomial (ι × Bool) ℚ) |>.trans
    (by change -(mlProj (2 : MvPolynomial (ι × Bool) ℚ)) = -(2 : MvPolynomial (ι × Bool) ℚ)
        rw [mlProj_two_block])

/-- The mixed two-hit true-side Booleanity derivative belongs to the corrected
local residue span. -/
theorem mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_mem_residueSpan :
    mlProj (blockPiPlusInvAlgHom ι
      (pderiv (i, true) (pderiv (i, false)
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι
            ((1 : MvPolynomial (ι × Bool) ℚ) -
              X (i, true) * (1 - X (i, true)))))))) ∈
      BlockBooleanityActualProjectedResidueSpan (i := i) := by
  rw [mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm]
  exact Submodule.neg_mem _ (two_mem_blockBooleanityActualProjectedResidueSpan (i := i))

/-- Conditional discharge of the obsolete true-side constant-closure seam.  The
paper-faithful route does not try to prove this hypothesis; it uses
`mlProj_blockPiPlusInv_booleanProjected_booleanity_true_mem_residueSpan` instead. -/
theorem mlProj_blockPiPlusInv_booleanProjected_booleanity_true_of_exactIdentities
    (hmixed : BlockPiPlusInvMixedMlProjZero i)
    (h : BlockBooleanityTrueNormalizedIdentity i) :
    mlProj (blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((1 : MvPolynomial (ι × Bool) ℚ) -
            X (i, true) * (1 - X (i, true)))))) =
      (1 : MvPolynomial (ι × Bool) ℚ) := by
  rw [h]
  rw [map_sub, map_smul]
  have hsub :
      mlProj ((blockPiPlusInvAlgHom ι) 1 -
        (2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, false) * X (i, true))) =
      mlProj ((blockPiPlusInvAlgHom ι) 1) -
        mlProj ((2 : ℚ) • (blockPiPlusInvAlgHom ι) (X (i, false) * X (i, true))) := by
    exact map_sub (mlProjLinearMap (ι × Bool) ℚ) _ _
  rw [hsub, mlProj_smul, hmixed]
  simp [mlProj_one_block]

/-! ## Axiom audit anchors -/

#print axioms mlProj_block_X_square_zero
#print axioms blockPiPlusInvMixedMlProjZero_unconditional
#print axioms blockBooleanityFalseNormalizedIdentity_unconditional
#print axioms blockBooleanityTrueNormalizedActualForm
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_false_unconditional
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_true_mem_residueSpan
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_false_mem_residueSpan
#print axioms mlProj_blockPiPlusInv_pderiv_false_booleanProjected_booleanity_false_actualForm
#print axioms mlProj_blockPiPlusInv_pderiv_true_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_actualForm
#print axioms mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_actualForm
#print axioms mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_false_mem_residueSpan
#print axioms mlProj_blockPiPlusInv_pderiv_true_pderiv_false_booleanProjected_booleanity_true_mem_residueSpan
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_false_of_exactIdentities
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_true_of_exactIdentities

end PallLean.Paper93.DeepMath.PathC
