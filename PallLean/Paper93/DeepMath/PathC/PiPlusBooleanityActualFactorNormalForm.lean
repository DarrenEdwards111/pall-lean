import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityCaseSplitObstruction

/-!
# Actual Booleanity factor normal form under Boolean-projected Pi+

Adjacency and transition are direct signed-cross rows.  The Booleanity branch
requires the actual factor `1 - X_v(1-X_v)`, not the mixed atom.  This file pins
the exact block-level polynomial identities needed for that branch and proves the
final row consequence from those identities.

No payload shape is introduced: these are concrete polynomial equalities.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

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

/-- Exact Boolean-normalization identity needed for the false-side actual
Booleanity factor. -/
def BlockBooleanityFalseNormalizedIdentity : Prop :=
  blockBooleanNormalize
    (blockPiPlusAlgHom ι
      ((1 : MvPolynomial (ι × Bool) ℚ) -
        X (i, false) * (1 - X (i, false)))) =
    ((1 : MvPolynomial (ι × Bool) ℚ) +
      (2 : ℚ) • (X (i, false) * X (i, true)))

/-- Exact Boolean-normalization identity needed for the true-side actual
Booleanity factor. -/
def BlockBooleanityTrueNormalizedIdentity : Prop :=
  blockBooleanNormalize
    (blockPiPlusAlgHom ι
      ((1 : MvPolynomial (ι × Bool) ℚ) -
        X (i, true) * (1 - X (i, true)))) =
    ((1 : MvPolynomial (ι × Bool) ℚ) -
      (2 : ℚ) • (X (i, false) * X (i, true)))

private theorem mlProj_one_block :
    mlProj (1 : MvPolynomial (ι × Bool) ℚ) = 1 := by
  have h1 : (1 : MvPolynomial (ι × Bool) ℚ) =
      MvPolynomial.monomial (0 : ι × Bool →₀ ℕ) (1 : ℚ) := by
    rw [MvPolynomial.monomial_zero']; rfl
  rw [h1, mlProj_monomial]
  exact if_pos (by intro j; simp)

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

/-- If the exact true-side Booleanity normalization identities are supplied,
then the actual Booleanity row normal form is the constant `1`. -/
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
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_false_of_exactIdentities
#print axioms mlProj_blockPiPlusInv_booleanProjected_booleanity_true_of_exactIdentities

end PallLean.Paper93.DeepMath.PathC
