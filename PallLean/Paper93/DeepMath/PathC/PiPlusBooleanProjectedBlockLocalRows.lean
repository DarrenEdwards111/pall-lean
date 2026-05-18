import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedPaperScaleRoute

/-!
# Block-local Boolean-projected Pi+ row calculus

This file starts discharging the actual Boolean-ambient local algebra behind the
paper-scale Route-C socket.  The earlier two-variable calculation showed why
same-window raw pullback is false and why the `(1,0)` window is necessary.  Here
we lift that calculation from `Fin 2` to an arbitrary `Pi+` block `ι × Bool`.

The key statement is that the Boolean-projected image of the mixed block
monomial `X(i,false) * X(i,true)`, pulled back by the inverse half-Hadamard
transform, is exactly a one-derivative source row.  This is the local atom that
the compiled/windowed Cook--Levin row theorem must assemble globally.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP

attribute [local instance] Classical.dec

variable {ι : Type*} (i : ι)

/-- Generic iterated derivative list for arbitrary variable types.  The global
`SPDP.iterDerivList` is specialized to `Fin n`; this local version lets the
block-coordinate calculation stay polymorphic in `ι`. -/
noncomputable def blockIterDerivList {σ : Type*}
    (indices : List σ) (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-- Boolean quotient exponent for an arbitrary variable type.  This is the same
monomial-basis operation as `zeroProfileBooleanExponent`, but stated for block
coordinates `ι × Bool` rather than only `Fin n`. -/
noncomputable def blockBooleanExponent {σ : Type*}
    (α : σ →₀ ℕ) : σ →₀ ℕ :=
  α.support.sum (fun i => Finsupp.single i 1)

/-- Boolean quotient normalization for arbitrary block-coordinate variables. -/
noncomputable def blockBooleanNormalizeLinearMap {σ : Type*} :
    MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  Finsupp.lmapDomain ℚ ℚ (blockBooleanExponent (σ := σ))

/-- Boolean quotient normalization as an operation. -/
noncomputable def blockBooleanNormalize {σ : Type*}
    (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  blockBooleanNormalizeLinearMap p

@[simp] theorem blockBooleanExponent_single_pos {σ : Type*}
    (i : σ) {k : ℕ} (hk : k ≠ 0) :
    blockBooleanExponent (Finsupp.single i k) =
      Finsupp.single i 1 := by
  classical
  rw [blockBooleanExponent, Finsupp.support_single_ne_zero i hk]
  simp

@[simp] theorem blockBooleanNormalize_monomial {σ : Type*}
    (α : σ →₀ ℕ) (c : ℚ) :
    blockBooleanNormalize (MvPolynomial.monomial α c) =
      MvPolynomial.monomial (blockBooleanExponent α) c := by
  change
    (Finsupp.lmapDomain ℚ ℚ (blockBooleanExponent (σ := σ)))
        (AddMonoidAlgebra.lsingle α c) =
      AddMonoidAlgebra.lsingle (blockBooleanExponent α) c
  rw [Finsupp.lmapDomain_apply, AddMonoidAlgebra.lsingle_apply,
    Finsupp.mapDomain_single]
  simp [AddMonoidAlgebra.lsingle_apply]

@[simp] theorem blockBooleanNormalize_X {σ : Type*} (i : σ) :
    blockBooleanNormalize (MvPolynomial.X i : MvPolynomial σ ℚ) =
      MvPolynomial.X i := by
  rw [MvPolynomial.X]
  simp

/-- Block Boolean normalization sends a square monomial to its singleton
representative: the quotient relation `Xᵢ² = Xᵢ`. -/
theorem blockBooleanNormalize_X_mul_X {σ : Type*} [DecidableEq σ] (i : σ) :
    blockBooleanNormalize
        (MvPolynomial.X i * MvPolynomial.X i : MvPolynomial σ ℚ) =
      MvPolynomial.X i := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul]
  have hpow :
      (Finsupp.single i 1 + Finsupp.single i 1 : σ →₀ ℕ) =
        Finsupp.single i 2 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne hji]
  rw [hpow]
  simp

/-- Block Boolean normalization is linear over subtraction. -/
theorem blockBooleanNormalize_sub {σ : Type*}
    (p q : MvPolynomial σ ℚ) :
    blockBooleanNormalize (p - q) =
      blockBooleanNormalize p - blockBooleanNormalize q := by
  exact map_sub blockBooleanNormalizeLinearMap p q

/-- Boolean normalization repairs the quadratic leakage of one block-local
mixed monomial under `Pi+`: in the Boolean quotient, the image is the linear
difference of the two coordinates. -/
theorem blockBooleanNormalize_blockPiPlusAlgHom_mixed
    [DecidableEq ι] :
    blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, false)) * (X (i, true)) : MvPolynomial (ι × Bool) ℚ)) =
      (X (i, false) - X (i, true) : MvPolynomial (ι × Bool) ℚ) := by
  simp
  have hmul :
      ((X (i, false) + X (i, true)) * (X (i, false) - X (i, true)) :
          MvPolynomial (ι × Bool) ℚ) =
        X (i, false) * X (i, false) - X (i, true) * X (i, true) := by
    ring
  rw [hmul, blockBooleanNormalize_sub]
  rw [blockBooleanNormalize_X_mul_X, blockBooleanNormalize_X_mul_X]

/-- The inverse half-Hadamard sends the repaired local difference back to the
`true` coordinate. -/
theorem blockPiPlusInvAlgHom_sub_same_block
    [DecidableEq ι] :
    blockPiPlusInvAlgHom ι
      ((X (i, false) - X (i, true)) : MvPolynomial (ι × Bool) ℚ) =
      X (i, true) := by
  simp [sub_eq_add_neg]
  module

/-- Block-local Boolean-projected pullback of the mixed monomial.  This is the
arbitrary-block version of `piPlusHadamard2InvGauge_booleanProjected_pair`. -/
theorem blockPiPlusInvAlgHom_booleanProjected_mixed
    [DecidableEq ι] :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, false)) * (X (i, true)) : MvPolynomial (ι × Bool) ℚ))) =
      X (i, true) := by
  rw [blockBooleanNormalize_blockPiPlusAlgHom_mixed i]
  exact blockPiPlusInvAlgHom_sub_same_block i

/-- A singleton variable is already multilinear, so `mlProj` fixes it. -/
theorem mlProj_X_block {σ : Type*} [DecidableEq σ]
    (j : σ) :
    mlProj (MvPolynomial.X j : MvPolynomial σ ℚ) = MvPolynomial.X j := by
  rw [MvPolynomial.X, mlProj_monomial]
  refine if_pos ?_
  intro k
  by_cases hk : k = j
  · subst k
    simp
  · rw [Finsupp.single_eq_of_ne hk]
    exact Nat.zero_le 1

/-- The same local pullback is exactly a one-derivative source row.  This is the
block-local `(extraK, extraL) = (1,0)` row-transport atom. -/
theorem blockPiPlus_booleanProjected_mixed_pullback_oneDerivativeRow
    [DecidableEq ι] :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, false)) * (X (i, true)) : MvPolynomial (ι × Bool) ℚ))) =
      mlProj
        ((1 : MvPolynomial (ι × Bool) ℚ) *
          pderiv (i, false)
            (((X (i, false)) * (X (i, true))) :
              MvPolynomial (ι × Bool) ℚ)) := by
  rw [blockPiPlusInvAlgHom_booleanProjected_mixed i]
  have hderiv :
      pderiv (i, false)
        (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) =
        X (i, true) := by
    simp
  rw [hderiv]
  simp [mlProj_X_block]

/-- Same atom in the actual row-certificate language: the source row is the
SPDP generator with derivative list `[(i,false)]` and multiplier `1`. -/
theorem blockPiPlus_booleanProjected_mixed_pullback_iterDerivRow
    [DecidableEq ι] :
    blockPiPlusInvAlgHom ι
      (blockBooleanNormalize
        (blockPiPlusAlgHom ι
          ((X (i, false)) * (X (i, true)) : MvPolynomial (ι × Bool) ℚ))) =
      mlProj
        ((1 : MvPolynomial (ι × Bool) ℚ) *
          blockIterDerivList [(i, false)]
            (((X (i, false)) * (X (i, true))) :
              MvPolynomial (ι × Bool) ℚ)) := by
  simpa [blockIterDerivList]
    using blockPiPlus_booleanProjected_mixed_pullback_oneDerivativeRow (i := i)

/-! ## Axiom audit anchors -/

#print axioms blockBooleanNormalize_blockPiPlusAlgHom_mixed
#print axioms blockPiPlusInvAlgHom_sub_same_block
#print axioms blockPiPlusInvAlgHom_booleanProjected_mixed
#print axioms blockPiPlus_booleanProjected_mixed_pullback_oneDerivativeRow
#print axioms blockPiPlus_booleanProjected_mixed_pullback_iterDerivRow

end PallLean.Paper93.DeepMath.PathC
