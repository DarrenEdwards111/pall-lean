import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterScaffold
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterIsotropicMinimization

/-!
# Route C ⇒ Route A wiring: general position ⇒ tight-frame realization

This file connects the *analytic* isotropic-position existence theorem
`ForsterIsotropic.exists_isotropic` (proved unconditionally in
`ComputationalDepthForsterIsotropicMinimization.lean`, matrix form) to the
*combinatorial* `Forster.IsTightFrame` interface of
`ComputationalDepthForsterScaffold.lean` (Euclidean-space form), which feeds
`Forster.forster_bound_of_tightFrame`.

The bridge is genuine, not a socket:

* `exists_isotropic` returns a matrix `T` with `Tᵀ = T`, `T * T = S`,
  `IsUnit T.det` and the matrix tight-frame identity
  `∑ᵢ (n i • T *ᵥ vᵢ)(n i • T *ᵥ vᵢ)ᵀ = (m/d)·I` with `n i = ⟪vᵢ, S vᵢ⟫^{-1/2}`.

* `T` is promoted to a `LinearEquiv` on `EuclideanSpace ℝ (Fin d)`; because
  `T * T = S` the Euclidean norm `‖T_E (R.u i)‖` equals the matrix
  normaliser `√⟪vᵢ, S vᵢ⟫`, so the two normalisations coincide *exactly* —
  this is why the matrix tight frame transfers to the quadratic-form tight
  frame `∑ᵢ ⟪ûᵢ, y⟫² = (m/d)‖y‖²` with no fudge factor.

The **hypothesis is general position** (`GenPos`), not mere spanning: the
scaffold's own `not_isotropicKernel_as_stated` shows the spanning-only kernel
is false, and the duplicate-row counterexample (`v₁ = e₁, v₂ = e₂, v₃ = e₁`)
has no isotropic position.  So this discharges the *corrected* obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterWiring

open scoped BigOperators Matrix RealInnerProductSpace
open Forster ForsterIsotropic Matrix

variable {m' d n : ℕ}

/-- **General position** of a unit realization: every `d`-tuple of the row
vectors is linearly independent, i.e. the square submatrix they form is
invertible.  This is exactly the hypothesis `exists_isotropic` needs, and it is
strictly stronger than `Spans` (which is insufficient: `not_isotropicKernel_as_stated`). -/
def GenPos {M : Fin (m' + 1) → Fin n → Bool} (R : UnitRealization M d) : Prop :=
  ∀ e : Fin d → Fin (m' + 1), Function.Injective e →
    IsUnit (Matrix.of (fun i k => (R.u (e k)) i) : Matrix (Fin d) (Fin d) ℝ).det

/-- General position (with at least `d` vectors available) forces the row
vectors to span the ambient space `Fin d → ℝ`: any invertible `d × d`
submatrix has columns that already span, and those columns lie in the range. -/
theorem span_of_genPos {M : Fin (m' + 1) → Fin n → Bool} (_hd : 0 < d) (hdm' : d ≤ m')
    (R : UnitRealization M d) (hgp : GenPos R) :
    Submodule.span ℝ (Set.range (fun i => (R.u i : Fin d → ℝ))) = ⊤ := by
  -- the standard inclusion `Fin d ↪ Fin (m'+1)`
  have hlt : ∀ k : Fin d, (k : ℕ) < m' + 1 := fun k => lt_of_lt_of_le k.2 (by omega)
  let e : Fin d → Fin (m' + 1) := fun k => ⟨(k : ℕ), hlt k⟩
  have he : Function.Injective e := by
    intro a b hab
    have h : a.val = b.val := congrArg (fun x : Fin (m' + 1) => x.val) hab
    exact Fin.ext h
  have hB := hgp e he
  set B : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i k => (R.u (e k)) i) with hBdef
  haveI : Invertible B := B.invertibleOfIsUnitDet hB
  -- columns of `B` are precisely the vectors `R.u (e k)`
  have hcolsub : Set.range B.col ⊆ Set.range (fun i => (R.u i : Fin d → ℝ)) := by
    rintro z ⟨k, rfl⟩
    refine ⟨e k, ?_⟩
    funext i
    rw [Matrix.col_apply, hBdef, Matrix.of_apply]
  -- invertibility ⇒ the columns span everything
  have htop : Submodule.span ℝ (Set.range B.col) = (⊤ : Submodule ℝ (Fin d → ℝ)) := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    intro y
    refine ⟨B⁻¹ *ᵥ y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hB,
      Matrix.one_mulVec]
  have : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤
      Submodule.span ℝ (Set.range (fun i => (R.u i : Fin d → ℝ))) := by
    rw [← htop]; exact Submodule.span_mono hcolsub
  exact top_le_iff.mp this

/-- **Wiring theorem (Route C ⇒ Route A, truncated level).**  A unit realization
in *general position* can be replaced by a tight-frame realization of the same
dimension.  This discharges the (corrected, general-position) isotropic-position
obligation that `Forster.forster_bound_of_tightFrame` consumes — combining the
unconditional analytic existence `exists_isotropic` with the Euclidean/matrix
inner-product dictionary. -/
theorem isTightFrame_of_genPos {M : Fin (m' + 1) → Fin n → Bool} (hd : 0 < d)
    (hdm' : d ≤ m') (R : UnitRealization M d) (hgp : GenPos R) :
    ∃ R' : UnitRealization M d, IsTightFrame R' := by
  -- underlying row vectors, viewed in `Fin d → ℝ`
  let v : Fin (m' + 1) → (Fin d → ℝ) := fun i => R.u i
  have hune : ∀ i, R.u i ≠ 0 := by
    intro i h
    have := R.u_unit i
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  have hne : ∀ i, v i ≠ 0 := by
    intro i h
    apply hune i
    have hv0 : (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) (R.u i) = 0 := h
    exact (LinearEquiv.map_eq_zero_iff _).mp hv0
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := span_of_genPos hd hdm' R hgp
  -- the analytic isotropic-position theorem (matrix form), now exposing `T*T = S`
  obtain ⟨S, T, hSpd, hTsymm, hTT, hTunit, hTframe⟩ :=
    exists_isotropic hd hdm' hne hspan hgp
  -- promote the matrix `T` to a linear automorphism of `EuclideanSpace ℝ (Fin d)`
  haveI : Invertible T := T.invertibleOfIsUnitDet hTunit
  let φ : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) := WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  let T_E : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    φ.trans ((T.toLinearEquiv' inferInstance).trans φ.symm)
  -- componentwise `T_E x = T *ᵥ x`
  have hTEapp : ∀ (x : EuclideanSpace ℝ (Fin d)) (c : Fin d),
      (T_E x) c = (T *ᵥ (fun j => x j)) c := by
    intro x c
    simp only [T_E, φ, LinearEquiv.trans_apply, WithLp.coe_linearEquiv,
      WithLp.coe_symm_linearEquiv]
    rfl
  -- the matrix normaliser equals the Euclidean norm of `T_E (R.u i)`
  have hnormSq : ∀ i, (T *ᵥ v i) ⬝ᵥ (T *ᵥ v i) = v i ⬝ᵥ (S *ᵥ v i) := by
    intro i
    rw [dotProduct_mulVec, ← mulVec_transpose, hTsymm, mulVec_mulVec, hTT, dotProduct_comm]
  have hTEnorm : ∀ i, ‖T_E (R.u i)‖ ^ 2 = v i ⬝ᵥ (S *ᵥ v i) := by
    intro i
    rw [eucl_normSq_eq_sum, ← hnormSq i]
    show ∑ c, ((T_E (R.u i)) c) ^ 2 = (T *ᵥ v i) ⬝ᵥ (T *ᵥ v i)
    simp only [dotProduct, sq]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hTEapp (R.u i) c]
  -- nonvanishing of the transformed vectors
  have hqpos : ∀ i, 0 < v i ⬝ᵥ (S *ᵥ v i) := fun i => quadForm_pos hSpd (hne i)
  have hTEpos : ∀ i, 0 < ‖T_E (R.u i)‖ := by
    intro i
    have h2 : (0 : ℝ) < ‖T_E (R.u i)‖ ^ 2 := by rw [hTEnorm i]; exact hqpos i
    nlinarith [norm_nonneg (T_E (R.u i)), h2]
  -- the inverse-norm normaliser coincides with the matrix one `(√⟪vᵢ,Svᵢ⟫)⁻¹`
  have hnorminv : ∀ i, (‖T_E (R.u i)‖)⁻¹ = (Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ := by
    intro i
    congr 1
    rw [← hTEnorm i, Real.sqrt_sq (le_of_lt (hTEpos i))]
  -- adjoint construction for the `w`-side, preserving inner products (hence signs)
  set Sadj : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearMap.adjoint (T_E.symm : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    with hSadjdef
  have hTS : ∀ x y, (⟪T_E x, Sadj y⟫ : ℝ) = ⟪x, y⟫ := by
    intro x y
    rw [hSadjdef, LinearMap.adjoint_inner_right]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hSinj : ∀ y, Sadj y = 0 → y = 0 := by
    intro y hy
    have hxy : ∀ x, (⟪x, y⟫ : ℝ) = 0 := by
      intro x
      have hx := hTS x y
      rw [hy, inner_zero_right] at hx
      exact hx.symm
    exact inner_self_eq_zero.mp (hxy y)
  have hRwne : ∀ j, R.w j ≠ 0 := by
    intro j h; have := R.w_unit j; rw [h, norm_zero] at this; exact one_ne_zero this.symm
  have hSwne : ∀ j, 0 < ‖Sadj (R.w j)‖ := fun j => by
    rw [norm_pos_iff]; exact fun h => hRwne j (hSinj _ h)
  -- assemble the tight-frame realization
  refine ⟨{
      u := fun i => (‖T_E (R.u i)‖)⁻¹ • T_E (R.u i)
      w := fun j => (‖Sadj (R.w j)‖)⁻¹ • Sadj (R.w j)
      u_unit := ?_
      w_unit := ?_
      sign_ok := ?_ }, ?_⟩
  · intro i
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hTEpos i),
      inv_mul_cancel₀ (ne_of_gt (hTEpos i))]
  · intro j
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hSwne j),
      inv_mul_cancel₀ (ne_of_gt (hSwne j))]
  · intro i j
    rw [real_inner_smul_left, real_inner_smul_right, hTS]
    have hpos : 0 < (‖T_E (R.u i)‖)⁻¹ * ((‖Sadj (R.w j)‖)⁻¹) :=
      mul_pos (inv_pos.mpr (hTEpos i)) (inv_pos.mpr (hSwne j))
    have := R.sign_ok i j
    nlinarith [this, hpos]
  -- the tight-frame identity, transferred from the matrix identity `hTframe`
  · intro y
    -- the unit frame vectors, in matrix form
    set û : Fin (m' + 1) → (Fin d → ℝ) :=
      fun i => (Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i) with hûdef
    -- each Euclidean inner product is the matrix dot product `û i ⬝ᵥ y`
    have hinner : ∀ i, (⟪(‖T_E (R.u i)‖)⁻¹ • T_E (R.u i), y⟫ : ℝ) = (û i) ⬝ᵥ (fun c => y c) := by
      intro i
      rw [real_inner_smul_left, eucl_inner_eq_sum, hnorminv i, hûdef]
      simp only [dotProduct, Finset.mul_sum, hTEapp (R.u i), Pi.smul_apply, smul_eq_mul,
        mul_assoc]
      exact Finset.sum_congr rfl (fun x _ => rfl)
    -- square, then convert to a quadratic form via the outer-product identity
    have hsq : ∀ i, (⟪(‖T_E (R.u i)‖)⁻¹ • T_E (R.u i), y⟫ : ℝ) ^ 2
        = (fun c => y c) ⬝ᵥ (Matrix.vecMulVec (û i) (û i) *ᵥ (fun c => y c)) := by
      intro i
      rw [hinner i, sq, ← dotProduct_vecMulVec_mulVec (û i) (fun c => y c)]
    rw [Finset.sum_congr rfl (fun i _ => hsq i)]
    -- pull the sum inside the quadratic form, then apply the matrix tight frame
    rw [← dotProduct_sum]
    rw [show (∑ i, Matrix.vecMulVec (û i) (û i) *ᵥ (fun c => y c))
          = (∑ i, Matrix.vecMulVec (û i) (û i)) *ᵥ (fun c => y c) from
        (sum_mulVec _ _ _).symm]
    simp only [hûdef]
    rw [hTframe]
    rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    have hyy : (fun c => y c) ⬝ᵥ (fun c => y c) = ‖y‖ ^ 2 := by
      rw [eucl_normSq_eq_sum]
      simp only [dotProduct, sq]
    rw [hyy]

end PallLean.Paper93.DeepMath.PathB.ForsterWiring

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterWiring.isTightFrame_of_genPos
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterWiring.span_of_genPos
