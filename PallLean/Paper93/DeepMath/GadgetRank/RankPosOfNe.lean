import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Range

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- A nonzero matrix has rank at least `1`.

Derived from the fact that `Matrix.rank` is the `finrank` of the range of
`mulVecLin`: if the rank is `0`, the range collapses to `⊥`, so
`mulVecLin = 0`, which forces the matrix itself to vanish.  This is the
matrix analogue of `Matrix.rank_zero` (the converse direction). -/
theorem rank_pos_of_ne_zero {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (hM : M ≠ 0) :
    1 ≤ M.rank := by
  by_contra h
  push_neg at h
  -- `h : M.rank < 1`, hence `M.rank = 0`.
  have hzero : M.rank = 0 := Nat.lt_one_iff.mp h
  -- `M.rank` is definitionally `finrank ℝ (LinearMap.range M.mulVecLin)`.
  have hfinrank : Module.finrank ℝ (LinearMap.range M.mulVecLin) = 0 := hzero
  -- From `finrank = 0` of a submodule of a finite-dimensional space,
  -- conclude the submodule is `⊥`.
  have hrange_bot : LinearMap.range M.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := ℝ)]
    exact hfinrank
  -- `range = ⊥` for a linear map iff the linear map is `0`.
  have hmulVecLin_zero : M.mulVecLin = 0 :=
    LinearMap.range_eq_bot.mp hrange_bot
  -- Conclude `M = 0`: `M.mulVecLin` applied to the `j`-th standard basis
  -- vector recovers the `j`-th column of `M`; all columns are therefore zero.
  apply hM
  ext i j
  -- Evaluate the zero linear map hypothesis at `Pi.single j 1`.
  have hcol :
      M.mulVecLin (Pi.single j (1 : ℝ)) = 0 := by
    have := congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) =>
      f (Pi.single j (1 : ℝ))) hmulVecLin_zero
    simpa using this
  -- Translate `mulVecLin` to `mulVec` and evaluate at index `i`.
  have hmul : Matrix.mulVec M (Pi.single j (1 : ℝ)) = 0 := by
    have := hcol
    rw [Matrix.mulVecLin_apply] at this
    exact this
  have hij : (Matrix.mulVec M (Pi.single j (1 : ℝ))) i = 0 := by
    rw [hmul]; rfl
  -- `(M *ᵥ e_j) i = ∑ k, M i k * δ_{j,k} = M i j`.
  have hexpand :
      (Matrix.mulVec M (Pi.single j (1 : ℝ))) i = M i j := by
    unfold Matrix.mulVec
    unfold dotProduct
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have : Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ) k = 0 :=
        Pi.single_eq_of_ne hkj _
      rw [this]; ring
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  -- Combine to conclude `M i j = 0`.
  have : M i j = 0 := by
    rw [← hexpand]; exact hij
  simpa using this

end PallLean.Paper93.DeepMath.GadgetRank
