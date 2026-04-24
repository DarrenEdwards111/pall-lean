/-
  PallLean/Paper93/Paper283/PaddedMinorInverse.lean

  Paper §28.3 — Zero-padded extension of the inverse of a principal
  minor `A[J,J]` back to the ambient `N × N` matrix. Entries outside
  `J × J` are set to zero.

  This file provides:

    * `paddedMinorInverse`           : the zero-padded inverse;
    * `paddedMinorInverse_zero_outside`
      : entries with row index `i ∉ J` are zero;
    * `paddedMinorInverse_identity_zero`
      : when `J ≠ Finset.univ`, a concrete witness `(i, j)` with
        `paddedMinorInverse 1 J i j = 0`.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import PallLean.Paper93.Paper283.PrincipalMinor

namespace PallLean.Paper93.Paper283

open Matrix

/-- Zero-padded extension: given an inverse of `A[J,J]`, extend to
    `N × N` by zeros outside `J × J`. -/
noncomputable def paddedMinorInverse {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (J : Finset (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if hi : i ∈ J then
      if hj : j ∈ J then
        ((principalMinor A J)⁻¹) ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

/-- Entries of the zero-padded inverse with row index outside `J` are zero. -/
theorem paddedMinorInverse_zero_outside {N} (A : Matrix (Fin N) (Fin N) ℝ)
    (J : Finset (Fin N)) (i j : Fin N) (hi : i ∉ J) :
    paddedMinorInverse A J i j = 0 := by
  unfold paddedMinorInverse
  simp [hi]

/-- When `J ≠ Finset.univ`, the zero-padded inverse of the identity has
    at least one zero entry: pick any `i ∉ J` and any `j`. -/
theorem paddedMinorInverse_identity_zero {N : ℕ} (J : Finset (Fin N))
    (hJ : J ≠ Finset.univ) :
    ∃ i j, paddedMinorInverse (1 : Matrix (Fin N) (Fin N) ℝ) J i j = 0 := by
  -- Since `J ≠ Finset.univ`, there exists some `i ∈ Finset.univ \ J`,
  -- i.e.\ some `i : Fin N` with `i ∉ J`.
  have hne : (Finset.univ \ J).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hJ (Finset.univ_subset_iff.mp hsub)
  obtain ⟨i, hi_mem⟩ := hne
  have hi_notin : i ∉ J := (Finset.mem_sdiff.mp hi_mem).2
  -- Use the out-of-`J` zeroing lemma with any `j`; we use `i` itself
  -- (recall `Fin N` is nonempty since `i : Fin N`).
  refine ⟨i, i, ?_⟩
  exact paddedMinorInverse_zero_outside
    (1 : Matrix (Fin N) (Fin N) ℝ) J i i hi_notin

end PallLean.Paper93.Paper283
