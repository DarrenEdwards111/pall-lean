import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Adjugate of identity and diagonal matrices (N-Frame)

Thin Mathlib wrappers specialised to real square matrices indexed by `Fin n`:

* `adjugate_one` — `adj(I) = I`.
* `adjugate_diagonal_isDiag` — for a diagonal matrix `diagonal d`, the adjugate is again
  diagonal with entries `∏ j ∈ Finset.univ \ {i}, d j`.

Both wrap Mathlib lemmas (`Matrix.adjugate_one`, `Matrix.adjugate_diagonal`).  The
diagonal version is restated using the set-difference notation `Finset.univ \ {i}` (which
agrees with `Finset.univ.erase i` via `Finset.sdiff_singleton_eq_erase`).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Adjugate of the identity matrix is the identity. -/
theorem adjugate_one {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).adjugate = 1 :=
  Matrix.adjugate_one

/-- For a diagonal matrix `diagonal d`, the adjugate is again diagonal, with
    `(adj (diagonal d)) i i = ∏ j ∈ Finset.univ \ {i}, d j`. -/
theorem adjugate_diagonal_isDiag {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal d).adjugate
      = Matrix.diagonal (fun i => ∏ j ∈ Finset.univ \ ({i} : Finset (Fin n)), d j) := by
  rw [Matrix.adjugate_diagonal d]
  congr 1
  funext i
  rw [Finset.sdiff_singleton_eq_erase]

end PallLean.Paper93.DeepMath.NFrame
