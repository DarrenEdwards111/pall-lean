import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Jacobi formula for 1×1 matrices (N-Frame)

For a `1 × 1` matrix `A` over `ℝ`, the determinant is `det A = A 0 0`, so
the Jacobi formula `d(det A) = adj(A)ᵀ : dA` degenerates to the trivial
statement `∂ det / ∂ A₀₀ = 1`. We package several equivalent formulations:

* `det_fin_one_as_identity` — `Matrix.det` on `Matrix (Fin 1) (Fin 1) ℝ`
  coincides with the single-entry evaluation `fun A => A 0 0`.
* `adjugate_fin_one` — the adjugate of a `1 × 1` matrix is the identity
  matrix `1`.
* `adjugate_fin_one_entry` — the unique cofactor entry is `1`.
* `det_fin_one_linear_map_val` — `det` is affine-linear in the entry:
  `(A + ΔA).det - A.det = ΔA 0 0`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For 1×1 matrices, `det A = A 0 0`, so the Jacobi formula is trivial:
    `∂/∂ A 0 0 (det) = 1`. More precisely, `det` evaluated on a `1 × 1`
    matrix is the identity projection onto the single entry `A 0 0`. -/
theorem det_fin_one_as_identity :
    (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) = (fun A => A 0 0) := by
  funext A
  exact Matrix.det_fin_one A

/-- The cofactor / adjugate of a 1×1 matrix is the identity 1×1 matrix. -/
theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.adjugate = 1 :=
  Matrix.adjugate_fin_one A

/-- For 1×1 matrices, `(A.adjugate) 0 0 = 1` — the single cofactor entry. -/
theorem adjugate_fin_one_entry (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.adjugate 0 0 = 1 := by
  rw [adjugate_fin_one]
  simp

/-- Jacobi formula, linearised form: for 1×1 matrices, `det` is affine-linear
    in the entry, with directional increment `ΔA 0 0`. This is the concrete
    manifestation of `d(det A) = adj(A)ᵀ : dA = 1 · ΔA 0 0` when `n = 1`. -/
theorem det_fin_one_linear_map_val (A ΔA : Matrix (Fin 1) (Fin 1) ℝ) :
    (A + ΔA).det - A.det = ΔA 0 0 := by
  rw [Matrix.det_fin_one (A + ΔA), Matrix.det_fin_one A]
  simp [Matrix.add_apply]

end PallLean.Paper93.DeepMath.NFrame
