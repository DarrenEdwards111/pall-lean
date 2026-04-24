import PallLean.Paper93.DeepMath.NFrame.DetFinTwoGrad
import Mathlib.Data.Matrix.Basis

/-!
# Partial derivatives of the 2×2 determinant (N-Frame)

For a real 2×2 matrix `A`, the determinant depends on each of the four
entries linearly (fixing the other three). This file records the
"partial derivative in the `(0,0)` direction" identity in finite
difference form:

  `det (A + Matrix.single 0 0 δ) - det A = δ * A 1 1`.

Combined with `Matrix.det_fin_two`, this gives the explicit slope of
`det` in the `A 0 0` coordinate at any fixed matrix `A`.

We also record the closed-form specialisation

  `det !![a, b; c, d] = a * d - b * c`

for later reuse downstream.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Closed-form 2×2 determinant: `det !![a, b; c, d] = a * d - b * c`.

This is the `Matrix.det_fin_two` specialisation pinned to the literal
matrix notation. It lets downstream proofs access the determinant of a
concretely given 2×2 matrix without first rewriting via the generic
`Matrix.det_fin_two`. -/
theorem det_fin_two_partial_entry_00
    (a b c d : ℝ) :
    let A := !![a, b; c, d]
    A.det = a * d - b * c := by
  intro A
  exact Matrix.det_fin_two A

/-- Partial derivative of 2×2 determinant in the `(0,0)` direction in
finite-difference form. For a 2×2 real matrix `A` and a scalar `δ`,

  `det (A + Matrix.single 0 0 δ) - det A = δ * A 1 1`.

This is the linear (slope) behaviour of `det` in the `A 0 0` entry. -/
theorem det_fin_two_diff_in_entry_00
    (A : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) :
    (A + Matrix.single 0 0 δ).det - A.det = δ * A 1 1 := by
  -- Expand both determinants via `Matrix.det_fin_two`.
  rw [Matrix.det_fin_two (A + Matrix.single 0 0 δ), Matrix.det_fin_two A]
  -- Evaluate the entry-wise sums. The perturbation `single 0 0 δ`
  -- is `δ` at `(0,0)` and `0` everywhere else.
  have h00 : ((A + Matrix.single 0 0 δ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = A 0 0 + δ := by
    rw [Matrix.add_apply]
    simp
  have h01 : ((A + Matrix.single 0 0 δ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = A 0 1 := by
    rw [Matrix.add_apply]
    simp
  have h10 : ((A + Matrix.single 0 0 δ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = A 1 0 := by
    rw [Matrix.add_apply]
    simp
  have h11 : ((A + Matrix.single 0 0 δ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = A 1 1 := by
    rw [Matrix.add_apply]
    simp
  rw [h00, h01, h10, h11]
  ring

end PallLean.Paper93.DeepMath.NFrame
