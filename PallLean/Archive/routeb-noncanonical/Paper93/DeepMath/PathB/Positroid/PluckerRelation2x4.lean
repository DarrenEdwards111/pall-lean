import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# The fundamental Plücker relation for 2×4 matrices

This file proves the simplest non-trivial Plücker relation:
for a 2×4 matrix with entries `a, b, c, d, e, f, g, h` (row by row), the
2×2 minors over column pairs satisfy the quadratic identity

  `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`,

where `pᵢⱼ` is the determinant of the submatrix on columns `i, j`.
This is the only Plücker relation defining the Grassmannian `Gr(2,4)`
inside `ℙ⁵` and is the foundational example for positroid geometry.

The relation is a polynomial identity in the eight matrix entries, so
the proof is just `ring`. Two corollaries verify the relation on
explicit positroid-cell representatives.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The fundamental Plücker relation for 2×4 matrices:
    `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`,
    expressed as a polynomial identity in the 8 entries of the matrix.

    Here, for a matrix with rows `(a, b, c, d)` and `(e, f, g, h)`, the
    2×2 column-pair minors are
    `p₁₂ = a*f - b*e`, `p₁₃ = a*g - c*e`, `p₁₄ = a*h - d*e`,
    `p₂₃ = b*g - c*f`, `p₂₄ = b*h - d*f`, `p₃₄ = c*h - d*g`. -/
theorem plucker_relation_2x4 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- The Plücker coordinates of the 2×4 matrix `[[1,0,0,0],[0,1,0,0]]`:
    `p₁₂ = 1, p₁₃ = 0, p₁₄ = 0, p₂₃ = 0, p₂₄ = 0, p₃₄ = 0`.
    The relation reduces to `1*0 - 0*0 + 0*0 = 0`. -/
theorem plucker_relation_2x4_canonical_basis :
    let p₁₂ : ℝ := 1; let p₁₃ : ℝ := 0; let p₁₄ : ℝ := 0;
    let p₂₃ : ℝ := 0; let p₂₄ : ℝ := 0; let p₃₄ : ℝ := 0;
    p₁₂ * p₃₄ - p₁₃ * p₂₄ + p₁₄ * p₂₃ = 0 := by
  simp

/-- For the 2×4 matrix `[[1,1,0,0],[0,0,1,1]]` (a positroid cell representative):
    `p₁₂ = 0, p₁₃ = 1, p₁₄ = 1, p₂₃ = 1, p₂₄ = 1, p₃₄ = 0`.
    The Plücker relation: `0*0 - 1*1 + 1*1 = 0`. -/
theorem plucker_relation_2x4_positroid_example :
    let p₁₂ : ℝ := 0; let p₁₃ : ℝ := 1; let p₁₄ : ℝ := 1;
    let p₂₃ : ℝ := 1; let p₂₄ : ℝ := 1; let p₃₄ : ℝ := 0;
    p₁₂ * p₃₄ - p₁₃ * p₂₄ + p₁₄ * p₂₃ = 0 := by
  simp

end PallLean.Paper93.DeepMath.PathB.Positroid
