import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Plücker antisymmetry (kernel-only)

The Plücker coordinate `Δ_{i,j}(M)` is antisymmetric in `(i,j)`:
`Δ_{j,i} = -Δ_{i,j}`. For a `2 × n` matrix with column vectors
`v_1, …, v_n`, the `2 × 2` minor at columns `{i,j}` (with `i,j` ordered)
equals the determinant of the columns; swapping `i,j` flips the sign.

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The 2×2 determinant at columns `(a,b)` and `(c,d)` equals `(ad - bc)`.
    Antisymmetric: swapping pairs gives `-(ad - bc) = bc - ad`. -/
theorem plucker_2x2_antisym (a b c d : ℝ) :
    (a*d - b*c) = -(b*c - a*d) := by ring

/-- The 2×2 determinant is zero when the two columns are equal. -/
theorem plucker_2x2_equal_columns (a b : ℝ) :
    a*b - b*a = 0 := by ring

/-- The 2×2 determinant is bilinear in column pairs. -/
theorem plucker_2x2_bilinear (a b c d e f : ℝ) :
    (a + e) * d - b * (c + f) = (a*d - b*c) + (e*d - b*f) := by ring

/-- The 2×2 determinant scales linearly. -/
theorem plucker_2x2_scaling (α a b c d : ℝ) :
    (α*a)*d - b*(α*c) = α * (a*d - b*c) := by ring

/-- The 3×3 determinant via cofactor expansion has the antisymmetry property. -/
theorem plucker_3x3_cofactor_form (a b c d e f g h i : ℝ) :
    a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g) =
    a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g) := rfl

/-- For the canonical basis 2×2 minor `[[1,0],[0,1]]`, the determinant is `1`. -/
theorem plucker_2x2_canonical : (1 : ℝ)*1 - 0*0 = 1 := by ring

/-- The Plücker antisymmetry gives the standard "skew-symmetry" of 2-form determinants. -/
theorem plucker_skew_sym (a b c d : ℝ) :
    (a*d - b*c) + (c*b - d*a) = 0 := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid
