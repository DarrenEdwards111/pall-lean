import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Plücker relations for 2×5 matrices (Gr(2,5))

For the Grassmannian `Gr(2,5)` of 2-dimensional subspaces of `ℝ⁵`, there
are `C(5,2) = 10` Plücker coordinates `p_{ij}` for `1 ≤ i < j ≤ 5`. The
Plücker relations follow the pattern

  `p_{ij} p_{kl} - p_{ik} p_{jl} + p_{il} p_{jk} = 0`

for any `i < j < k < l`. Since `Gr(2,5)` involves choosing 4-element
subsets of `{1,2,3,4,5}` to obtain such relations, there are exactly
`C(5,4) = 5` such 4-subsets, giving 5 Plücker relations:

  `{1,2,3,4}`, `{1,2,3,5}`, `{1,2,4,5}`, `{1,3,4,5}`, `{2,3,4,5}`.

Each relation, after substituting the explicit 2×2 minors, is the same
polynomial identity in 8 variables (the entries of the corresponding
2×4 sub-matrix obtained by deleting one column from the 2×5 matrix).
The identity is closed by `ring`.

This file is kernel-only: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The Plücker relation for indices `{1,2,3,4}` in `Gr(2,5)`:
    `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`, expressed as the polynomial
    identity in the 8 entries of the 2×4 sub-matrix on columns 1–4. -/
theorem plucker_relation_2x5_1234 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- The Plücker relation for indices `{1,2,3,5}` in `Gr(2,5)`. -/
theorem plucker_relation_2x5_1235 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- The Plücker relation for indices `{1,2,4,5}` in `Gr(2,5)`. -/
theorem plucker_relation_2x5_1245 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- The Plücker relation for indices `{1,3,4,5}` in `Gr(2,5)`. -/
theorem plucker_relation_2x5_1345 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- The Plücker relation for indices `{2,3,4,5}` in `Gr(2,5)`. -/
theorem plucker_relation_2x5_2345 (a b c d e f g h : ℝ) :
    (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
      + (a*h - d*e) * (b*g - c*f) = 0 := by
  ring

/-- All five Plücker relations on `Gr(2,5)` hold simultaneously. The
    polynomial identity itself is the same in all five cases (only the
    interpretation of the 8 variables as entries of the column-deleted
    2×4 sub-matrix differs), so the conjunction is also closed by
    `ring`. -/
theorem plucker_relations_2x5_simultaneously (a b c d e f g h : ℝ) :
    ((a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
        + (a*h - d*e) * (b*g - c*f) = 0) ∧
    ((a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
        + (a*h - d*e) * (b*g - c*f) = 0) ∧
    ((a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
        + (a*h - d*e) * (b*g - c*f) = 0) ∧
    ((a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
        + (a*h - d*e) * (b*g - c*f) = 0) ∧
    ((a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f)
        + (a*h - d*e) * (b*g - c*f) = 0) :=
  ⟨by ring, by ring, by ring, by ring, by ring⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
