import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN

/-!
# Concrete examples of principal-TNN matrices

This file collects a handful of concrete principal-TNN examples that arise
repeatedly in the §7.1 amplituhedron / positroid material. Each example is
obtained by specialising `diagonal_nonneg_isPrincipalTNN` from
`DiagonalNonnegTNN.lean` to a fixed dimension and a tuple of non-negative
diagonal entries.

These small fixed-dimension instances are convenient for downstream files
that want a literal principal-TNN witness without re-deriving the diagonal
case each time.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The 1×1 zero matrix is principal-TNN. -/
theorem zero_1x1_isPrincipalTNN :
    IsPrincipalTNN (Matrix.diagonal (![0] : Fin 1 → ℝ)) := by
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  fin_cases i
  · exact le_refl 0

/-- For c ≥ 0, the 1×1 matrix `Matrix.diagonal ![c]` is principal-TNN. -/
theorem diag_1x1_nonneg_isPrincipalTNN (c : ℝ) (hc : 0 ≤ c) :
    IsPrincipalTNN (Matrix.diagonal (![c] : Fin 1 → ℝ)) := by
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  fin_cases i
  · exact hc

/-- For a, b, c ≥ 0, the 3×3 diagonal matrix `diagonal ![a, b, c]` is principal-TNN. -/
theorem diag_3x3_nonneg_isPrincipalTNN (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IsPrincipalTNN (Matrix.diagonal (![a, b, c] : Fin 3 → ℝ)) := by
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- For a, b, c, d ≥ 0, the 4×4 diagonal matrix is principal-TNN. -/
theorem diag_4x4_nonneg_isPrincipalTNN (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPrincipalTNN (Matrix.diagonal (![a, b, c, d] : Fin 4 → ℝ)) := by
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd

end PallLean.Paper93.DeepMath.PathB.Positroid
