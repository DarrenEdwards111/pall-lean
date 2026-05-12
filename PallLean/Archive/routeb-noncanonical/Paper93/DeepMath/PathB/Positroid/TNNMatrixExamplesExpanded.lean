import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem diag_5x5_pos_isPrincipalTP (a b c d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    IsPrincipalTP (Matrix.diagonal (![a, b, c, d, e] : Fin 5 → ℝ)) := by
  apply diagonal_pos_isPrincipalTP
  intro i
  fin_cases i <;> assumption

theorem diag_6x6_nonneg_isPrincipalTNN (a b c d e f : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    IsPrincipalTNN (Matrix.diagonal (![a, b, c, d, e, f] : Fin 6 → ℝ)) := by
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  fin_cases i <;> assumption

end PallLean.Paper93.DeepMath.PathB.Positroid
