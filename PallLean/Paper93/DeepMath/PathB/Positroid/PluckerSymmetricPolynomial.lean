import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem sym_poly_e1 (a b c : ℝ) : a + b + c - (a + b + c) = 0 := by ring

theorem sym_poly_e2 (a b c : ℝ) : a*b + a*c + b*c - (a*b + a*c + b*c) = 0 := by ring

theorem sym_poly_e3 (a b c : ℝ) : a*b*c - a*b*c = 0 := by ring

theorem newton_p1_e1 (a b c : ℝ) :
    a + b + c = a + b + c := rfl

theorem newton_p2_e1 (a b c : ℝ) :
    a^2 + b^2 + c^2 = (a+b+c)^2 - 2*(a*b + b*c + a*c) := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid
