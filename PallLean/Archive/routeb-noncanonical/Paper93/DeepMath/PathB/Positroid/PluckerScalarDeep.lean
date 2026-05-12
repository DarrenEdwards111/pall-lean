import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_scalar_deep_1 (a b c d : ℝ) :
    (a*c - b*d)^2 + (a*d + b*c)^2 = (a^2 + b^2)*(c^2 + d^2) := by ring

theorem plucker_scalar_deep_2 (a b c : ℝ) :
    a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c) * (a^2 + b^2 + c^2 - a*b - b*c - a*c) := by ring

theorem plucker_scalar_deep_3 (a b : ℝ) :
    a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4 = (a + b)^4 := by ring

theorem plucker_scalar_deep_4 (a b : ℝ) :
    (a + b)^6 = a^6 + 6*a^5*b + 15*a^4*b^2 + 20*a^3*b^3 + 15*a^2*b^4 + 6*a*b^5 + b^6 := by ring

theorem plucker_scalar_deep_5 (a b c : ℝ) :
    (a + b + c)^2 = a^2 + b^2 + c^2 + 2*(a*b + b*c + a*c) := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid
