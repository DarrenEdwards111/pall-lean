import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem plucker_6x12_swap (a b : ℝ) :
    a * b - b * a = 0 := by ring

theorem plucker_6x12_6fold_zero (a b c d e f : ℝ) :
    a * b * c * d * e * f - f * e * d * c * b * a = 0 := by ring

theorem plucker_6x12_polynomial_id (a b c d e f g h : ℝ) :
    (a + b + c) * (d + e + f + g + h) - (a + b + c) * d - (a + b + c) * e
    - (a + b + c) * f - (a + b + c) * g - (a + b + c) * h = 0 := by ring

theorem plucker_6x12_distrib (a b c d e f : ℝ) :
    a * (b + c + d + e + f) = a*b + a*c + a*d + a*e + a*f := by ring

theorem plucker_6x12_3x3_subdet_id (a b c d e f g h i : ℝ) :
    a * (e*i - f*h) - b * (d*i - f*g) + c * (d*h - e*g) =
    a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g := by ring

end PallLean.Paper93.DeepMath.PathB.Positroid
