import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice

namespace PallLean.Paper93.Paper283

/-- Sign function: sgn x = 1 if x > 0, -1 if x < 0, 0 otherwise. -/
noncomputable def sgn (x : ℝ) : ℝ := if x > 0 then 1 else if x < 0 then -1 else 0

theorem sgn_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  unfold sgn
  split_ifs with h1
  · rfl
  · exact absurd h h1

theorem sgn_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  unfold sgn
  split_ifs with h1
  · linarith
  · rfl

theorem sgn_zero : sgn 0 = 0 := by
  unfold sgn
  split_ifs with h1
  · linarith
  · linarith

/-- Positive part (·)_+ = max(·, 0). -/
noncomputable def posPart (x : ℝ) : ℝ := max x 0

theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := le_max_right _ _
theorem posPart_zero : posPart 0 = 0 := by simp [posPart]

end PallLean.Paper93.Paper283
