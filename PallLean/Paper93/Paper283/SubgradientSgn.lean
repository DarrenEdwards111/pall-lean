import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic

namespace PallLean.Paper93.Paper283

/-- Subgradient of sgn at x: set-valued. -/
noncomputable def subgradientSgn (x : ℝ) : Set ℝ :=
  if x > 0 then {1}
  else if x < 0 then {-1}
  else Set.Icc (-1 : ℝ) 1

theorem subgradientSgn_pos {x : ℝ} (hx : 0 < x) :
    subgradientSgn x = {1} := by
  unfold subgradientSgn
  simp [hx]

theorem subgradientSgn_neg {x : ℝ} (hx : x < 0) :
    subgradientSgn x = {-1} := by
  unfold subgradientSgn
  have h1 : ¬ x > 0 := by linarith
  have h2 : x < 0 := hx
  simp [h1, h2]

theorem subgradientSgn_zero : subgradientSgn 0 = Set.Icc (-1 : ℝ) 1 := by
  unfold subgradientSgn
  simp

theorem subgradientSgn_nonempty (x : ℝ) : (subgradientSgn x).Nonempty := by
  unfold subgradientSgn
  split_ifs
  · exact ⟨1, rfl⟩
  · exact ⟨-1, rfl⟩
  · exact ⟨0, by simp [Set.mem_Icc]⟩

end PallLean.Paper93.Paper283
