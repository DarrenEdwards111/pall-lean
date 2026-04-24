import PallLean.Paper93.DeepMath.NFrame.Subgradient

namespace PallLean.Paper93.DeepMath.NFrame

/-- At `x = 0`, both `0` and `1` are in the subgradient of `max 0 ·`.
    (In fact the full subgradient is `[0, 1]`, but we only prove these two endpoints here.) -/
theorem zero_mem_subgradient_max_at_zero :
    (0 : ℝ) ∈ subgradient (fun y => max (0 : ℝ) y) 0 := by
  intro y
  show max (0 : ℝ) 0 + 0 * (y - 0) ≤ max 0 y
  rw [show max (0 : ℝ) 0 = 0 from by simp, zero_mul, add_zero]
  exact le_max_left _ _

theorem one_mem_subgradient_max_at_zero :
    (1 : ℝ) ∈ subgradient (fun y => max (0 : ℝ) y) 0 := by
  intro y
  simp only [sub_zero, one_mul]
  rw [show max 0 (0:ℝ) = 0 from by simp]
  rw [zero_add]
  exact le_max_right _ _

/-- Any `t ∈ [0, 1]` is in the subgradient of `max 0 ·` at 0. -/
theorem convex_subgradient_max_at_zero (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ∈ subgradient (fun y => max (0 : ℝ) y) 0 := by
  intro y
  simp only [sub_zero]
  rw [show max 0 (0:ℝ) = 0 from by simp]
  rw [zero_add]
  -- need: t * y ≤ max 0 y
  rcases le_or_gt (0 : ℝ) y with hy | hy
  · -- y ≥ 0: max 0 y = y, need t * y ≤ y, which holds since t ≤ 1 and y ≥ 0
    rw [max_eq_right hy]
    nlinarith
  · -- y < 0: max 0 y = 0, need t * y ≤ 0, which holds since t ≥ 0 and y < 0
    rw [max_eq_left hy.le]
    exact mul_nonpos_of_nonneg_of_nonpos h0 hy.le

end PallLean.Paper93.DeepMath.NFrame
