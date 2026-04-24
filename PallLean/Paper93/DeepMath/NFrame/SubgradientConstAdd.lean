import PallLean.Paper93.DeepMath.NFrame.Subgradient

namespace PallLean.Paper93.DeepMath.NFrame

/-- Adding a constant to `f` doesn't change the subgradient. -/
theorem subgradient_add_const (f : ℝ → ℝ) (c x : ℝ) :
    subgradient (fun y => f y + c) x = subgradient f x := by
  ext v
  simp only [subgradient, Set.mem_setOf_eq]
  constructor
  · intro h y
    have := h y
    linarith
  · intro h y
    have := h y
    linarith

/-- Scaling `f` by `c ≥ 0` scales the subgradient by `c`. -/
theorem subgradient_smul_nonneg (f : ℝ → ℝ) (c x v : ℝ) (hc : 0 ≤ c) :
    v ∈ subgradient f x → c * v ∈ subgradient (fun y => c * f y) x := by
  intro h y
  have h_y := h y
  -- h_y : f x + v * (y - x) ≤ f y
  -- goal : c * f x + (c * v) * (y - x) ≤ c * f y
  nlinarith [h_y]

end PallLean.Paper93.DeepMath.NFrame
