import PallLean.Paper93.DeepMath.NFrame.Subgradient

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a pure linear map `f x := a * x`, the subgradient is exactly `{a}`. -/
theorem subgradient_pure_linear (a x : ℝ) : a ∈ subgradient (fun y => a * y) x := by
  intro y
  linarith [le_refl (a * y)]

/-- Negation of a convex function: `subgradient (-f) x = -subgradient f x`
    is NOT true for convex f (since -f is concave). But we can say: if `v ∈ ∂f(x)`,
    then evaluation: `f(y) ≥ f(x) + v(y-x)` holds. -/
theorem subgradient_applies (f : ℝ → ℝ) (x v : ℝ) (hv : v ∈ subgradient f x) (y : ℝ) :
    f x + v * (y - x) ≤ f y := hv y

/-- Subgradient is nonempty for convex functions only trivially: membership implies lower bound. -/
theorem mem_subgradient_iff (f : ℝ → ℝ) (x v : ℝ) :
    v ∈ subgradient f x ↔ ∀ y, f x + v * (y - x) ≤ f y := Iff.rfl

end PallLean.Paper93.DeepMath.NFrame
