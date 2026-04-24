import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Convex-analytic subgradient (paper §28 / DeepMath)

This file defines the convex-analytic subgradient of a real-valued
function `f : ℝ → ℝ` at a point `x`, and records three small but
complete identities:

* `subgradient_const`: `0 ∈ ∂c` for any constant function `λ _ => c`.
* `subgradient_linear`: `a ∈ ∂(fun y => a*y + b)` at every `x`.
* `one_mem_subgradient_max_pos`: `1 ∈ ∂(max 0 ·)(x)` for `x > 0`.

These three lemmas are the minimal convex-analytic bricks used by the
`NFrame` barrier/determining-modes layer.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The subgradient of a real-valued function at a point: `v ∈ ∂f(x)` iff
    `f(x) + v · (y − x) ≤ f(y)` for all y. Standard convex-analysis definition. -/
def subgradient (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {v | ∀ y : ℝ, f x + v * (y - x) ≤ f y}

/-- `0` is in the subgradient of a constant function `λ _ => c` at any point. -/
theorem subgradient_const (c x : ℝ) : (0 : ℝ) ∈ subgradient (fun _ => c) x := by
  intro y
  simp

/-- `a` is in the subgradient of `fun y => a * y + b` at any `x`. -/
theorem subgradient_linear (a b x : ℝ) : a ∈ subgradient (fun y => a * y + b) x := by
  intro y
  show a * x + b + a * (y - x) ≤ a * y + b
  nlinarith [sq_nonneg (y - x)]

/-- The subgradient of `max 0 ·` at `x > 0` contains `1`. -/
theorem one_mem_subgradient_max_pos (x : ℝ) (h : 0 < x) :
    (1 : ℝ) ∈ subgradient (fun y => max 0 y) x := by
  intro y
  have h_max_x : max 0 x = x := max_eq_right h.le
  have h_y_le_max : y ≤ max 0 y := le_max_right _ _
  show max 0 x + 1 * (y - x) ≤ max 0 y
  rw [h_max_x]
  linarith

end PallLean.Paper93.DeepMath.NFrame
