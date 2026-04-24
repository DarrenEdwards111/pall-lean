import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

/-!
# Convexity of the positive part `x ↦ max 0 x`

This file records the elementary fact that the positive-part function
`x ↦ max 0 x` is convex on all of `ℝ`. This is a direct consequence
of the convexity of the constant function `0` and the identity
function `id`, together with the fact that the pointwise maximum
(supremum) of two convex functions is convex (`ConvexOn.sup`).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The positive part function `x ↦ max 0 x` is convex on `ℝ`. -/
theorem max_zero_convexOn : ConvexOn ℝ Set.univ (fun x : ℝ => max 0 x) := by
  -- Both the constant `0` and the identity are convex on `Set.univ`.
  have hconst : ConvexOn ℝ (Set.univ : Set ℝ) (fun _ : ℝ => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) convex_univ
  have hid : ConvexOn ℝ (Set.univ : Set ℝ) (_root_.id : ℝ → ℝ) :=
    convexOn_id convex_univ
  -- The pointwise maximum of two convex functions is convex.
  have hsup : ConvexOn ℝ (Set.univ : Set ℝ)
      ((fun _ : ℝ => (0 : ℝ)) ⊔ (_root_.id : ℝ → ℝ)) :=
    hconst.sup hid
  -- Rewrite `(fun _ => 0) ⊔ id` as `fun x => max 0 x`.
  have hfun :
      ((fun _ : ℝ => (0 : ℝ)) ⊔ (_root_.id : ℝ → ℝ))
        = (fun x : ℝ => max 0 x) := by
    funext x
    simp [Pi.sup_apply, max_def, Function.id_def]
  -- Transport the convexity statement along this equality.
  simpa [hfun] using hsup

end PallLean.Paper93.DeepMath.NFrame
