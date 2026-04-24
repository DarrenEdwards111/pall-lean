import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# N-Frame: convexity of `-log` on `(0, ∞)`

This file wraps Mathlib's strict concavity of `Real.log` on `(0, ∞)`
(`strictConcaveOn_log_Ioi`) into the convexity statement needed by the
N-Frame scalar single-minor barrier: the scalar map `x ↦ -Real.log x`
is convex on `(0, ∞)`.

The wrapper is a thin adapter: strict concavity of `Real.log` gives,
via `.neg`, strict convexity of `-Real.log`, whose `.convexOn`
projection yields convexity. The function pointwise equals
`fun x => -Real.log x`, so we only need to rewrite the pointwise-negation.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Scalar `-log` is convex on `(0, ∞)`. Wraps Mathlib's
`strictConcaveOn_log_Ioi` via `.neg.convexOn` and rewrites the pointwise
negation `-Real.log` into `fun x => -Real.log x`. -/
theorem neg_log_convexOn_Ioi :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) := by
  -- `strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) Real.log`.
  -- `.neg` gives `StrictConvexOn ℝ (Ioi 0) (-Real.log)`.
  -- `.convexOn` drops strictness.
  have h : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (-Real.log) :=
    strictConcaveOn_log_Ioi.neg.convexOn
  -- Rewrite `-Real.log` as `fun x => -Real.log x`.
  have hfun : (-Real.log) = (fun x => -Real.log x) := by
    funext x; rfl
  rw [hfun] at h
  exact h

end PallLean.Paper93.DeepMath.NFrame
