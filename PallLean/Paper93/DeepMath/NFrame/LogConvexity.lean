import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# N-Frame: log convexity wrappers

This file wraps Mathlib's strict concavity of `Real.log` on `(0, ∞)`
(`strictConcaveOn_log_Ioi`) into the forms needed by the N-Frame scalar
barrier theory:

* `log_strictConcaveOn`      : `Real.log` is strictly concave on `(0, ∞)`;
* `neg_log_strictConvexOn`   : `fun x => -Real.log x` is strictly convex on `(0, ∞)`;
* `neg_log_convexOn_Ioi_weak`: the corresponding convexity (dropping strictness).

The Mathlib lemma `strictConcaveOn_log_Ioi` lives at the root namespace in
`Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean` (inside a
`public section` with `open Real`), so we access it without the `Real.`
prefix.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `Real.log` is strictly concave on `(0, ∞)`. Wraps Mathlib's
`strictConcaveOn_log_Ioi`. -/
theorem log_strictConcaveOn : StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
  strictConcaveOn_log_Ioi

/-- `fun x => -Real.log x` is strictly convex on `(0, ∞)`. Obtained from
`log_strictConcaveOn` via `.neg`, with a pointwise rewrite of the
function-level negation into the lambda form. -/
theorem neg_log_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) := by
  have h : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (-Real.log) :=
    log_strictConcaveOn.neg
  have hfun : (-Real.log) = (fun x => -Real.log x) := by
    funext x; rfl
  rw [hfun] at h
  exact h

/-- `fun x => -Real.log x` is convex on `(0, ∞)` (relaxation of the strict
form). Obtained from `neg_log_strictConvexOn` via `.convexOn`. -/
theorem neg_log_convexOn_Ioi_weak :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) :=
  neg_log_strictConvexOn.convexOn

end PallLean.Paper93.DeepMath.NFrame
