/-
  PallLean/Paper93/DeepMath/NFrame/SignLocallyConst.lean

  `Real.sign` is locally constant away from zero: in a neighborhood of
  a positive point it is identically `1`, and in a neighborhood of a
  negative point it is identically `-1`. These facts are the analytic
  backbone behind the derivative computation of the parity term on
  `{φ ≠ 0}`, where `parityTerm χ · ` is locally a constant.

  Kernel-only; uses only Mathlib filter/nhds primitives.
-/
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

namespace PallLean.Paper93.DeepMath.NFrame

open Filter Topology

/-- `Real.sign` is eventually equal to `1` in a neighborhood of any `x > 0`. -/
theorem sign_locally_eq_one (x : ℝ) (hx : 0 < x) :
    ∀ᶠ y in 𝓝 x, Real.sign y = 1 := by
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact Real.sign_of_pos hy

/-- `Real.sign` is eventually equal to `-1` in a neighborhood of any `x < 0`. -/
theorem sign_locally_eq_neg_one (x : ℝ) (hx : x < 0) :
    ∀ᶠ y in 𝓝 x, Real.sign y = -1 := by
  filter_upwards [eventually_lt_nhds hx] with y hy
  exact Real.sign_of_neg hy

end PallLean.Paper93.DeepMath.NFrame
