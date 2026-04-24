import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compactness of closed balls in matrix space (N-Frame)

With the *elementwise* norm on `Matrix (Fin n) (Fin n) ℝ` (obtained via
`open scoped Matrix.Norms.Elementwise`, which attaches
`Matrix.normedAddCommGroup` and `Matrix.normedSpace = Pi.normedSpace`),
the matrix space is isomorphic (as a normed space) to
`Fin n → Fin n → ℝ`. This finite product of proper spaces is itself a
`ProperSpace`, so `ProperSpace.isCompact_closedBall` gives compactness
of every closed ball.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- Closed ball in matrix space (with entry-wise norm) is compact. -/
theorem matrix_closedBall_isCompact {n : ℕ}
    (A₀ : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) :
    IsCompact (Metric.closedBall A₀ R) :=
  isCompact_closedBall A₀ R

end PallLean.Paper93.DeepMath.NFrame
