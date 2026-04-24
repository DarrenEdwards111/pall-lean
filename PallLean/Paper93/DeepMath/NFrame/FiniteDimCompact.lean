import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Heine--Borel in finite-dimensional Euclidean space (N-Frame)

This file packages the Heine--Borel theorem in the concrete form we
use elsewhere in the N-Frame development: in the finite-dimensional
Euclidean space `Fin n → ℝ`, closed and bounded sets are compact, and
closed balls are compact.

Both statements are direct wrappers of Mathlib lemmas:
* `Metric.isCompact_of_isClosed_isBounded` (at the root namespace,
  re-exported as `isCompact_of_isClosed_isBounded`), which gives the
  Heine--Borel implication in any `ProperSpace`;
* `ProperSpace.isCompact_closedBall`, which is the defining field of
  the `ProperSpace` class and gives compactness of closed balls.

The relevant `ProperSpace (Fin n → ℝ)` instance is obtained from
`pi_properSpace` (a finite product of proper spaces is proper) and the
`ProperSpace ℝ` instance.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Bornology

/-- **Heine--Borel** in `ℝⁿ = Fin n → ℝ`: closed and bounded implies compact.

This is a direct wrapper of `isCompact_of_isClosed_isBounded`, which holds in
every `ProperSpace`; the instance `pi_properSpace` provides
`ProperSpace (Fin n → ℝ)`. -/
theorem isCompact_of_isClosed_isBounded {n : ℕ} (s : Set (Fin n → ℝ))
    (hclosed : IsClosed s) (hbounded : Bornology.IsBounded s) :
    IsCompact s :=
  (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hclosed, hbounded⟩

/-- The closed ball of radius `R` centred at `0` in `Fin n → ℝ` is compact.

This is a direct wrapper of `ProperSpace.isCompact_closedBall`; the hypothesis
`0 ≤ R` is not strictly needed by the Mathlib lemma (it handles negative radii
as well, with an empty closed ball), but is kept here for clarity. -/
theorem isCompact_closedBall {n : ℕ} (R : ℝ) (_hR : 0 ≤ R) :
    IsCompact (Metric.closedBall (0 : Fin n → ℝ) R) :=
  ProperSpace.isCompact_closedBall 0 R

end PallLean.Paper93.DeepMath.NFrame
