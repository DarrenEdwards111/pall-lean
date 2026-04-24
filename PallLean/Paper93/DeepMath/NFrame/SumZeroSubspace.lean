import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Pi

/-!
# Sum-zero subspace of `Fin n → ℝ`

This file records two elementary facts about the sum-zero subspace
`{Φ : Fin n → ℝ | ∑ i, Φ i = 0}` of `ℝ^n`:

* it is closed (as the zero set of a continuous linear functional);
* it is convex (being in fact a linear subspace).

Both facts are used downstream in the N-Frame analysis of the
Paper93 truncated Navier--Stokes construction.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The sum-zero subspace `{Φ : Fin n → ℝ | ∑ Φᵢ = 0}` is closed in ℝ^n. -/
theorem sumZeroSubspace_isClosed {n : ℕ} :
    IsClosed {phi : Fin n → ℝ | ∑ i, phi i = 0} := by
  apply isClosed_eq
  · exact continuous_finset_sum _ fun i _ => continuous_apply i
  · exact continuous_const

/-- The sum-zero subspace is a convex set. -/
theorem sumZeroSubspace_convex {n : ℕ} :
    Convex ℝ {phi : Fin n → ℝ | ∑ i, phi i = 0} := by
  intros x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  show ∑ i, (a • x + b • y) i = 0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
             ← Finset.mul_sum, hx, hy]
  ring

end PallLean.Paper93.DeepMath.NFrame
