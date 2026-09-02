import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCommutatorNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingStateCapacity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingBottleneckNoGo

/-!
# Quaternion-moment capstone

This capstone records the exact outcome of the noncommutative/quotient search.

1. Semantic restriction operators on distinct variables commute, so their
   commutator cannot be a separating invariant.
2. Residual non-mergeability does give a genuine lower bound for computations
   forced through a finite crossing quotient.
3. The naive bridge from general efficient computation to a small crossing
   quotient is false: storage access forces the quotient bound to be
   exponential.

Everything here is a theorem assembled from proved components.  It is not a
proof of `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.QuaternionMomentCapstone

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.RestrictionCommutatorNoGo

/-- The three-way audited status of the proposed "quaternion moment". -/
structure QuaternionMomentStatus : Prop where
  /-- Literal semantic restriction holonomy is flat. -/
  semantic_restrictions_commute :
    ∀ {n : ℕ} (f : (Fin n → Bool) → Bool)
      (i j : Fin n) (b c : Bool), i ≠ j →
      restrictAt (restrictAt f i b) j c =
        restrictAt (restrictAt f j c) i b
  /-- A faithful finite crossing quotient bounds residual non-mergeability. -/
  restricted_quotient_capacity :
    ∀ {Left Right State : Type}
      [Fintype Left] [DecidableEq Left] [Fintype State]
      (M : CrossingStateModel Left Right State)
      (Target : (Left → Bool) → (Right → Bool) → Bool),
      M.Computes Target → subfunctionCount Left Right Target ≤ M.width
  /-- Any crossing quotient covering storage access must have exponential size. -/
  general_crossing_bridge_blows_up :
    ∀ (s bound : ℕ → ℕ),
      (∀ m : ℕ, ∃ M : CrossingModel (StorageAccess m),
        M.numStates ≤ bound (s m)) →
      ∀ m : ℕ, 2 ^ m ≤ bound (s m)

/-- **Machine-checked capstone.**  The commutator candidate is flat; quotient
non-mergeability is sound for crossing-state models; and its unrestricted
small-quotient bridge is blocked by storage access. -/
theorem quaternionMomentStatus : QuaternionMomentStatus where
  semantic_restrictions_commute := by
    intro n f i j b c hij
    exact restrictAt_comm f i j b c hij
  restricted_quotient_capacity := by
    intro Left Right State _ _ _ M Target hM
    exact M.subfunctionCount_le_width Target hM
  general_crossing_bridge_blows_up := by
    intro s bound h
    exact crossing_bottleneck_must_blow_up s bound h

end PallLean.Paper93.DeepMath.PathB.QuaternionMomentCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.QuaternionMomentCapstone.quaternionMomentStatus
