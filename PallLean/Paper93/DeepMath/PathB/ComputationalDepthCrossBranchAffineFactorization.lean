import PallLean.Paper93.DeepMath.PathB.ComputationalDepthParityRankRestrictionNoGo

/-!
# Cross-branch affine factorization for queried parity coordinates

Querying `q` parity-input columns produces one residual shift for each Boolean assignment.  Algebraically those shifts
are subset sums of the queried column vectors.  This file packages all branches into one deduplicated affine family
and proves:

* there are at most `2^q` distinct shifts;
* any further residual-state classifier has at most `2^q` classes;
* it has strictly fewer classes exactly when that classifier identifies two distinct reachable shifts.

Thus cross-branch reuse has a precise load-bearing condition: a collision in the residual affine quotient.  Merely
rewriting branches as cosets does not itself produce a saving; one must prove many such collisions for the circuit
class, or exhibit a factorized algorithm whose cost is smaller than the number of distinct classes.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization

open scoped Classical
open Finset

variable {V Class : Type*} [AddCommMonoid V] [DecidableEq V] [DecidableEq Class]

/-- Reachable shifts of queried parity columns: all subset sums, deduplicated. -/
def branchShiftSet (queried : Finset V) : Finset V :=
  queried.powerset.image (fun s => ∑ v ∈ s, v)

/-- Distinct residual classes after applying a semantic/coset classifier to every reachable shift. -/
def affineClassSet (queried : Finset V) (classify : V → Class) : Finset Class :=
  (branchShiftSet queried).image classify

/-- The deduplicated shift family never exceeds the `2^q` raw assignment branches. -/
theorem branchShiftSet_card_le (queried : Finset V) :
    (branchShiftSet queried).card ≤ 2 ^ queried.card := by
  unfold branchShiftSet
  calc
    (queried.powerset.image (fun s => ∑ v ∈ s, v)).card ≤ queried.powerset.card := card_image_le
    _ = 2 ^ queried.card := card_powerset queried

/-- Any cross-branch semantic quotient has at most `2^q` residual classes. -/
theorem affineClassSet_card_le (queried : Finset V) (classify : V → Class) :
    (affineClassSet queried classify).card ≤ 2 ^ queried.card := by
  exact le_trans card_image_le (branchShiftSet_card_le queried)

/-- Exact criterion for whether semantic classification compresses the reachable shift family. -/
theorem affineClassSet_card_eq_iff_injOn (queried : Finset V) (classify : V → Class) :
    (affineClassSet queried classify).card = (branchShiftSet queried).card ↔
      Set.InjOn classify (branchShiftSet queried : Set V) := by
  exact Finset.card_image_iff

/-- Two distinct reachable shifts with the same residual class give genuine cross-branch reuse. -/
theorem affineClassSet_card_lt_of_collision (queried : Finset V) (classify : V → Class)
    {a b : V} (ha : a ∈ branchShiftSet queried) (hb : b ∈ branchShiftSet queried)
    (hne : a ≠ b) (hclass : classify a = classify b) :
    (affineClassSet queried classify).card < (branchShiftSet queried).card := by
  have hnotinj : ¬ Set.InjOn classify (branchShiftSet queried : Set V) := by
    intro hinj
    exact hne (hinj ha hb hclass)
  have hle : (affineClassSet queried classify).card ≤ (branchShiftSet queried).card := card_image_le
  exact lt_of_le_of_ne hle (fun heq => hnotinj ((affineClassSet_card_eq_iff_injOn queried classify).mp heq))

end PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization

#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization.branchShiftSet_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization.affineClassSet_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchAffineFactorization.affineClassSet_card_lt_of_collision
