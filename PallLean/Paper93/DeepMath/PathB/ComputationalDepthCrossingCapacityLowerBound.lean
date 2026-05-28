import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSubfunctionCapacityWall

/-!
# Crossing-state capacity lower bound

**STATUS: GENUINE RESTRICTED CAPACITY THEOREM.**

This file proves the clean kernel behind Nechiporuk-style subfunction arguments,
OBDD width lower bounds, and one-way communication lower bounds.

If a computation is structurally forced to pass from an `XR` block to an `XB`
block through one of `c` crossing states, then it can expose at most `c` distinct
residual/subfunctions on the `XB` side.  This is exactly the restricted capacity
theorem missing from unrestricted semantic models.

Honest scope: this applies to crossing / bounded-width / one-way-message models.
It does **not** apply to arbitrary circuits, TC⁰, NC¹, or width-5 BP unless a
separate theorem proves that those models have such a crossing bottleneck.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Classical

variable {XR XB : Type*} [Fintype XR] [Fintype XB]

/-- The distinct residual functions `xB ↦ f xR xB` as `xR` ranges over `XR`. -/
noncomputable def crossingSubfunctions (f : XR -> XB -> Bool) : Finset (XB -> Bool) :=
  Finset.univ.image f

/-- Number of distinct crossing residual functions. -/
noncomputable def crossingSubfunctionCount (f : XR -> XB -> Bool) : Nat :=
  (crossingSubfunctions f).card

/-- A crossing model: after the `XR` side is processed, all information that can
influence the `XB` side is compressed into one of `numStates` states. -/
structure CrossingModel (f : XR -> XB -> Bool) where
  numStates : Nat
  state : XR -> Fin numStates
  combine : Fin numStates -> XB -> Bool
  computes : forall xR, f xR = combine (state xR)

/-- Capacity theorem: a crossing model with `c` states exposes at most `c`
distinct residual functions. -/
theorem crossing_capacity {f : XR -> XB -> Bool} (M : CrossingModel f) :
    crossingSubfunctionCount f <= M.numStates := by
  classical
  have key : crossingSubfunctions f ⊆ Finset.univ.image M.combine := by
    intro g hg
    simp only [crossingSubfunctions, Finset.mem_image, Finset.mem_univ, true_and] at hg
    obtain ⟨xR, hxR⟩ := hg
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨M.state xR, (M.computes xR).symm.trans hxR⟩
  calc
    crossingSubfunctionCount f
        <= (Finset.univ.image M.combine).card := Finset.card_le_card key
    _ <= (Finset.univ : Finset (Fin M.numStates)).card := Finset.card_image_le
    _ = M.numStates := by rw [Finset.card_univ, Fintype.card_fin]

/-- Lower-bound form: a function with `k` crossing residuals requires at least
`k` crossing states. -/
theorem crossing_state_lower_bound {f : XR -> XB -> Bool} (M : CrossingModel f)
    {k : Nat} (hk : k <= crossingSubfunctionCount f) : k <= M.numStates :=
  Nat.le_trans hk (crossing_capacity M)

/-! ## Concrete exponential instance: storage access -/

/-- Storage access: the left block is a Boolean table, the right block is an
index, and the output is the addressed bit. -/
def StorageAccess (m : Nat) : (Fin m -> Bool) -> Fin m -> Bool :=
  fun data i => data i

/-- Storage access has exactly `2^m` crossing residual functions. -/
theorem storageAccess_crossingSubfunctionCount (m : Nat) :
    crossingSubfunctionCount (StorageAccess m) = 2 ^ m := by
  classical
  unfold crossingSubfunctionCount crossingSubfunctions StorageAccess
  change (Finset.univ.image (fun data : Fin m -> Bool => data)).card = 2 ^ m
  calc
    (Finset.univ.image (fun data : Fin m -> Bool => data)).card
        = (Finset.univ : Finset (Fin m -> Bool)).card := by
          exact Finset.card_image_of_injective _ (fun _ _ h => h)
    _ = 2 ^ m := by
          simp [Fintype.card_bool]

/-- Concrete exponential lower bound: any crossing model for storage access on
`m` cells needs at least `2^m` crossing states. -/
theorem storageAccess_crossing_lb (m : Nat)
    (M : CrossingModel (StorageAccess m)) :
    2 ^ m <= M.numStates := by
  rw [← storageAccess_crossingSubfunctionCount m]
  exact crossing_capacity M

/-- Package for the crossing-capacity theorem and its exponential storage-access
instance. -/
structure CrossingCapacityLowerBound : Prop where
  capacity : forall {XR XB : Type*} [Fintype XR] [Fintype XB]
    {f : XR -> XB -> Bool} (M : CrossingModel f),
    crossingSubfunctionCount f <= M.numStates
  storage_access : forall m : Nat, forall M : CrossingModel (StorageAccess m),
    2 ^ m <= M.numStates

/-- Completed crossing-capacity lower-bound package. -/
theorem crossingCapacityLowerBound : CrossingCapacityLowerBound where
  capacity := by
    intro XR XB hXR hXB f M
    exact crossing_capacity M
  storage_access := storageAccess_crossing_lb

/-! ## Kernel-only trace -/

#print axioms crossing_capacity
#print axioms crossing_state_lower_bound
#print axioms storageAccess_crossingSubfunctionCount
#print axioms storageAccess_crossing_lb
#print axioms crossingCapacityLowerBound

end PallLean.Paper93.DeepMath.PathB
