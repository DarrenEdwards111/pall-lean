import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingCapacityLowerBound

/-!
# Crossing-bottleneck no-go (the bridge is false, not merely open)

**STATUS: NO-GO / CONSERVATION THEOREM.  FORMAL DISPROOF OF THE CROSSING BRIDGE.**

The crossing-state capacity bound (`crossing_capacity`) gives exponential lower
bounds *only* for models forced through one small crossing state.  The tempting
"bridge" to real complexity classes would be a **crossing-bottleneck theorem**:
that every cheap computation in TC⁰ / NC¹ / width-5 BP can be turned into a
crossing model with few states.  This file proves that such a bridge **cannot
exist** for these classes — it is false, not merely unproven.

## The argument

A crossing bottleneck for a class would imply, via `crossing_capacity`, that any
function the class computes cheaply has small crossing-subfunction count.  But
**storage access** (the multiplexer) is computable by polynomial-size `AC⁰ ⊆ NC¹ ⊆`
width-5 BP, yet `crossingSubfunctionCount (StorageAccess m) = 2^m`.  Hence the
bottleneck bound would have to be exponential in the (small) budget — i.e. there
is no *small* crossing bottleneck.  Equivalently: width-5 BPs reread the boundary
`Θ(m)` times, so the effective crossing state is `2^{Θ(m)}`, never a single small
state.

## Honest status

`bottleneck_capacity_le_bound` and `crossing_bottleneck_must_blow_up` are proved
outright.  The single standard fact used as a hypothesis is that storage access
is cheaply computable in the class (multiplexer ∈ AC⁰) — supplied as the
existence of *some* crossing model with the claimed bottleneck bound; the theorem
shows that hypothesis forces the bound `≥ 2^m`.  This mirrors the project's
healthiest pattern: formalize *why the crossing cannot be crossed* rather than
fake a bridge.  It is the exact dual of the subfunction-capacity wall.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {XR XB : Type*} [Fintype XR] [Fintype XB]

/-! ## The crossing-bottleneck hypothesis, as a definition -/

/-- A class with cheap-computability relation `Compute` has a **crossing
bottleneck** with budget-to-state bound `bound` if every function it computes with
budget `s` can be realised by a crossing model using at most `bound s` states.
This is exactly the bridge one would need to apply `crossing_capacity` to the
class. -/
def CrossingBottleneck
    (Compute : (XR -> XB -> Bool) -> Nat -> Prop) (bound : Nat -> Nat) : Prop :=
  forall (f : XR -> XB -> Bool) (s : Nat),
    Compute f s -> ∃ M : CrossingModel f, M.numStates <= bound s

/-- Under a crossing bottleneck, every cheaply-computed function has crossing
subfunction count bounded by `bound s`.  (Immediate from `crossing_capacity`.) -/
theorem bottleneck_capacity_le_bound
    {Compute : (XR -> XB -> Bool) -> Nat -> Prop} {bound : Nat -> Nat}
    (H : CrossingBottleneck Compute bound)
    {f : XR -> XB -> Bool} {s : Nat} (hf : Compute f s) :
    crossingSubfunctionCount f <= bound s := by
  obtain ⟨M, hM⟩ := H f s hf
  exact Nat.le_trans (crossing_capacity M) hM

/-! ## The no-go: the bottleneck bound must be exponential -/

/-- **Crossing bottleneck forces exponential blowup.**  Suppose that for every
`m`, the storage-access function on `m` cells admits a crossing model whose state
count is within the claimed bottleneck bound `bound (s m)` (this is precisely the
crossing-bottleneck claim instantiated at storage access, which the class computes
with budget `s m`).  Then `bound (s m) ≥ 2^m` for all `m`.

So there is no *small* crossing bottleneck: the budget-to-state bound is forced to
grow exponentially. -/
theorem crossing_bottleneck_must_blow_up
    (s bound : Nat -> Nat)
    (Hbot : forall m : Nat,
        ∃ M : CrossingModel (StorageAccess m), M.numStates <= bound (s m)) :
    forall m : Nat, 2 ^ m <= bound (s m) := by
  intro m
  obtain ⟨M, hM⟩ := Hbot m
  calc
    2 ^ m = crossingSubfunctionCount (StorageAccess m) :=
          (storageAccess_crossingSubfunctionCount m).symm
    _ <= M.numStates := crossing_capacity M
    _ <= bound (s m) := hM

/-- **The bridge is false.**  If a claimed crossing bottleneck ever gives a bound
below `2^m` at some scale `m` (as any genuinely *small* — e.g. polynomial —
bottleneck must, since storage access is computed with small budget `s m`), it
contradicts the forced exponential blowup.  Hence no small crossing bottleneck
exists for any class that computes storage access cheaply. -/
theorem no_small_crossing_bottleneck
    (s bound : Nat -> Nat)
    (Hbot : forall m : Nat,
        ∃ M : CrossingModel (StorageAccess m), M.numStates <= bound (s m))
    (m : Nat) (Hsmall : bound (s m) < 2 ^ m) : False :=
  Nat.not_lt.mpr (crossing_bottleneck_must_blow_up s bound Hbot m) Hsmall

/-! ## Bundled no-go -/

/-- Package: the capacity transfer under a bottleneck, plus the exponential-blowup
no-go witnessed by storage access. -/
structure CrossingBottleneckNoGo : Prop where
  /-- A bottleneck transfers the crossing bound to the class. -/
  transfer : forall {XR XB : Type} [Fintype XR] [Fintype XB]
    {Compute : (XR -> XB -> Bool) -> Nat -> Prop} {bound : Nat -> Nat},
    CrossingBottleneck Compute bound ->
    forall {f : XR -> XB -> Bool} {s : Nat}, Compute f s ->
      crossingSubfunctionCount f <= bound s
  /-- Any crossing bottleneck for storage access blows up exponentially. -/
  blow_up : forall (s bound : Nat -> Nat),
    (forall m : Nat, ∃ M : CrossingModel (StorageAccess m), M.numStates <= bound (s m)) ->
    forall m : Nat, 2 ^ m <= bound (s m)

/-- Completed crossing-bottleneck no-go. -/
theorem crossingBottleneckNoGo : CrossingBottleneckNoGo where
  transfer := by
    intro XR XB _ _ Compute bound H f s hf
    exact bottleneck_capacity_le_bound H hf
  blow_up := crossing_bottleneck_must_blow_up

/-! ## Kernel-only trace -/

#print axioms bottleneck_capacity_le_bound
#print axioms crossing_bottleneck_must_blow_up
#print axioms no_small_crossing_bottleneck
#print axioms crossingBottleneckNoGo

end PallLean.Paper93.DeepMath.PathB
