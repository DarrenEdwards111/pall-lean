import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTC0NC1ObserverRoute
import Mathlib.Data.Finset.Basic

/-!
# Threshold-composition frontier signpost for TC⁰

**STATUS: CONDITIONAL SIGNPOST, NOT PROGRESS TOWARD A TC⁰ LOWER BOUND.**

The observer-invariant diagnosis says that any TC⁰ lower-bound route of this
kind would need a composition theorem:

> low invariant at the leaves, plus stability under every threshold layer,
> implies low invariant for every constant-depth threshold circuit.

This file formalizes only the free structural-induction part of that statement
for a small *layered* threshold-circuit syntax.  The main theorem
`thresholdCircuit_preservation` says: **if** one assumes the layer-stability rule,
then the invariant is bounded on the whole circuit.

All hard TC⁰ content sits in the hypothesis `ThresholdLayerStable`.  No
non-natural invariant satisfying that hypothesis is supplied here.  This file is
a map of the wall, not a brick through it.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Layered threshold-circuit syntax -/

/-- A threshold gate on `fanin` Boolean inputs. -/
def thresholdValue {fanin : Nat} (θ : Nat) (vals : Fin fanin -> Bool) : Bool :=
  decide (θ ≤ ((Finset.univ : Finset (Fin fanin)).filter (fun i => vals i)).card)

/-- A layered threshold expression over `n` Boolean variables.  `ThresholdLayer n d`
contains circuits of exactly layer-depth `d`: leaves live at depth `0`, and a gate
at depth `d+1` takes finitely many children from depth `d`.  This is enough for
constant-depth TC⁰-style composition accounting; non-layered circuits can be
padded by dummy identity layers in ordinary circuit models. -/
inductive ThresholdLayer (n : Nat) : Nat -> Type where
  | var : Fin n -> ThresholdLayer n 0
  | cst : Bool -> ThresholdLayer n 0
  | gate {d fanin : Nat} : Nat -> (Fin fanin -> ThresholdLayer n d) -> ThresholdLayer n (d + 1)

namespace ThresholdLayer

/-- Semantics of a layered threshold expression. -/
def eval {n d : Nat} : ThresholdLayer n d -> BoolFun n
  | var i => fun x => x i
  | cst b => fun _ => b
  | gate θ child => fun x => thresholdValue θ (fun i => eval (child i) x)

/-- Size, included for budget bookkeeping. -/
def size {n d : Nat} : ThresholdLayer n d -> Nat
  | var _ => 1
  | cst _ => 1
  | @gate _ d fanin _ child => 1 + ∑ i : Fin fanin, size (child i)

/-- Leaf preservation condition: variables and constants have bounded invariant. -/
def LeafPreserved {n : Nat} (I : TCObserverInvariant n) (B : Nat -> Nat) : Prop :=
  (∀ i : Fin n, I.Q (eval (var i)) ≤ B 0) ∧
  (∀ b : Bool, I.Q (eval (cst b)) ≤ B 0)

/-- Threshold-layer composition condition.  If every child function of a threshold
gate at layer `d` is bounded by the depth-indexed budget `B d`, then the threshold
of those children is bounded at layer `d+1`.  This is the unproved,
barrier-strength condition for any proposed invariant. -/
def ThresholdLayerStable {n : Nat} (I : TCObserverInvariant n) (B : Nat -> Nat) : Prop :=
  ∀ {d fanin : Nat} (θ : Nat) (child : Fin fanin -> ThresholdLayer n d),
    (∀ i, I.Q (eval (child i)) ≤ B d) ->
      I.Q (eval (gate θ child)) ≤ B (d + 1)

/-- **Conditional composition signpost.**  If an observer invariant is bounded on
leaves and one assumes stability under threshold layers, then every layered
threshold circuit has low invariant at its depth.  The proof is structural
induction; the hard/open content is entirely the `ThresholdLayerStable`
hypothesis. -/
theorem thresholdCircuit_preservation {n : Nat}
    (I : TCObserverInvariant n) (B : Nat -> Nat)
    (hleaf : LeafPreserved I B)
    (hstable : ThresholdLayerStable I B) :
    ∀ {d : Nat} (C : ThresholdLayer n d), I.Q (eval C) ≤ B d := by
  intro d C
  induction C with
  | var i => exact hleaf.1 i
  | cst b => exact hleaf.2 b
  | gate θ child ih =>
      exact hstable θ child ih

/-- A target violates the threshold-composition invariant at depth `d` if its
invariant value exceeds the budget allowed for depth `d`. -/
def ThresholdTargetGap {n : Nat} (I : TCObserverInvariant n)
    (B : Nat -> Nat) (f : BoolFun n) (d : Nat) : Prop :=
  B d < I.Q f

/-- Consequence: a target with invariant above the depth-`d` threshold cannot be
computed by any layered threshold expression of depth exactly `d`. -/
theorem no_thresholdLayer_of_composition_gap {n d : Nat}
    (I : TCObserverInvariant n) (B : Nat -> Nat)
    (hleaf : LeafPreserved I B)
    (hstable : ThresholdLayerStable I B)
    {f : BoolFun n}
    (hgap : ThresholdTargetGap I B f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f := by
  rintro ⟨C, hCf⟩
  have hpres := thresholdCircuit_preservation I B hleaf hstable C
  rw [hCf] at hpres
  exact Nat.not_lt.mpr hpres hgap

/-- A bundled conditional route.  To beat TC⁰ by this observer method, one would
need to supply a non-natural invariant, leaf preservation, threshold-layer
stability, and an explicit target gap.  This structure does not assert such an
invariant exists. -/
structure ThresholdCompositionRoute {n : Nat} (f : BoolFun n) (d : Nat) where
  I : TCObserverInvariant n
  B : Nat -> Nat
  leaf_preserved : LeafPreserved I B
  threshold_stable : ThresholdLayerStable I B
  target_gap : ThresholdTargetGap I B f d

/-- Any completed threshold-composition route gives a depth-`d` lower bound. -/
theorem lower_bound_of_thresholdCompositionRoute {n d : Nat}
    {f : BoolFun n} (R : ThresholdCompositionRoute f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f :=
  no_thresholdLayer_of_composition_gap R.I R.B R.leaf_preserved R.threshold_stable
    R.target_gap

/-! ## Honest frontier statement -/

/-- The exact missing theorem shape: find an invariant and budget satisfying
`ThresholdCompositionRoute` for an explicit hard target.  This definition is
intentionally a signpost/target, not a proof that such an invariant exists. -/
def TC0BreakthroughTarget {n : Nat} (f : BoolFun n) (d : Nat) : Prop :=
  Nonempty (ThresholdCompositionRoute f d)

#print axioms thresholdCircuit_preservation
#print axioms no_thresholdLayer_of_composition_gap
#print axioms lower_bound_of_thresholdCompositionRoute

end ThresholdLayer

end PallLean.Paper93.DeepMath.PathB
