import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContextualContinuationCurvature
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCNFSelfReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingCapacityLowerBound

/-!
# CNF-derived contextual bubbles and a restricted-observer lower bound

This file moves contextual continuation curvature from an abstract non-flat toy
to genuine, solver-independent CNF syntax.

First, encoded CNF restriction supplies the transport around a two-coordinate
context square.  Exact SAT semantics makes this square flat: restricting two
different variables commutes semantically.  Thus raw syntax/restriction cannot
manufacture curvature by itself; curvature must enter through a lossy,
context-dependent observer projection.

Second, a canonical family of unit-clause CNFs turns each left assignment into
the residual predicate accepting exactly the matching right assignment.  These
formulas are generated directly from syntax, without consulting SAT answers.
Their continuation fiber has exactly `2^m` distinct semantic sections.  The
existing crossing-capacity theorem then gives an unconditional exponential
state lower bound for every fixed-order / one-way observer that must compress
the whole left bubble before seeing the right continuation.

This is a genuine restricted-model Route-G theorem.  It is not a lower bound
for arbitrary polynomial-time machines, which may reread variables and move
their boundary adaptively.
-/

namespace PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver

open ContextualContinuationCurvature
open CNFSelfReduction

/-! ## Exact CNF restriction transport is flat -/

inductive RestrictionContext
  | outer
  | afterLeft
  | afterRight
  | afterBoth
  deriving DecidableEq, Fintype

def restrictionSquare : BubbleSquare RestrictionContext where
  outer := .outer
  left := .afterLeft
  right := .afterRight
  inner := .afterBoth

/-- Before the common endpoint the observer carries encoded CNF syntax; at the
endpoint it carries the complete continuation semantics of that syntax. -/
def restrictionFiber (n : ℕ) : RestrictionContext → Type
  | .outer => CNF n
  | .afterLeft => CNF n
  | .afterRight => CNF n
  | .afterBoth => (Fin n → Bool) → Bool

def restrictionBundle (n : ℕ) : ContextualBundle RestrictionContext where
  Fiber := restrictionFiber n

/-- Two genuine syntactic restriction routes, compared by their full semantics
at the common inner bubble. -/
def restrictionTransport {n : ℕ} (i j : Fin n) (vi vj : Bool) :
    LocalTransport (restrictionBundle n) restrictionSquare where
  outerLeft := fun φ ↦ restrict φ i vi
  outerRight := fun φ ↦ restrict φ j vj
  leftInner := fun φ a ↦ eval (restrict φ j vj) a
  rightInner := fun φ a ↦ eval (restrict φ i vi) a

/-- Restriction of distinct coordinates commutes at the level of genuine CNF
continuation semantics. -/
theorem restrict_restrict_semantically_commute {n : ℕ}
    (φ : CNF n) (i j : Fin n) (vi vj : Bool) (hij : i ≠ j) :
    (fun a ↦ eval (restrict (restrict φ i vi) j vj) a) =
      (fun a ↦ eval (restrict (restrict φ j vj) i vi) a) := by
  funext a
  rw [restrict_correct, restrict_correct, restrict_correct, restrict_correct]
  rw [Function.update_comm hij.symm]

/-- The solver-independent CNF restriction square is flat.  Any later
curvature must therefore be charged to observer-relative compression rather
than to the exact restriction semantics. -/
theorem restrictionTransport_flat {n : ℕ}
    (i j : Fin n) (vi vj : Bool) (hij : i ≠ j) :
    Flat (restrictionTransport i j vi vj) := by
  intro φ
  exact restrict_restrict_semantically_commute φ i j vi vj hij

/-! ## A solver-independent CNF continuation family -/

/-- The encoded formula fixing every variable to the supplied assignment.
The construction reads only the assignment syntax; it never asks a SAT solver
for the answer to a generated query. -/
def unitAssignmentCNF {m : ℕ} (a : Fin m → Bool) : CNF m :=
  List.ofFn (fun i ↦ [(i, a i)])

/-- A unit-assignment CNF accepts exactly its generating assignment. -/
theorem unitAssignmentCNF_eval_true_iff {m : ℕ}
    (a b : Fin m → Bool) :
    eval (unitAssignmentCNF a) b = true ↔ a = b := by
  simp only [eval, unitAssignmentCNF, List.all_eq_true,
    List.forall_mem_ofFn_iff, clauseSat, List.any_cons, List.any_nil,
    Bool.or_false, litSat, beq_iff_eq]
  constructor
  · intro h
    funext i
    exact (h i).symm
  · intro h i
    exact (congrFun h i).symm

/-- The continuation semantics exposed by the CNF generated from `a`. -/
def unitCNFContinuation (m : ℕ) :
    (Fin m → Bool) → (Fin m → Bool) → Bool :=
  fun a b ↦ eval (unitAssignmentCNF a) b

/-- Different outer assignments induce different genuine CNF continuation
sections. -/
theorem unitCNFContinuation_injective (m : ℕ) :
    Function.Injective (unitCNFContinuation m) := by
  intro a a' h
  have ha := congrFun h a
  have hleft : unitCNFContinuation m a a = true :=
    (unitAssignmentCNF_eval_true_iff a a).2 rfl
  have hright : unitCNFContinuation m a' a = true := by
    rw [← ha]
    exact hleft
  exact ((unitAssignmentCNF_eval_true_iff a' a).1 hright).symm

/-- The genuine unit-CNF continuation fiber has exactly `2^m` semantic
sections. -/
theorem unitCNFContinuation_crossingSubfunctionCount (m : ℕ) :
    crossingSubfunctionCount (unitCNFContinuation m) = 2 ^ m := by
  classical
  unfold crossingSubfunctionCount crossingSubfunctions
  calc
    (Finset.univ.image (unitCNFContinuation m)).card =
        (Finset.univ : Finset (Fin m → Bool)).card := by
      exact Finset.card_image_of_injective _ (unitCNFContinuation_injective m)
    _ = 2 ^ m := by simp [Fintype.card_bool]

/-- **Restricted observer lower bound.**  Every fixed-order/one-way observer
that compresses the outer assignment into one crossing state before receiving
the future assignment needs at least `2^m` states to reproduce the genuine CNF
continuation semantics. -/
theorem unitCNF_fixedOrderObserver_requires_two_pow_states (m : ℕ)
    (M : CrossingModel (unitCNFContinuation m)) :
    2 ^ m ≤ M.numStates := by
  rw [← unitCNFContinuation_crossingSubfunctionCount m]
  exact crossing_capacity M

/-- The two completed calibrations packaged together: exact CNF transport is
flat, while a fixed-order observer boundary for a genuine CNF continuation
family requires exponential state capacity. -/
structure CNFContextualRestrictedCalibration : Prop where
  exactRestrictionFlat : ∀ {n : ℕ} (i j : Fin n) (vi vj : Bool), i ≠ j →
    Flat (restrictionTransport i j vi vj)
  continuationCount : ∀ m : ℕ,
    crossingSubfunctionCount (unitCNFContinuation m) = 2 ^ m
  fixedOrderLowerBound : ∀ m : ℕ,
    ∀ M : CrossingModel (unitCNFContinuation m), 2 ^ m ≤ M.numStates

theorem cnfContextualRestrictedCalibration :
    CNFContextualRestrictedCalibration where
  exactRestrictionFlat := restrictionTransport_flat
  continuationCount := unitCNFContinuation_crossingSubfunctionCount
  fixedOrderLowerBound := unitCNF_fixedOrderObserver_requires_two_pow_states

/-!
## Audit boundary

This closes the first restricted-observer experiment proposed by the contextual
bubble program.  The formulas are genuine CNFs generated without answer-coded
`yesCNF`/`noCNF` selection.  The exponential result is unconditional but applies
only to a one-way crossing boundary.  Extending it to adaptive rereading and
polynomial memory is precisely the next, substantially harder test; this file
makes no claim that the restricted theorem already applies to general P.
-/

end PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver

#print axioms PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver.restrictionTransport_flat
#print axioms PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver.unitAssignmentCNF_eval_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver.unitCNFContinuation_crossingSubfunctionCount
#print axioms PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver.unitCNF_fixedOrderObserver_requires_two_pow_states
#print axioms PallLean.Paper93.DeepMath.PathB.CNFContextualBubbleRestrictedObserver.cnfContextualRestrictedCalibration
