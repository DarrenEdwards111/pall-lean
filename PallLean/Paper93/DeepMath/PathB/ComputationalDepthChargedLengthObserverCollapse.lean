import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedLengthObserver

/-!
# The final-decision quotient collapses holographic innovation

`ComputationalDepthChargedLengthObserver` gives every charged machine a finite observer at every input length.
This file performs the required minimisation stress test.

The current `LengthObserver` contract asks only that the terminal observer state recover the final Boolean
decision.  Under exactly that contract there is a two-state quotient for every machine: label every execution
point by the machine's eventual answer on its input, use the identity observer transition, and read that Boolean
at the end.  The label never changes along a run, so cumulative observer innovation is zero.

Consequences:

* `decisionObserver` is finite, causal, and decision-sufficient;
* `decisionObserver_innovation_zero` proves zero charged innovation on every input;
* `decisionScheme_resource_zero` proves its worst-case resource is identically zero;
* `universal_observer_lower_impossible` rejects any lower bound quantified over all currently-valid observers.

Thus minimising the present observer notion trivialises it.  A viable holographic observer must be sufficient for
a richer family of **continuations/queries**, not merely the final output bit.  That strengthened continuation
semantics is the next genuine definition; otherwise the Boolean quotient always wins.

## Honest scope

A no-go theorem for final-decision-only minimisation.  It does not refute dynamic SPDP with continuation/query
sufficiency and proves no complexity separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver

/-- The two-state final-decision quotient.  It remembers only the eventual answer for the point's input. -/
def decisionObserver (M : ChargedMachine) (n : Nat) : LengthObserver M n where
  State := Bool
  stateFintype := inferInstance
  stateDecEq := inferInstance
  observe := fun p => ChargedHolographicMachine.decide M (List.ofFn p.input)
  observedNext := id
  observedOutput := id
  step_commutes := fun _ _ => rfl
  output_factors := fun _ => rfl

/-- Observer innovation along one length-`n` run: count observer-state changes between consecutive charged
times. -/
def observerInnovation {M : ChargedMachine} {n : Nat} (O : LengthObserver M n)
    (a : Fin n → Bool) : Nat :=
  ∑ t : Fin (M.clock n),
    if O.observe ⟨a, ⟨t.val, by omega⟩⟩ ≠ O.observe ⟨a, ⟨t.val + 1, by omega⟩⟩
    then 1 else 0

/-- The final-decision quotient never changes along a run. -/
theorem decisionObserver_innovation_zero (M : ChargedMachine) (n : Nat) (a : Fin n → Bool) :
    observerInnovation (decisionObserver M n) a = 0 := by
  simp [observerInnovation, decisionObserver]

/-- A length-indexed observer scheme for one machine. -/
abbrev ObserverScheme (M : ChargedMachine) := ∀ n, LengthObserver M n

/-- The decision-only scheme exists for every charged machine. -/
def decisionScheme (M : ChargedMachine) : ObserverScheme M :=
  decisionObserver M

/-- Worst-case observer innovation at length `n`. -/
def schemeResource {M : ChargedMachine} (S : ObserverScheme M) (n : Nat) : Nat :=
  (Finset.univ : Finset (Fin n → Bool)).sup (observerInnovation (S n))

theorem decisionScheme_resource_zero (M : ChargedMachine) (n : Nat) :
    schemeResource (decisionScheme M) n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro a _
  change observerInnovation (decisionObserver M n) a ≤ 0
  rw [decisionObserver_innovation_zero]

/-- The decision-only scheme is polynomially bounded (indeed identically zero) for every machine, regardless
of its language or runtime. -/
theorem decisionScheme_polyBounded (M : ChargedMachine) :
    PolyBounded (schemeResource (decisionScheme M)) := by
  refine ⟨0, 0, fun n => ?_⟩
  rw [decisionScheme_resource_zero]
  exact Nat.zero_le _

/-- No language can have super-polynomial innovation for **every** observer satisfying the current final-output
contract: the two-state decision observer is always a zero-cost counterexample. -/
theorem universal_observer_lower_impossible (M : ChargedMachine) :
    ¬ (∀ S : ObserverScheme M, ¬ PolyBounded (schemeResource S)) := by
  intro h
  exact h (decisionScheme M) (decisionScheme_polyBounded M)

end PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse.decisionObserver_innovation_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse.decisionScheme_resource_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse.decisionScheme_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserverCollapse.universal_observer_lower_impossible
