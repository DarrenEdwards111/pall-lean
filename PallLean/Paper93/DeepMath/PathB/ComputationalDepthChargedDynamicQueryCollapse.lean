import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedDynamicQueryInnovation

/-!
# The dynamic query-innovation measure also collapses over all schemes

`ComputationalDepthChargedDynamicQueryInnovation` shows the dynamic profile-change measure clears `PUpper`
(it is `≤ clock`) and that the *time-invariant* `eqTraceProfile` has `2^n` static profiles yet zero dynamic
innovation.  That zero is presented there as *avoiding* the equality trap.  This file records the other reading
of the same fact: a time-invariant profile has zero dynamic innovation **for every input**, so the dynamic
measure inherits exactly the final-decision collapse of
`ComputationalDepthChargedLengthObserverCollapse`.

* `answerSemantics` — the trivial time-invariant scheme whose single query returns the machine's decision.  It is
  a valid `ContinuationSemantics` (causal + decision-sufficient) with **zero** cumulative dynamic innovation on
  every input, hence `answerScheme_polyBounded`.
* `universal_dynamic_lower_impossible` — therefore **no** language can have super-polynomial dynamic innovation
  against *every* valid query scheme: the answer scheme is a zero-cost counterexample.  This is the exact analogue
  of `universal_observer_lower_impossible` for the dynamic measure.
* `richSemantics` / `richScheme_distinguishes` + `richScheme_dynamic_zero` — sharper: a scheme can be *rich*
  (its `2^n` query profiles separate distinct inputs, so it does **not** collapse to the final bit under
  `profile_ne_of_query`) and *still* have zero dynamic innovation.  So "rich enough to block final-bit collapse"
  does **not** force nonzero dynamic innovation; the missing ingredient is genuine time-variation.

## Consequence for the socket

`SATLower` for this measure cannot be quantified over all valid schemes (impossible), so it must be restricted to
a class of *canonical, time-varying, non-collapsing* schemes.  But a decision-relevant time-varying profile tracks
the computation, driving innovation back to `≈ clock`.  So the dynamic measure sits on both horns at once:
time-invariant schemes collapse it to `0`; time-varying decision-relevant schemes push it to the runtime ceiling
where `SATLower = SAT ∉ P`.  No complexity separation is proved here; this is a machine-checked scope no-go.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryCollapse

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver
open PallLean.Paper93.DeepMath.PathB.ChargedContinuationQuotient
open PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryInnovation

/-! ## The trivial time-invariant "answer" scheme collapses the dynamic measure -/

/-- The time-invariant scheme whose one query returns the machine's decision on the point's input. -/
def answerSemantics (M : ChargedMachine) (n : Nat) : ContinuationSemantics M n where
  Query := Unit
  queryFintype := inferInstance
  queryDecEq := inferInstance
  response := fun p _ => ChargedHolographicMachine.decide M (List.ofFn p.input)
  outputQuery := ()
  output_correct := fun _ => rfl
  next_respects := fun _ _ h => h

/-- The answer scheme's profile never changes along a run (it ignores time). -/
theorem answerScheme_profile_time_invariant (M : ChargedMachine) (n : Nat)
    (a : Fin n → Bool) (t : Fin (M.clock n)) :
    profile (answerSemantics M n) (timePoint a t) = profile (answerSemantics M n) (succTimePoint a t) :=
  rfl

theorem answerScheme_dynamic_zero (M : ChargedMachine) (n : Nat) (a : Fin n → Bool) :
    profileInnovation (answerSemantics M n) a = 0 := by
  unfold profileInnovation
  apply Finset.sum_eq_zero
  intro t _
  rw [if_neg]
  rw [answerScheme_profile_time_invariant]
  exact fun h => h rfl

/-- The dynamic resource of the answer scheme is identically zero. -/
def answerScheme (M : ChargedMachine) : QueryScheme M := fun n => answerSemantics M n

theorem answerScheme_resource_zero (M : ChargedMachine) (n : Nat) :
    schemeResource (answerScheme M) n = 0 := by
  unfold schemeResource dynamicQueryResource
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro a _
  exact (answerScheme_dynamic_zero M n a).le

theorem answerScheme_polyBounded (M : ChargedMachine) :
    PolyBounded (schemeResource (answerScheme M)) :=
  ⟨0, 0, fun n => by rw [answerScheme_resource_zero]; exact Nat.zero_le _⟩

/-- **The dynamic measure also collapses.**  No language can have super-polynomial dynamic query innovation
against every valid scheme — the time-invariant answer scheme is always a zero-cost counterexample.  Exact
analogue of `universal_observer_lower_impossible`. -/
theorem universal_dynamic_lower_impossible (M : ChargedMachine) :
    ¬ (∀ S : QueryScheme M, ¬ PolyBounded (schemeResource S)) :=
  fun h => h (answerScheme M) (answerScheme_polyBounded M)

/-! ## Rich (non-final-bit) yet zero-innovation: richness is not the missing ingredient -/

/-- A rich time-invariant scheme: besides the decision query it exposes one equality query per candidate input,
so distinct inputs get distinct profiles. -/
def richSemantics (M : ChargedMachine) (n : Nat) : ContinuationSemantics M n where
  Query := Option (Fin n → Bool)
  queryFintype := inferInstance
  queryDecEq := inferInstance
  response := fun p q =>
    match q with
    | none => ChargedHolographicMachine.decide M (List.ofFn p.input)
    | some b => decide (p.input = b)
  outputQuery := none
  output_correct := fun _ => rfl
  next_respects := fun _ _ h => h

theorem richScheme_profile_time_invariant (M : ChargedMachine) (n : Nat)
    (a : Fin n → Bool) (t : Fin (M.clock n)) :
    profile (richSemantics M n) (timePoint a t) = profile (richSemantics M n) (succTimePoint a t) :=
  rfl

/-- The rich scheme still has zero dynamic innovation (it is time-invariant). -/
theorem richScheme_dynamic_zero (M : ChargedMachine) (n : Nat) (a : Fin n → Bool) :
    profileInnovation (richSemantics M n) a = 0 := by
  unfold profileInnovation
  apply Finset.sum_eq_zero
  intro t _
  rw [if_neg]
  rw [richScheme_profile_time_invariant]
  exact fun h => h rfl

/-- Yet the rich scheme is not the final-bit collapse: distinct inputs occupy distinct intrinsic classes. -/
theorem richScheme_distinguishes (M : ChargedMachine) (n : Nat) (p q : ReachablePoint M n)
    (hpq : p.input ≠ q.input) :
    profile (richSemantics M n) p ≠ profile (richSemantics M n) q := by
  apply profile_ne_of_query (richSemantics M n) p q (some p.input)
  have h1 : (richSemantics M n).response p (some p.input) = true := by
    show decide (p.input = p.input) = true
    simp
  have h2 : (richSemantics M n).response q (some p.input) = false := by
    show decide (q.input = p.input) = false
    exact decide_eq_false (fun h => hpq h.symm)
  rw [h1, h2]
  decide

end PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryCollapse.universal_dynamic_lower_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryCollapse.richScheme_dynamic_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedDynamicQueryCollapse.richScheme_distinguishes
