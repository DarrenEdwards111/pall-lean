import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedHolographicMachine

/-!
# Finite length-indexed observers for every charged machine

The charged TM has an infinite ambient configuration space, so a single finite quotient of *all* configurations
need not exist.  Complexity only uses the bounded runs on inputs of one length.  This file constructs the
canonical finite carrier of those runs:

`ReachablePoint M n = (input : Fin n → Bool) × (time : Fin (M.clock n + 1))`.

Its boundary map reconstructs the genuine TM configuration after `time` charged steps.  Time advancement is
saturating; before the clock boundary, advancing the observer corresponds exactly to one concrete TM step.
The final observer output equals the machine decision.

Thus every charged machine has a finite, causal, decision-sufficient observer at each input length.  The carrier
has exactly `2^n · (clock n + 1)` states.  This closes the *existence/coverage* gap left by
`ComputationalDepthChargedHolographicMachine`.

It does not yet give an intrinsic lower-bound measure: the canonical carrier remembers the entire input and
time.  The next step is minimisation/quotienting by causal observational equivalence and proving simulation
invariance before attempting a SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver

open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine

/-- A point on a bounded execution: an input of length `n` and a charged time at most `clock n`. -/
structure ReachablePoint (M : ChargedMachine) (n : Nat) where
  input : Fin n → Bool
  time : Fin (M.clock n + 1)
deriving DecidableEq, Fintype

/-- The real machine configuration represented by a bounded execution point. -/
def boundary {M : ChargedMachine} {n : Nat} (p : ReachablePoint M n) : Config M :=
  run M p.time.val (init M (List.ofFn p.input))

/-- Saturating time successor. -/
def nextTime {T : Nat} (t : Fin (T + 1)) : Fin (T + 1) :=
  ⟨min (t.val + 1) T, Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩

/-- Advance one observer step, saturating at the clock boundary. -/
def nextPoint {M : ChargedMachine} {n : Nat} (p : ReachablePoint M n) : ReachablePoint M n :=
  ⟨p.input, nextTime p.time⟩

theorem nextTime_val_of_lt {T : Nat} (t : Fin (T + 1)) (h : t.val < T) :
    (nextTime t).val = t.val + 1 := by
  have hle : t.val + 1 ≤ T := h
  simp [nextTime, Nat.min_eq_left hle]

/-- Before the terminal clock boundary, observer advancement is exactly one charged TM transition. -/
theorem boundary_next {M : ChargedMachine} {n : Nat} (p : ReachablePoint M n)
    (h : p.time.val < M.clock n) :
    boundary (nextPoint p) = step M (boundary p) := by
  unfold boundary nextPoint
  rw [nextTime_val_of_lt p.time h]
  simp [run, Function.iterate_succ_apply']

/-- The initial observer point for a length-`n` input. -/
def initialPoint (M : ChargedMachine) {n : Nat} (a : Fin n → Bool) : ReachablePoint M n :=
  ⟨a, ⟨0, by omega⟩⟩

/-- The terminal observer point at the machine's charged clock. -/
def finalPoint (M : ChargedMachine) {n : Nat} (a : Fin n → Bool) : ReachablePoint M n :=
  ⟨a, ⟨M.clock n, by omega⟩⟩

@[simp] theorem boundary_initial (M : ChargedMachine) {n : Nat} (a : Fin n → Bool) :
    boundary (initialPoint M a) = init M (List.ofFn a) := by
  simp [boundary, initialPoint, run]

@[simp] theorem boundary_final (M : ChargedMachine) {n : Nat} (a : Fin n → Bool) :
    boundary (finalPoint M a) = run M (M.clock n) (init M (List.ofFn a)) := rfl

/-- Reading acceptance from the terminal boundary gives exactly the charged machine decision. -/
theorem final_output_correct (M : ChargedMachine) {n : Nat} (a : Fin n → Bool) :
    M.accept (boundary (finalPoint M a)).state =
      ChargedHolographicMachine.decide M (List.ofFn a) := by
  simp [boundary, finalPoint, ChargedHolographicMachine.decide]

/-- A finite causal observer of all charged runs at one input length.  Causality is required precisely on
nonterminal points; terminal saturation need not simulate an extra machine step. -/
structure LengthObserver (M : ChargedMachine) (n : Nat) where
  State : Type
  stateFintype : Fintype State
  stateDecEq : DecidableEq State
  observe : ReachablePoint M n → State
  observedNext : State → State
  observedOutput : State → Bool
  step_commutes : ∀ p, p.time.val < M.clock n → observe (nextPoint p) = observedNext (observe p)
  output_factors : ∀ a, observedOutput (observe (finalPoint M a)) =
    ChargedHolographicMachine.decide M (List.ofFn a)

attribute [instance] LengthObserver.stateFintype LengthObserver.stateDecEq

/-- The canonical observer: retain the bounded execution point itself. -/
def canonicalObserver (M : ChargedMachine) (n : Nat) : LengthObserver M n where
  State := ReachablePoint M n
  stateFintype := inferInstance
  stateDecEq := inferInstance
  observe := id
  observedNext := nextPoint
  observedOutput := fun p => M.accept (boundary p).state
  step_commutes := fun _ _ => rfl
  output_factors := final_output_correct M

/-- **Coverage theorem.** Every charged machine has a finite causal, decision-sufficient observer at every
input length. -/
theorem exists_lengthObserver (M : ChargedMachine) (n : Nat) : Nonempty (LengthObserver M n) :=
  ⟨canonicalObserver M n⟩

/-- The bounded trace carrier is definitionally a product of input and time. -/
def reachablePointEquiv (M : ChargedMachine) (n : Nat) :
    ReachablePoint M n ≃ ((Fin n → Bool) × Fin (M.clock n + 1)) where
  toFun := fun p => (p.input, p.time)
  invFun := fun p => ⟨p.1, p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Exact size of the canonical bounded trace carrier. -/
theorem card_reachablePoint (M : ChargedMachine) (n : Nat) :
    Fintype.card (ReachablePoint M n) = 2 ^ n * (M.clock n + 1) := by
  rw [Fintype.card_congr (reachablePointEquiv M n)]
  simp

end PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver.boundary_next
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver.final_output_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver.exists_lengthObserver
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver.card_reachablePoint
