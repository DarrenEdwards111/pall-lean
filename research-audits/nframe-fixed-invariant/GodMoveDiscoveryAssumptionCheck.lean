import GodMoveMachineDiscoveryPrecision

/-!
# The SAT correctness hypothesis is essential

The revised discovery program always has its proved query-count and
coefficient-precision bounds. These bounds do not imply discovery correctness.
An explicit machine that halts immediately and rejects every word has the
zero polynomial clock, but returns no samples even for the constant-true
one-gate circuit. Its samples therefore fail to separate the wire space.

This is a kernel-checked counterexample to dropping `Decides M SATLang T`,
not a counterexample to the conditional construction theorem.
-/

namespace GodMoveDiscoveryAssumptionCheck

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveRationalRowBasis
open GodMoveMachineCircuitOracle GodMoveMachineRowFinder GodMoveMachineDiscovery
open GodMoveMachineDiscoveryPrecision GodMoveSamplingBarrier
open GodMoveRationalMachineQuery
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine SeparationTarget
open NFrameBoundaryTransducer (CGate output)

/-- A genuine finite-control machine, already halted, that rejects every word. -/
def rejectMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => true
  δ := fun _ _ => ((), none, 2)
  accept := fun _ => false

def zeroClock : ℕ → ℕ := fun _ => 0

theorem zeroClock_polynomial : PvsNPSeparatingInvariant.PolyBounded zeroClock := by
  exact ⟨0, 0, fun _ => Nat.le_refl 0⟩

theorem rejectMachine_halts (x : List Bool) (t : ℕ) : HaltsBy rejectMachine x t := rfl

theorem rejectMachine_answer (x : List Bool) (t : ℕ) :
    decideOut rejectMachine x t = false := rfl

theorem reject_circuitSAT (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    circuitSAT rejectMachine T c = false := rfl

theorem reject_findWitness (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    findWitnessWithCount rejectMachine T c = (none, 1) := by
  simp only [findWitnessWithCount, reject_circuitSAT, Bool.false_eq_true, ↓reduceIte]

theorem reject_rowAttempt (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (j : Fin c.length) :
    rowAttempt rejectMachine T c B j = (none, 1) := by
  unfold rowAttempt rationalWitnessWithCount
  exact reject_findWitness T _

theorem reject_findIn (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) (js : List (Fin c.length)) :
    findIn rejectMachine T c B js = (none, js.length) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [findIn, reject_rowAttempt, ih, List.length_cons]
      congr 1
      omega

theorem reject_findRow (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n))
    (B : RowBasis c.length) :
    findRowWithCount rejectMachine T c B = (none, c.length) := by
  simp only [findRowWithCount, reject_findIn, List.length_ofFn]

/-- Even though every machine call halts, no assignment is ever selected. -/
theorem reject_machineSamples (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    machineSamples rejectMachine T c = [] := by
  simp only [machineSamples, machineSearch, discover, reject_findRow]

theorem reject_machineSearch_queries (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    (machineSearch rejectMachine T c).queries = c.length := by
  simp only [machineSearch, discover, reject_findRow]

def trueCircuit : List (CGate 0) := [.cst true]

theorem trueCircuit_accepts : ∃ a : Assignment 0, output trueCircuit a = true :=
  ⟨fun i => Fin.elim0 i, rfl⟩

/-- SAT correctness cannot be recovered from immediate halting or a small clock. -/
theorem rejectMachine_not_decides (T : ℕ → ℕ) : ¬ Decides rejectMachine SATLang T := by
  intro hD
  have hyes := (circuitSAT_correct rejectMachine T hD trueCircuit).mpr trueCircuit_accepts
  rw [reject_circuitSAT] at hyes
  contradiction

/-- Dropping the supplied SAT correctness hypothesis makes separation false
already on one constant gate and no external inputs. -/
theorem reject_samples_not_separating (T : ℕ → ℕ) :
    ¬ SeparatesWires trueCircuit (machineSamples rejectMachine T trueCircuit) := by
  intro hsep
  have h := (exists_accept_iff_sample_accepts trueCircuit
    (machineSamples rejectMachine T trueCircuit) hsep).mp trueCircuit_accepts
  rw [reject_machineSamples] at h
  exact Bool.noConfusion h

/-- The previously proved numerical bounds hold on this failing computation.
They therefore cannot replace the missing semantic hypothesis. -/
theorem bounded_but_incorrect :
    PvsNPSeparatingInvariant.PolyBounded zeroClock ∧
    (∀ x, HaltsBy rejectMachine x (zeroClock x.length)) ∧
    (machineSearch rejectMachine zeroClock trueCircuit).queries ≤
      (trueCircuit.length + 1) * (trueCircuit.length * (0 + 1)) ∧
    DiscoveryPrecision rejectMachine zeroClock trueCircuit
      (trueCircuit.length + 1) (empty trueCircuit.length) ∧
    ¬ SeparatesWires trueCircuit (machineSamples rejectMachine zeroClock trueCircuit) :=
  ⟨zeroClock_polynomial, fun x => rejectMachine_halts x _,
    machineSearch_queries_le rejectMachine zeroClock trueCircuit,
    machineSearch_precision rejectMachine zeroClock trueCircuit,
    reject_samples_not_separating zeroClock⟩

end GodMoveDiscoveryAssumptionCheck

#print axioms GodMoveDiscoveryAssumptionCheck.zeroClock_polynomial
#print axioms GodMoveDiscoveryAssumptionCheck.rejectMachine_halts
#print axioms GodMoveDiscoveryAssumptionCheck.reject_machineSamples
#print axioms GodMoveDiscoveryAssumptionCheck.reject_machineSearch_queries
#print axioms GodMoveDiscoveryAssumptionCheck.rejectMachine_not_decides
#print axioms GodMoveDiscoveryAssumptionCheck.reject_samples_not_separating
#print axioms GodMoveDiscoveryAssumptionCheck.bounded_but_incorrect
