import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine

/-!
# Fixed runtime metadata locator for zero-copy rebasing

The previous executable rebase writer receives its absolute splice offset as
finite-control data.  This file supplies the first genuinely uniform piece of
the replacement: one fixed machine scans a tape-resident doubled unary field
and halts immediately after its `01` boundary.  Its state space is independent
of the encoded number, the input, and the live schedule round.

The locator is proved both at the tape origin and behind an arbitrary prefix.
Thus later composition may place rebase metadata in consumed workspace and
hand the resulting head position to a fixed writer without compiling that
position into the machine state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact

inductive RebaseUnaryLocatorState
  | low
  | high (lo : Bool)
  | done
  deriving DecidableEq, Fintype

/-- A fixed pair scanner for a doubled unary field `11* 01`. -/
def rebaseUnaryLocatorMachine : Machine where
  State := RebaseUnaryLocatorState
  fin := inferInstance
  dec := inferInstance
  start := .low
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .low => (.high b, none, 1)
    | .high lo =>
        if lo && b then (.low, none, 1)
        else if !lo && b then (.done, none, 1)
        else (.done, none, 2)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem step_locator_low (p : Nat) (T : List Bool) :
    step rebaseUnaryLocatorMachine ⟨.low, p, T⟩ =
      ⟨.high (T.getD p false), p + 1, T⟩ := by
  simp [step, rebaseUnaryLocatorMachine, moveHead]

theorem step_locator_data (p : Nat) (T : List Bool)
    (h : T.getD p false = true) :
    step rebaseUnaryLocatorMachine ⟨.high true, p, T⟩ =
      ⟨.low, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rebaseUnaryLocatorMachine, moveHead, h]

theorem step_locator_boundary (p : Nat) (T : List Bool)
    (h : T.getD p false = true) :
    step rebaseUnaryLocatorMachine ⟨.high false, p, T⟩ =
      ⟨.done, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, rebaseUnaryLocatorMachine, moveHead, h]

/-- Scan any `k` complete `11` pairs under a pointwise tape hypothesis. -/
theorem rebaseUnaryLocator_run_data (T : List Bool) (q k : Nat)
    (h : ∀ i, i < 2 * k → T.getD (q + i) false = true) :
    run rebaseUnaryLocatorMachine (2 * k) ⟨.low, q, T⟩ =
      ⟨.low, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h0 : T.getD (q + 2 * k) false = true := by
        apply h
        omega
      have h1 : T.getD (q + 2 * k + 1) false = true := by
        simpa [Nat.add_assoc] using h (2 * k + 1) (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add,
        ih (fun i hi => h i (by omega)), run_succ, run_succ, run_zero,
        step_locator_low, h0, step_locator_data _ _ h1]
      congr 1

theorem prefixed_unary_getD_data (pre tail : List Bool) (n c : Nat)
    (hc : c < 2 * n) :
    (pre ++ unaryD n ++ tail).getD (pre.length + c) false = true := by
  rw [List.append_assoc]
  rw [List.getD_append_right (h := by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getD_append (h := by rw [unaryD_length]; omega)]
  exact unaryD_getD_data n c hc

theorem prefixed_unary_getD_markLo (pre tail : List Bool) (n : Nat) :
    (pre ++ unaryD n ++ tail).getD (pre.length + 2 * n) false = false := by
  rw [List.append_assoc]
  rw [List.getD_append_right (h := by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getD_append (h := by rw [unaryD_length]; omega)]
  exact unaryD_getD_markLo n

theorem prefixed_unary_getD_markHi (pre tail : List Bool) (n : Nat) :
    (pre ++ unaryD n ++ tail).getD (pre.length + 2 * n + 1) false = true := by
  rw [List.append_assoc]
  rw [List.getD_append_right (h := by omega)]
  rw [show pre.length + 2 * n + 1 - pre.length = 2 * n + 1 by omega]
  rw [List.getD_append (h := by rw [unaryD_length]; omega)]
  exact unaryD_getD_markHi n

/-- Exact fixed-machine run behind an arbitrary protected prefix. -/
theorem rebaseUnaryLocator_run_prefixed (pre tail : List Bool) (n : Nat) :
    run rebaseUnaryLocatorMachine (2 * n + 2)
        ⟨.low, pre.length, pre ++ unaryD n ++ tail⟩ =
      ⟨.done, pre.length + 2 * n + 2, pre ++ unaryD n ++ tail⟩ := by
  let T := pre ++ unaryD n ++ tail
  have hdata : ∀ i, i < 2 * n →
      T.getD (pre.length + i) false = true := by
    intro i hi
    exact prefixed_unary_getD_data pre tail n i hi
  have hlo : T.getD (pre.length + 2 * n) false = false :=
    prefixed_unary_getD_markLo pre tail n
  have hhi : T.getD (pre.length + 2 * n + 1) false = true :=
    prefixed_unary_getD_markHi pre tail n
  rw [show 2 * n + 2 = 2 * n + 2 by rfl, run_add,
    rebaseUnaryLocator_run_data T pre.length n hdata,
    run_succ, run_succ, run_zero, step_locator_low, hlo,
    step_locator_boundary _ _ hhi]

/-- Origin specialization: the encoded value affects only the runtime and
final head, never the finite controller. -/
theorem rebaseUnaryLocator_run (n : Nat) (tail : List Bool) :
    run rebaseUnaryLocatorMachine (2 * n + 2)
        (init rebaseUnaryLocatorMachine (unaryD n ++ tail)) =
      ⟨.done, 2 * n + 2, unaryD n ++ tail⟩ := by
  simpa using rebaseUnaryLocator_run_prefixed [] tail n

theorem rebaseUnaryLocator_halted (n : Nat) (tail : List Bool) :
    rebaseUnaryLocatorMachine.halt
      (run rebaseUnaryLocatorMachine (2 * n + 2)
        (init rebaseUnaryLocatorMachine (unaryD n ++ tail))).st = true := by
  rw [rebaseUnaryLocator_run]
  rfl

/-! ## Two-field runtime rebase metadata

The splice location and remaining archive size may be stored as two adjacent
doubled-unary fields.  Head-preserving composition of the same fixed scanner
reads both fields without adding either value to the controller state.
-/

/-- One fixed controller that crosses the runtime splice and remaining-count
fields consecutively. -/
def rebaseMetadataLocatorMachine : Machine :=
  headSeqMachine rebaseUnaryLocatorMachine rebaseUnaryLocatorMachine

def rebaseMetadataLocatorClock (R d : Nat) : Nat :=
  (2 * R + 2) + 1 + (2 * d + 2)

theorem rebaseMetadataLocator_run (R d : Nat) (tail : List Bool) :
    run rebaseMetadataLocatorMachine (rebaseMetadataLocatorClock R d)
        (init rebaseMetadataLocatorMachine
          (unaryD R ++ unaryD d ++ tail)) =
      ⟨Sum.inr .done, 2 * R + 2 + 2 * d + 2,
        unaryD R ++ unaryD d ++ tail⟩ := by
  let T := unaryD R ++ unaryD d ++ tail
  have h1 : run rebaseUnaryLocatorMachine (2 * R + 2)
      (init rebaseUnaryLocatorMachine T) =
      ⟨.done, 2 * R + 2, T⟩ := by
    simpa [T, List.append_assoc] using
      rebaseUnaryLocator_run R (unaryD d ++ tail)
  have hh1 : rebaseUnaryLocatorMachine.halt .done = true := rfl
  have h2 : run rebaseUnaryLocatorMachine (2 * d + 2)
      ⟨rebaseUnaryLocatorMachine.start, 2 * R + 2, T⟩ =
      ⟨.done, 2 * R + 2 + 2 * d + 2, T⟩ := by
    have hp := rebaseUnaryLocator_run_prefixed (unaryD R) tail d
    simpa [T, rebaseUnaryLocatorMachine, unaryD_length,
      Nat.add_assoc] using hp
  have hh2 : rebaseUnaryLocatorMachine.halt .done = true := rfl
  exact headSeq_run rebaseUnaryLocatorMachine rebaseUnaryLocatorMachine
    T T T (2 * R + 2) (2 * d + 2) (2 * R + 2)
    (2 * R + 2 + 2 * d + 2) .done .done h1 hh1 h2 hh2

theorem rebaseMetadataLocator_halted (R d : Nat) (tail : List Bool) :
    rebaseMetadataLocatorMachine.halt
      (run rebaseMetadataLocatorMachine (rebaseMetadataLocatorClock R d)
        (init rebaseMetadataLocatorMachine
          (unaryD R ++ unaryD d ++ tail))).st = true := by
  rw [rebaseMetadataLocator_run]
  rfl

/-- The fresh zero-copy selector prefix is exactly the unary field understood
by the fixed locator. -/
theorem zeroCopyRebasePrefix_eq_unaryD (d : Nat) :
    zeroCopyRebasePrefix d = unaryD d := by
  rw [zeroCopyRebasePrefix, unaryD_eq]
  rw [flattenPairs_append]
  congr 1
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [List.replicate_succ, flattenPairs]
      rw [show 2 * (d + 1) = 2 + 2 * d by omega,
        List.replicate_add, ih]
      rfl

/-- Consequently the fixed locator crosses a runtime-generated rebase prefix
and stops exactly at the first untouched future-archive cell. -/
theorem rebaseUnaryLocator_zeroCopyPrefix (d : Nat) (archive : List Bool) :
    run rebaseUnaryLocatorMachine (2 * d + 2)
        (init rebaseUnaryLocatorMachine
          (zeroCopyRebasePrefix d ++ archive)) =
      ⟨.done, (zeroCopyRebasePrefix d).length,
        zeroCopyRebasePrefix d ++ archive⟩ := by
  rw [zeroCopyRebasePrefix_eq_unaryD,
    rebaseUnaryLocator_run, unaryD_length]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator.rebaseUnaryLocator_run_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator.rebaseMetadataLocator_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRebaseLocator.rebaseUnaryLocator_zeroCopyPrefix
