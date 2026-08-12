import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeFixedOuterRound

/-!
# One fixed controller for the repeated outer shift

This controller internalizes the three certified phase machines.  Handoffs
preserve head and tape.  Exhaustion state `more` loops to the universal
forward pass; `final` enters the sole genuine halt state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUniversalPassedShift
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeProgressReturn

inductive RuntimeFixedOuterControllerState
  | shift (s : RuntimeUniversalPassedShiftState)
  | ret (s : RuntimeProgressReturnState)
  | exhaust (s : RuntimeProgressExhaustState)
  | final
  deriving DecidableEq, Fintype

/-- The complete outer loop has one constant finite state type.  No payload,
record length, offset, schedule, or round number occurs in control. -/
def runtimeFixedOuterControllerMachine : Machine where
  State := RuntimeFixedOuterControllerState
  fin := inferInstance
  dec := inferInstance
  start := .shift runtimeUniversalPassedShiftMachine.start
  halt := fun s => decide (s = .final)
  δ := fun s b =>
    match s with
    | .shift ss =>
        if runtimeUniversalPassedShiftMachine.halt ss then
          (.ret runtimeProgressReturnMachine.start, none, 2)
        else
          let tr := runtimeUniversalPassedShiftMachine.δ ss b
          (.shift tr.1, tr.2.1, tr.2.2)
    | .ret sr =>
        if runtimeProgressReturnMachine.halt sr then
          (.exhaust runtimeProgressExhaustMachine.start, none, 2)
        else
          let tr := runtimeProgressReturnMachine.δ sr b
          (.ret tr.1, tr.2.1, tr.2.2)
    | .exhaust se =>
        if se = .more then
          (.shift runtimeUniversalPassedShiftMachine.start, none, 2)
        else if se = .final then
          (.final, none, 2)
        else
          let tr := runtimeProgressExhaustMachine.δ se b
          (.exhaust tr.1, tr.2.1, tr.2.2)
    | .final => (.final, none, 2)
  accept := fun s => decide (s = .final)

def outerShiftCfg (c : Cfg runtimeUniversalPassedShiftMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.shift c.st, c.hd, c.tp⟩

def outerReturnCfg (c : Cfg runtimeProgressReturnMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.ret c.st, c.hd, c.tp⟩

def outerExhaustCfg (c : Cfg runtimeProgressExhaustMachine) :
    Cfg runtimeFixedOuterControllerMachine :=
  ⟨.exhaust c.st, c.hd, c.tp⟩

theorem runtimeFixedOuterController_shift_step
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : runtimeUniversalPassedShiftMachine.halt c.st = false) :
    step runtimeFixedOuterControllerMachine (outerShiftCfg c) =
      outerShiftCfg (step runtimeUniversalPassedShiftMachine c) := by
  simp [step, runtimeFixedOuterControllerMachine, outerShiftCfg, h]

theorem runtimeFixedOuterController_shift_handoff
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (h : runtimeUniversalPassedShiftMachine.halt c.st = true) :
    step runtimeFixedOuterControllerMachine (outerShiftCfg c) =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start, c.hd, c.tp⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, outerShiftCfg,
    outerReturnCfg, h, moveHead]

theorem runtimeFixedOuterController_return_step
    (c : Cfg runtimeProgressReturnMachine)
    (h : runtimeProgressReturnMachine.halt c.st = false) :
    step runtimeFixedOuterControllerMachine (outerReturnCfg c) =
      outerReturnCfg (step runtimeProgressReturnMachine c) := by
  simp [step, runtimeFixedOuterControllerMachine, outerReturnCfg, h]

theorem runtimeFixedOuterController_return_handoff
    (c : Cfg runtimeProgressReturnMachine)
    (h : runtimeProgressReturnMachine.halt c.st = true) :
    step runtimeFixedOuterControllerMachine (outerReturnCfg c) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, c.hd, c.tp⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, outerReturnCfg,
    outerExhaustCfg, h, moveHead]

theorem runtimeFixedOuterController_exhaust_step
    (c : Cfg runtimeProgressExhaustMachine)
    (hm : c.st ≠ .more) (hf : c.st ≠ .final) :
    step runtimeFixedOuterControllerMachine (outerExhaustCfg c) =
      outerExhaustCfg (step runtimeProgressExhaustMachine c) := by
  have hh : runtimeProgressExhaustMachine.halt c.st = false := by
    simp [runtimeProgressExhaustMachine, hm, hf]
  simp [step, runtimeFixedOuterControllerMachine, outerExhaustCfg, hm, hf, hh]

/-- The physical `more` decision loops to the universal forward pass without
moving the head or changing tape. -/
theorem runtimeFixedOuterController_more_handoff
    (p : Nat) (T : List Bool) :
    step runtimeFixedOuterControllerMachine
        ⟨RuntimeFixedOuterControllerState.exhaust .more, p, T⟩ =
      ⟨runtimeFixedOuterControllerMachine.start, p, T⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, moveHead]

/-- The physical sentinel decision enters the sole genuine halt state,
again without moving the head or changing tape. -/
theorem runtimeFixedOuterController_final_handoff
    (p : Nat) (T : List Bool) :
    step runtimeFixedOuterControllerMachine
        ⟨RuntimeFixedOuterControllerState.exhaust .final, p, T⟩ =
      ⟨RuntimeFixedOuterControllerState.final, p, T⟩ := by
  simp [step, runtimeFixedOuterControllerMachine, moveHead]

/-! ## Exact run lifting through the wrapper -/

theorem runtimeFixedOuterController_shift_run
    (c : Cfg runtimeUniversalPassedShiftMachine) (t : Nat)
    (hno : ∀ i < t, runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false) :
    run runtimeFixedOuterControllerMachine t (outerShiftCfg c) =
      outerShiftCfg (run runtimeUniversalPassedShiftMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_shift_step _ (hno t (by omega)),
        ← run_succ]

theorem runtimeFixedOuterController_shift_run_handoff
    (c : Cfg runtimeUniversalPassedShiftMachine) (t : Nat)
    (hno : ∀ i < t, runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false)
    (hh : runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine t c).st = true) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerShiftCfg c) =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          (run runtimeUniversalPassedShiftMachine t c).hd,
          (run runtimeUniversalPassedShiftMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_shift_run c t hno,
    runtimeFixedOuterController_shift_handoff _ hh]

theorem runtimeFixedOuterController_shift_leftSafe
    (c : Cfg runtimeUniversalPassedShiftMachine) (t : Nat)
    (hno : ∀ i < t, runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false)
    (hsafe : LeftSafeRun runtimeUniversalPassedShiftMachine c t) :
    LeftSafeRun runtimeFixedOuterControllerMachine (outerShiftCfg c) t := by
  intro i hi hhalt hmove
  have hrun := runtimeFixedOuterController_shift_run c i
    (fun j hj => hno j (by omega))
  rw [hrun] at hhalt hmove ⊢
  simp only [outerShiftCfg] at hhalt hmove ⊢
  have hlocalHalt : runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine i c).st = false := hno i hi
  simp [runtimeFixedOuterControllerMachine, hlocalHalt] at hmove
  exact hsafe i hi hlocalHalt hmove

theorem runtimeFixedOuterController_shift_handoff_leftSafe
    (c : Cfg runtimeUniversalPassedShiftMachine)
    (hh : runtimeUniversalPassedShiftMachine.halt c.st = true) :
    LeftSafeRun runtimeFixedOuterControllerMachine (outerShiftCfg c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [runtimeFixedOuterControllerMachine, outerShiftCfg, hh]

theorem runtimeFixedOuterController_return_run
    (c : Cfg runtimeProgressReturnMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false) :
    run runtimeFixedOuterControllerMachine t (outerReturnCfg c) =
      outerReturnCfg (run runtimeProgressReturnMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_return_step _ (hno t (by omega)),
        ← run_succ]

theorem runtimeFixedOuterController_return_run_handoff
    (c : Cfg runtimeProgressReturnMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false)
    (hh : runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine t c).st = true) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerReturnCfg c) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start,
          (run runtimeProgressReturnMachine t c).hd,
          (run runtimeProgressReturnMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_return_run c t hno,
    runtimeFixedOuterController_return_handoff _ hh]

theorem runtimeFixedOuterController_return_leftSafe
    (c : Cfg runtimeProgressReturnMachine) (t : Nat)
    (hno : ∀ i < t, runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false)
    (hsafe : LeftSafeRun runtimeProgressReturnMachine c t) :
    LeftSafeRun runtimeFixedOuterControllerMachine (outerReturnCfg c) t := by
  intro i hi hhalt hmove
  have hrun := runtimeFixedOuterController_return_run c i
    (fun j hj => hno j (by omega))
  rw [hrun] at hhalt hmove ⊢
  simp only [outerReturnCfg] at hhalt hmove ⊢
  have hlocalHalt : runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine i c).st = false := hno i hi
  simp [runtimeFixedOuterControllerMachine, hlocalHalt] at hmove
  exact hsafe i hi hlocalHalt hmove

theorem runtimeFixedOuterController_return_handoff_leftSafe
    (c : Cfg runtimeProgressReturnMachine)
    (hh : runtimeProgressReturnMachine.halt c.st = true) :
    LeftSafeRun runtimeFixedOuterControllerMachine (outerReturnCfg c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [runtimeFixedOuterControllerMachine, outerReturnCfg, hh]

theorem runtimeFixedOuterController_exhaust_run
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final) :
    run runtimeFixedOuterControllerMachine t (outerExhaustCfg c) =
      outerExhaustCfg (run runtimeProgressExhaustMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih (fun i hi => hno i (by omega)),
        runtimeFixedOuterController_exhaust_step _
          (hno t (by omega)).1 (hno t (by omega)).2,
        ← run_succ]

theorem runtimeFixedOuterController_exhaust_more_run_handoff
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final)
    (hm : (run runtimeProgressExhaustMachine t c).st = .more) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerExhaustCfg c) =
      ⟨runtimeFixedOuterControllerMachine.start,
        (run runtimeProgressExhaustMachine t c).hd,
        (run runtimeProgressExhaustMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_exhaust_run c t hno]
  cases hrun : run runtimeProgressExhaustMachine t c
  simp only [hrun] at hm ⊢
  subst hm
  exact runtimeFixedOuterController_more_handoff _ _

theorem runtimeFixedOuterController_exhaust_final_run_handoff
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final)
    (hf : (run runtimeProgressExhaustMachine t c).st = .final) :
    run runtimeFixedOuterControllerMachine (t + 1) (outerExhaustCfg c) =
      ⟨RuntimeFixedOuterControllerState.final,
        (run runtimeProgressExhaustMachine t c).hd,
        (run runtimeProgressExhaustMachine t c).tp⟩ := by
  rw [run_succ, runtimeFixedOuterController_exhaust_run c t hno]
  cases hrun : run runtimeProgressExhaustMachine t c
  simp only [hrun] at hf ⊢
  subst hf
  exact runtimeFixedOuterController_final_handoff _ _

theorem runtimeFixedOuterController_exhaust_leftSafe
    (c : Cfg runtimeProgressExhaustMachine) (t : Nat)
    (hno : ∀ i < t,
      (run runtimeProgressExhaustMachine i c).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i c).st ≠ .final)
    (hsafe : LeftSafeRun runtimeProgressExhaustMachine c t) :
    LeftSafeRun runtimeFixedOuterControllerMachine (outerExhaustCfg c) t := by
  intro i hi hhalt hmove
  have hrun := runtimeFixedOuterController_exhaust_run c i
    (fun j hj => hno j (by omega))
  rw [hrun] at hhalt hmove ⊢
  simp only [outerExhaustCfg] at hhalt hmove ⊢
  have hlocalHalt : runtimeProgressExhaustMachine.halt
      (run runtimeProgressExhaustMachine i c).st = false := by
    change decide ((run runtimeProgressExhaustMachine i c).st = .more ∨
      (run runtimeProgressExhaustMachine i c).st = .final) = false
    simp only [decide_eq_false_iff_not]
    push_neg
    exact hno i hi
  have hlocalMove : (runtimeProgressExhaustMachine.δ
      (run runtimeProgressExhaustMachine i c).st
      ((run runtimeProgressExhaustMachine i c).tp.getD
        (run runtimeProgressExhaustMachine i c).hd false)).2.2 = 0 := by
    simpa [runtimeFixedOuterControllerMachine, (hno i hi).1,
      (hno i hi).2] using hmove
  exact hsafe i hi hlocalHalt hlocalMove

theorem runtimeFixedOuterController_more_handoff_leftSafe
    (p : Nat) (T : List Bool) :
    LeftSafeRun runtimeFixedOuterControllerMachine
      ⟨RuntimeFixedOuterControllerState.exhaust .more, p, T⟩ 1 := by
  apply leftSafeRun_one_of_not_left
  simp [runtimeFixedOuterControllerMachine]

theorem runtimeFixedOuterController_final_handoff_leftSafe
    (p : Nat) (T : List Bool) :
    LeftSafeRun runtimeFixedOuterControllerMachine
      ⟨RuntimeFixedOuterControllerState.exhaust .final, p, T⟩ 1 := by
  apply leftSafeRun_one_of_not_left
  simp [runtimeFixedOuterControllerMachine]

/-! ## Concrete first-halt facts -/

/-- The two-step `more` test cannot reach either routing state early. -/
theorem runtimeProgressExhaust_more_no_early
    (pre tail : List Bool) :
    ∀ i < 2,
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩).st ≠ .final := by
  intro i hi
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead]

/-- The three-step sentinel test cannot reach either routing state early. -/
theorem runtimeProgressExhaust_final_no_early
    (pre tail : List Bool) :
    ∀ i < 3,
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩).st ≠ .more ∧
      (run runtimeProgressExhaustMachine i
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩).st ≠ .final := by
  intro i hi
  interval_cases i <;>
    simp [run_succ, step, runtimeProgressExhaustMachine, moveHead,
      List.getD_eq_getElem?_getD, writeAt]

/-- The concrete `more` test, including its loop-back control transition,
lifts to one exact run of the fixed wrapper. -/
theorem runtimeFixedOuterController_exhaust_more_exact
    (pre tail : List Bool) :
    run runtimeFixedOuterControllerMachine 3
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [true, false, false, false] ++ tail⟩) =
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩ := by
  have hr := runtimeProgressExhaust_more pre tail
  have hh : (run runtimeProgressExhaustMachine 2
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [true, false, false, false] ++ tail⟩).st = .more := by
    rw [hr]
  have h := runtimeFixedOuterController_exhaust_more_run_handoff
    _ 2 (runtimeProgressExhaust_more_no_early pre tail) hh
  rw [hr] at h
  simpa using h

/-- The concrete sentinel test, including the final pure-control transition,
lifts to an exact genuinely halted wrapper run. -/
theorem runtimeFixedOuterController_exhaust_final_exact
    (pre tail : List Bool) :
    run runtimeFixedOuterControllerMachine 4
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [false, true, false, false] ++ tail⟩) =
      ⟨RuntimeFixedOuterControllerState.final, pre.length + 1,
        pre ++ [false, false, false, false] ++ tail⟩ := by
  have hr := runtimeProgressExhaust_final pre tail
  have hh : (run runtimeProgressExhaustMachine 3
      ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
        pre ++ [false, true, false, false] ++ tail⟩).st = .final := by
    rw [hr]
  have h := runtimeFixedOuterController_exhaust_final_run_handoff
    _ 3 (runtimeProgressExhaust_final_no_early pre tail) hh
  rw [hr] at h
  simpa using h

theorem runtimeFixedOuterController_exhaust_more_exact_leftSafe
    (pre tail : List Bool) :
    LeftSafeRun runtimeFixedOuterControllerMachine
      (outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩) 3 := by
  rw [show 3 = 2 + 1 by omega]
  apply leftSafeRun_add
  · apply runtimeFixedOuterController_exhaust_leftSafe
    · exact runtimeProgressExhaust_more_no_early pre tail
    · exact runtimeProgressExhaust_more_leftSafe pre tail
  · rw [show run runtimeFixedOuterControllerMachine 2
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [true, false, false, false] ++ tail⟩) =
        ⟨RuntimeFixedOuterControllerState.exhaust .more, pre.length + 2,
          pre ++ [true, false, false, false] ++ tail⟩ by
      rw [runtimeFixedOuterController_exhaust_run _ 2
        (runtimeProgressExhaust_more_no_early pre tail)]
      rw [runtimeProgressExhaust_more]
      rfl]
    exact runtimeFixedOuterController_more_handoff_leftSafe _ _

theorem runtimeFixedOuterController_exhaust_final_exact_leftSafe
    (pre tail : List Bool) :
    LeftSafeRun runtimeFixedOuterControllerMachine
      (outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
          pre ++ [false, true, false, false] ++ tail⟩) 4 := by
  rw [show 4 = 3 + 1 by omega]
  apply leftSafeRun_add
  · apply runtimeFixedOuterController_exhaust_leftSafe
    · exact runtimeProgressExhaust_final_no_early pre tail
    · exact runtimeProgressExhaust_final_leftSafe pre tail
  · rw [show run runtimeFixedOuterControllerMachine 3
        (outerExhaustCfg
          ⟨runtimeProgressExhaustMachine.start, pre.length + 2,
            pre ++ [false, true, false, false] ++ tail⟩) =
        ⟨RuntimeFixedOuterControllerState.exhaust .final, pre.length + 1,
          pre ++ [false, false, false, false] ++ tail⟩ by
      rw [runtimeFixedOuterController_exhaust_run _ 3
        (runtimeProgressExhaust_final_no_early pre tail)]
      rw [runtimeProgressExhaust_final]
      rfl]
    exact runtimeFixedOuterController_final_handoff_leftSafe _ _

/-! ## Complete uninterrupted controller rounds -/

/-- When another ordinary progress word remains, the single fixed controller
runs the complete forward shift, reverse return, and exhaustion test, then
loops back to its genuine start state at the newly consumed physical hole. -/
theorem runtimeFixedOuterController_round_more
    (pre tail bits : List Bool) :
    let block := passedSourceBlock bits
    let T0 := pre ++ [true, false, true, false, false, false] ++
      flattenPairs block ++ tail
    let T2 := pre ++ [true, false, false, false] ++
      flattenPairs block ++ [false, false] ++ tail
    run runtimeFixedOuterControllerMachine
        ((8 * block.length + 1) +
          ((1 + 2 * block.length + 3 + 1) + 3))
        ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 2, T2⟩ := by
  dsimp only
  let block := passedSourceBlock bits
  let T0 := pre ++ [true, false, true, false, false, false] ++
    flattenPairs block ++ tail
  let T1 := pre ++ [true, false, true, false] ++
    flattenPairs block ++ [false, false] ++ tail
  let T2 := pre ++ [true, false, false, false] ++
    flattenPairs block ++ [false, false] ++ tail
  change run runtimeFixedOuterControllerMachine
      ((8 * block.length + 1) +
        ((1 + 2 * block.length + 3 + 1) + 3))
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
    ⟨runtimeFixedOuterControllerMachine.start, pre.length + 2, T2⟩
  rw [run_add]
  have hsExact := runtimeUniversalPassedShift_passedSourceBlock
    (pre ++ [true, false, true, false]) tail bits
  have hsNoEarly := runtimeUniversalPassedShift_passedSourceBlock_no_early
    (pre ++ [true, false, true, false]) tail bits
  have hsHalt : runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩).st = true := by
    rw [show run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          pre.length + 4 + 2 * block.length, T1⟩ by
      simpa [block, T0, T1, List.append_assoc, Nat.add_assoc] using hsExact]
    simp [runtimeUniversalPassedShiftMachine]
  have hs := runtimeFixedOuterController_shift_run_handoff
    ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩
    (8 * block.length)
    (by simpa [block, T0, List.append_assoc, Nat.add_assoc] using hsNoEarly)
    hsHalt
  rw [show run runtimeFixedOuterControllerMachine (8 * block.length + 1)
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ by
    change run runtimeFixedOuterControllerMachine (8 * block.length + 1)
        (outerShiftCfg
          ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩) = _
    rw [hs]
    rw [show run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          pre.length + 4 + 2 * block.length, T1⟩ by
      simpa [block, T0, T1, List.append_assoc, Nat.add_assoc] using hsExact]]
  rw [run_add]
  have hrExact := runtimeProgressReturn_passed_progress
    (pre ++ [true, false]) tail bits
  have hrNoEarly := runtimeProgressReturn_passed_progress_no_early
    (pre ++ [true, false]) tail bits
  have hrHalt : runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩).st = true := by
    rw [show run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩ by
      simpa [block, T1, T2, List.append_assoc, Nat.add_assoc] using hrExact]
    simp [runtimeProgressReturnMachine]
  have hr := runtimeFixedOuterController_return_run_handoff
    ⟨runtimeProgressReturnMachine.start,
      pre.length + 4 + 2 * block.length, T1⟩
    (1 + 2 * block.length + 3)
    (by simpa [block, T1, List.append_assoc, Nat.add_assoc] using hrNoEarly)
    hrHalt
  rw [show run runtimeFixedOuterControllerMachine
      (1 + 2 * block.length + 3 + 1)
      (outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2, T2⟩ by
    rw [hr]
    rw [show run runtimeProgressReturnMachine
        (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩ by
      simpa [block, T1, T2, List.append_assoc, Nat.add_assoc] using hrExact]]
  have he := runtimeFixedOuterController_exhaust_more_exact pre
    (flattenPairs block ++ [false, false] ++ tail)
  simpa [T2, block, List.append_assoc] using he

/-- With the last ordinary progress word, the same controller completes all
three phases, clears the permanent `01` sentinel, and reaches its sole genuine
halt state. -/
theorem runtimeFixedOuterController_round_final
    (pre tail bits : List Bool) :
    let block := passedSourceBlock bits
    let T0 := pre ++ [false, true, true, false, false, false] ++
      flattenPairs block ++ tail
    let T3 := pre ++ [false, false, false, false] ++
      flattenPairs block ++ [false, false] ++ tail
    run runtimeFixedOuterControllerMachine
        ((8 * block.length + 1) +
          ((1 + 2 * block.length + 3 + 1) + 4))
        ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
      ⟨RuntimeFixedOuterControllerState.final, pre.length + 1, T3⟩ := by
  dsimp only
  let block := passedSourceBlock bits
  let T0 := pre ++ [false, true, true, false, false, false] ++
    flattenPairs block ++ tail
  let T1 := pre ++ [false, true, true, false] ++
    flattenPairs block ++ [false, false] ++ tail
  let T2 := pre ++ [false, true, false, false] ++
    flattenPairs block ++ [false, false] ++ tail
  let T3 := pre ++ [false, false, false, false] ++
    flattenPairs block ++ [false, false] ++ tail
  change run runtimeFixedOuterControllerMachine
      ((8 * block.length + 1) +
        ((1 + 2 * block.length + 3 + 1) + 4))
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
    ⟨RuntimeFixedOuterControllerState.final, pre.length + 1, T3⟩
  rw [run_add]
  have hsExact := runtimeUniversalPassedShift_passedSourceBlock
    (pre ++ [false, true, true, false]) tail bits
  have hsNoEarly := runtimeUniversalPassedShift_passedSourceBlock_no_early
    (pre ++ [false, true, true, false]) tail bits
  have hsHalt : runtimeUniversalPassedShiftMachine.halt
      (run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩).st = true := by
    rw [show run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          pre.length + 4 + 2 * block.length, T1⟩ by
      simpa [block, T0, T1, List.append_assoc, Nat.add_assoc] using hsExact]
    simp [runtimeUniversalPassedShiftMachine]
  have hs := runtimeFixedOuterController_shift_run_handoff
    ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩
    (8 * block.length)
    (by simpa [block, T0, List.append_assoc, Nat.add_assoc] using hsNoEarly)
    hsHalt
  rw [show run runtimeFixedOuterControllerMachine (8 * block.length + 1)
      ⟨runtimeFixedOuterControllerMachine.start, pre.length + 4, T0⟩ =
      outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ by
    change run runtimeFixedOuterControllerMachine (8 * block.length + 1)
        (outerShiftCfg
          ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩) = _
    rw [hs]
    rw [show run runtimeUniversalPassedShiftMachine (8 * block.length)
        ⟨runtimeUniversalPassedShiftMachine.start, pre.length + 4, T0⟩ =
        ⟨RuntimeUniversalPassedShiftState.done,
          pre.length + 4 + 2 * block.length, T1⟩ by
      simpa [block, T0, T1, List.append_assoc, Nat.add_assoc] using hsExact]]
  rw [run_add]
  have hrExact := runtimeProgressReturn_passed_progress
    (pre ++ [false, true]) tail bits
  have hrNoEarly := runtimeProgressReturn_passed_progress_no_early
    (pre ++ [false, true]) tail bits
  have hrHalt : runtimeProgressReturnMachine.halt
      (run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩).st = true := by
    rw [show run runtimeProgressReturnMachine (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩ by
      simpa [block, T1, T2, List.append_assoc, Nat.add_assoc] using hrExact]
    simp [runtimeProgressReturnMachine]
  have hr := runtimeFixedOuterController_return_run_handoff
    ⟨runtimeProgressReturnMachine.start,
      pre.length + 4 + 2 * block.length, T1⟩
    (1 + 2 * block.length + 3)
    (by simpa [block, T1, List.append_assoc, Nat.add_assoc] using hrNoEarly)
    hrHalt
  rw [show run runtimeFixedOuterControllerMachine
      (1 + 2 * block.length + 3 + 1)
      (outerReturnCfg
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩) =
      outerExhaustCfg
        ⟨runtimeProgressExhaustMachine.start, pre.length + 2, T2⟩ by
    rw [hr]
    rw [show run runtimeProgressReturnMachine
        (1 + 2 * block.length + 3)
        ⟨runtimeProgressReturnMachine.start,
          pre.length + 4 + 2 * block.length, T1⟩ =
        ⟨RuntimeProgressReturnState.done, pre.length + 2, T2⟩ by
      simpa [block, T1, T2, List.append_assoc, Nat.add_assoc] using hrExact]]
  have he := runtimeFixedOuterController_exhaust_final_exact pre
    (flattenPairs block ++ [false, false] ++ tail)
  simpa [T2, T3, block, List.append_assoc] using he

/-! ## Structural iteration of the actual fixed controller -/

def runtimeFixedOuterControllerMoreClock (bits : List Bool) : Nat :=
  let block := passedSourceBlock bits
  (8 * block.length + 1) + ((1 + 2 * block.length + 3 + 1) + 3)

def runtimeFixedOuterControllerFinalClock (bits : List Bool) : Nat :=
  let block := passedSourceBlock bits
  (8 * block.length + 1) + ((1 + 2 * block.length + 3 + 1) + 4)

/-- Exact clock for a nonempty physical progress record.  This number occurs
only in the proof statement; the fixed controller discovers every iteration
and the final branch from tape symbols. -/
def runtimeFixedOuterControllerRoundsClock (bits : List Bool) : Nat → Nat
  | 0 => 0
  | 1 => runtimeFixedOuterControllerFinalClock bits
  | k + 2 => runtimeFixedOuterControllerMoreClock bits +
      runtimeFixedOuterControllerRoundsClock bits (k + 1)

/-- Every nonempty `10` progress record drives one uninterrupted run of the
single fixed controller.  The rightmost word is consumed first; induction
therefore follows the physical record from right to left until the permanent
`01` sentinel selects the genuine final state. -/
theorem runtimeFixedOuterController_rounds
    (pre tail bits : List Bool) (k : Nat) :
    let block := passedSourceBlock bits
    let marks := flattenPairs (List.replicate (k + 1) (true, false))
    let T0 := pre ++ [false, true] ++ marks ++ [false, false] ++
      flattenPairs block ++ tail
    let Tf := pre ++ [false, false, false, false] ++
      flattenPairs block ++
      flattenPairs (List.replicate (k + 1) (false, false)) ++ tail
    run runtimeFixedOuterControllerMachine
        (runtimeFixedOuterControllerRoundsClock bits (k + 1))
        ⟨runtimeFixedOuterControllerMachine.start,
          pre.length + 2 + 2 * (k + 1), T0⟩ =
      ⟨RuntimeFixedOuterControllerState.final, pre.length + 1, Tf⟩ := by
  induction k generalizing tail with
  | zero =>
      simpa [runtimeFixedOuterControllerRoundsClock,
        runtimeFixedOuterControllerFinalClock, flattenPairs,
        List.append_assoc, Nat.add_assoc] using
        runtimeFixedOuterController_round_final pre tail bits
  | succ k ih =>
      dsimp only
      let block := passedSourceBlock bits
      let earlier := flattenPairs (List.replicate k (true, false))
      let roundPre := pre ++ [false, true] ++ earlier
      let T0 := roundPre ++ [true, false, true, false, false, false] ++
        flattenPairs block ++ tail
      let T1 := roundPre ++ [true, false, false, false] ++
        flattenPairs block ++ [false, false] ++ tail
      have hmarks :
          flattenPairs (List.replicate (k + 1 + 1) (true, false)) =
            earlier ++ [true, false, true, false] := by
        rw [show k + 1 + 1 = k + 2 by omega,
          List.replicate_add]
        simp [earlier, flattenPairs_append, flattenPairs]
      have hzeros :
          flattenPairs (List.replicate (k + 1 + 1) (false, false)) =
            flattenPairs (List.replicate (k + 1) (false, false)) ++
              [false, false] := by
        rw [show k + 1 + 1 = (k + 1) + 1 by omega,
          List.replicate_add]
        simp [flattenPairs_append, flattenPairs]
      have hremaining :
          flattenPairs (List.replicate (k + 1) (true, false)) =
            earlier ++ [true, false] := by
        rw [show k + 1 = k + 1 by rfl, List.replicate_add]
        simp [earlier, flattenPairs_append, flattenPairs]
      have hhead0 : pre.length + 2 + 2 * (k + 1 + 1) =
          roundPre.length + 4 := by
        simp [roundPre, earlier, flattenPairs_length]
        omega
      have hhead1 : roundPre.length + 2 =
          pre.length + 2 + 2 * (k + 1) := by
        simp [roundPre, earlier, flattenPairs_length]
        omega
      rw [show runtimeFixedOuterControllerRoundsClock bits (k + 1 + 1) =
          runtimeFixedOuterControllerMoreClock bits +
            runtimeFixedOuterControllerRoundsClock bits (k + 1) by
        rw [show k + 1 + 1 = k + 2 by omega]
        rfl]
      rw [run_add]
      have hm := runtimeFixedOuterController_round_more roundPre tail bits
      rw [show run runtimeFixedOuterControllerMachine
          (runtimeFixedOuterControllerMoreClock bits)
          ⟨runtimeFixedOuterControllerMachine.start,
            pre.length + 2 + 2 * (k + 1 + 1),
            pre ++ [false, true] ++
              flattenPairs (List.replicate (k + 1 + 1) (true, false)) ++
              [false, false] ++ flattenPairs block ++ tail⟩ =
          ⟨runtimeFixedOuterControllerMachine.start,
            roundPre.length + 2, T1⟩ by
        rw [hmarks, hhead0]
        simpa [runtimeFixedOuterControllerMoreClock, block, T0, T1,
          roundPre, List.append_assoc] using hm]
      have hih := ih (tail := [false, false] ++ tail)
      rw [hremaining] at hih
      rw [hzeros]
      rw [hhead1]
      simpa [block, earlier, roundPre, T1, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih

@[simp] theorem runtimeFixedOuterController_final_halts :
    runtimeFixedOuterControllerMachine.halt
      RuntimeFixedOuterControllerState.final = true := by
  simp [runtimeFixedOuterControllerMachine]

#print axioms runtimeFixedOuterController_shift_step
#print axioms runtimeFixedOuterController_shift_handoff
#print axioms runtimeFixedOuterController_return_step
#print axioms runtimeFixedOuterController_return_handoff
#print axioms runtimeFixedOuterController_exhaust_step
#print axioms runtimeFixedOuterController_more_handoff
#print axioms runtimeFixedOuterController_final_handoff
#print axioms runtimeFixedOuterController_shift_run_handoff
#print axioms runtimeFixedOuterController_shift_leftSafe
#print axioms runtimeFixedOuterController_shift_handoff_leftSafe
#print axioms runtimeFixedOuterController_return_run_handoff
#print axioms runtimeFixedOuterController_return_leftSafe
#print axioms runtimeFixedOuterController_return_handoff_leftSafe
#print axioms runtimeFixedOuterController_exhaust_more_run_handoff
#print axioms runtimeFixedOuterController_exhaust_final_run_handoff
#print axioms runtimeFixedOuterController_exhaust_leftSafe
#print axioms runtimeFixedOuterController_more_handoff_leftSafe
#print axioms runtimeFixedOuterController_final_handoff_leftSafe
#print axioms runtimeProgressExhaust_more_no_early
#print axioms runtimeProgressExhaust_final_no_early
#print axioms runtimeFixedOuterController_exhaust_more_exact
#print axioms runtimeFixedOuterController_exhaust_final_exact
#print axioms runtimeFixedOuterController_exhaust_more_exact_leftSafe
#print axioms runtimeFixedOuterController_exhaust_final_exact_leftSafe
#print axioms runtimeFixedOuterController_round_more
#print axioms runtimeFixedOuterController_round_final
#print axioms runtimeFixedOuterController_rounds

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeFixedOuterController
