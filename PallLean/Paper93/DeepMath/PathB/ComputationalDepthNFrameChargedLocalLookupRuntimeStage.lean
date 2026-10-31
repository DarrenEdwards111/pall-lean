import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupNextStage

/-!
# Charged local lookup: runtime-indexed staging

`scheduledNextStageMachine x w t` removed the physical rewrite gap but baked
the round number into the machine.  The repeat controller already records that
number on tape as `cntT B j`.  This file makes the selection operational:
`runtimeStageCore B schedule` counts the leading marked `10` pairs, retains
their number in finite control, crosses the remaining `11` pairs and `01`
boundary, then writes `schedule[j]` over the work suffix.

Thus one machine works for every `j ≤ B`.  At `j = B`, the default empty
schedule entry makes the same core halt without writing, so the terminal
round needs no special external branch.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinInP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge

/-- Runtime-selected block, empty beyond the supplied schedule. -/
def scheduleAt (schedule : List (List Bool)) (j : Nat) : List Bool :=
  schedule.getD j []

/-- Writer state whose position bound depends on the runtime-selected block. -/
abbrev RuntimeWriterState (B : Nat) (schedule : List (List Bool)) :=
  (j : Fin (B + 1)) × Fin ((scheduleAt schedule j.val).length + 1)

/-- Scan states use phases `0/1` to count leading `10` pairs and `2/3` to
cross the remaining `11` pairs.  Encountering the `01` boundary enters the
dependent writer state. -/
abbrev RuntimeStageState (B : Nat) (schedule : List (List Bool)) :=
  (Fin 4 × Fin (B + 1) × Bool) ⊕ RuntimeWriterState B schedule

/-- One fixed runtime-indexed staging core for the whole schedule. -/
def runtimeStageCore (B : Nat) (schedule : List (List Bool)) : Machine where
  State := RuntimeStageState B schedule
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl (0, ⟨0, by omega⟩, false)
  halt := fun s => match s with
    | .inl _ => false
    | .inr ⟨j, k⟩ => decide (k.val = (scheduleAt schedule j.val).length)
  δ := fun s b => match s with
    | .inl (ph, j, carry) =>
        if ph = 0 then (Sum.inl (1, j, b), none, 1)
        else if ph = 1 then
          if carry then
            if b then (Sum.inl (2, j, carry), none, 1)
            else
              if hj : j.val < B then
                (Sum.inl (0, ⟨j.val + 1, by omega⟩, carry), none, 1)
              else (Sum.inl (0, j, carry), none, 1)
          else
            (Sum.inr ⟨j, ⟨0, by omega⟩⟩, none, 1)
        else if ph = 2 then (Sum.inl (3, j, b), none, 1)
        else if carry then (Sum.inl (2, j, carry), none, 1)
        else (Sum.inr ⟨j, ⟨0, by omega⟩⟩, none, 1)
    | .inr ⟨j, k⟩ =>
        if hk : k.val < (scheduleAt schedule j.val).length then
          (Sum.inr ⟨j, ⟨k.val + 1, by omega⟩⟩,
            some ((scheduleAt schedule j.val).getD k.val false), 1)
        else (Sum.inr ⟨j, k⟩, none, 2)
  accept := fun _ => false

def scanState (B : Nat) (schedule : List (List Bool))
    (ph : Fin 4) (j : Nat) (hj : j ≤ B) (carry : Bool) :
    (runtimeStageCore B schedule).State :=
  Sum.inl (ph, ⟨j, by omega⟩, carry)

def writerStart (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) : (runtimeStageCore B schedule).State :=
  Sum.inr ⟨⟨j, by omega⟩, ⟨0, by omega⟩⟩

def writerState (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (k : Nat)
    (hk : k ≤ (scheduleAt schedule j).length) :
    (runtimeStageCore B schedule).State :=
  Sum.inr ⟨⟨j, by omega⟩, ⟨k, by simpa using Nat.lt_succ_iff.mpr hk⟩⟩

/-! ## Pair-step laws -/

theorem runtime_mark_pair (B : Nat) (schedule : List (List Bool))
    (T : List Bool) (p j : Nat) (hj : j < B) (s : Bool)
    (hlo : T.getD p false = true) (hhi : T.getD (p + 1) false = false) :
    run (runtimeStageCore B schedule) 2
      ⟨scanState B schedule 0 j (by omega) s, p, T⟩ =
      ⟨scanState B schedule 0 (j + 1) (by omega) true, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeStageCore, scanState, moveHead, hlo, hhi, hj]

theorem runtime_first_data_pair (B : Nat) (schedule : List (List Bool))
    (T : List Bool) (p j : Nat) (hj : j ≤ B) (s : Bool)
    (hlo : T.getD p false = true) (hhi : T.getD (p + 1) false = true) :
    run (runtimeStageCore B schedule) 2
      ⟨scanState B schedule 0 j hj s, p, T⟩ =
      ⟨scanState B schedule 2 j hj true, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeStageCore, scanState, moveHead, hlo, hhi]

theorem runtime_skip_data_pair (B : Nat) (schedule : List (List Bool))
    (T : List Bool) (p j : Nat) (hj : j ≤ B)
    (hlo : T.getD p false = true) :
    run (runtimeStageCore B schedule) 2
      ⟨scanState B schedule 2 j hj true, p, T⟩ =
      ⟨scanState B schedule 2 j hj true, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeStageCore, scanState, moveHead, hlo]

theorem runtime_boundary_from_find (B : Nat) (schedule : List (List Bool))
    (T : List Bool) (p j : Nat) (hj : j ≤ B) (s : Bool)
    (hlo : T.getD p false = false) :
    run (runtimeStageCore B schedule) 2
      ⟨scanState B schedule 0 j hj s, p, T⟩ =
      ⟨writerStart B schedule j hj, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeStageCore, scanState, writerStart, moveHead, hlo]

theorem runtime_boundary_from_skip (B : Nat) (schedule : List (List Bool))
    (T : List Bool) (p j : Nat) (hj : j ≤ B)
    (hlo : T.getD p false = false) :
    run (runtimeStageCore B schedule) 2
      ⟨scanState B schedule 2 j hj true, p, T⟩ =
      ⟨writerStart B schedule j hj, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo
  rw [run_succ, run_succ, run_zero]
  simp [step, runtimeStageCore, scanState, writerStart, moveHead, hlo]

/-! ## Exact countdown selection -/

theorem runtime_marked_prefix (B : Nat) (schedule : List (List Bool))
    (j i : Nat) (hj : j ≤ B) (hi : i ≤ j) (old : List Bool) :
    run (runtimeStageCore B schedule) (2 * i)
      (init (runtimeStageCore B schedule) (cntT B j ++ old)) =
      ⟨scanState B schedule 0 i (by omega) (if i = 0 then false else true),
        2 * i, cntT B j ++ old⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, run_add,
        ih (by omega)]
      exact runtime_mark_pair B schedule (cntT B j ++ old) (2 * i) i
        (by omega) (if i = 0 then false else true)
        (cntE_mark_lo B j old i (by omega))
        (by simpa [Nat.add_assoc] using cntE_mark_hi B j old i (by omega))

theorem runtime_skip_data_pairs (B : Nat) (schedule : List (List Bool))
    (j k : Nat) (hj : j < B) (hk : k ≤ B - j - 1) (old : List Bool) :
    run (runtimeStageCore B schedule) (2 * k)
      ⟨scanState B schedule 2 j (by omega) true, 2 * (j + 1),
        cntT B j ++ old⟩ =
      ⟨scanState B schedule 2 j (by omega) true, 2 * (j + 1 + k),
        cntT B j ++ old⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, run_add,
        ih (by omega)]
      apply runtime_skip_data_pair B schedule (cntT B j ++ old)
      exact cntE_data B j old (2 * (j + 1 + k)) (by omega) (by omega) (by omega)

/-- After exactly the fixed countdown width, the runtime index `j` is retained
in the dependent writer state at the work-suffix origin. -/
theorem runtime_select_countdown (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (old : List Bool) :
    run (runtimeStageCore B schedule) (2 * B + 2)
      (init (runtimeStageCore B schedule) (cntT B j ++ old)) =
      ⟨writerStart B schedule j hj, 2 * B + 2, cntT B j ++ old⟩ := by
  by_cases hjB : j = B
  · subst j
    rw [show 2 * B + 2 = 2 * B + 2 by rfl, run_add,
      runtime_marked_prefix B schedule B B (by omega) (by omega) old]
    exact runtime_boundary_from_find B schedule (cntT B B ++ old) (2 * B)
      B (by omega) (if B = 0 then false else true)
      (cntE_cm_lo B B old (by omega))
  · have hjlt : j < B := by omega
    have hmark := runtime_marked_prefix B schedule j j (by omega) (by omega) old
    have hdata := runtime_first_data_pair B schedule (cntT B j ++ old)
      (2 * j) j (by omega) (if j = 0 then false else true)
      (cntE_data B j old (2 * j) (by omega) (by omega) (by omega))
      (cntE_data B j old (2 * j + 1) (by omega) (by omega) (by omega))
    have hskip := runtime_skip_data_pairs B schedule j (B - j - 1)
      hjlt (by omega) old
    have hskip' :
        run (runtimeStageCore B schedule) (2 * (B - j - 1))
          ⟨scanState B schedule 2 j (by omega) true, 2 * j + 2,
            cntT B j ++ old⟩ =
          ⟨scanState B schedule 2 j (by omega) true,
            2 * B, cntT B j ++ old⟩ := by
      simpa [show 2 * (j + 1) = 2 * j + 2 by ring,
        show j + 1 + (B - j - 1) = B by omega] using hskip
    have hbound := runtime_boundary_from_skip B schedule (cntT B j ++ old)
      (2 * B) j (by omega) (cntE_cm_lo B j old (by omega))
    rw [show 2 * B + 2 = 2 * j + (2 + (2 * (B - j - 1) + 2)) by omega,
      run_add, hmark, run_add, hdata, run_add, hskip']
    have hclock : 2 * j + (2 + (2 * (B - j - 1) + 2)) = 2 * B + 2 := by
      omega
    simpa [hclock] using hbound

/-! ## Runtime-selected block write -/

theorem runtime_write_selected (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (T : List Bool) (p k : Nat)
    (hk : k ≤ (scheduleAt schedule j).length) :
    run (runtimeStageCore B schedule) k
      ⟨writerStart B schedule j hj, p, T⟩ =
      ⟨writerState B schedule j hj k hk, p + k,
        stagedTape p (scheduleAt schedule j) k T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < (scheduleAt schedule j).length := by omega
      have hkne : k ≠ (scheduleAt schedule j).length := by omega
      rw [run_succ, ih (by omega)]
      simp [step, runtimeStageCore, writerState, stagedTape,
        moveHead, hklt, hkne, Nat.add_assoc]

/-- Complete runtime-indexed stage: select from the tape counter, overwrite
the chosen block, and halt. -/
theorem runtimeStageCore_run (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (old : List Bool) :
    run (runtimeStageCore B schedule)
      (2 * B + 2 + (scheduleAt schedule j).length)
      (init (runtimeStageCore B schedule) (cntT B j ++ old)) =
      ⟨writerState B schedule j hj (scheduleAt schedule j).length (by omega),
        2 * B + 2 + (scheduleAt schedule j).length,
        stagedTape (2 * B + 2) (scheduleAt schedule j)
          (scheduleAt schedule j).length (cntT B j ++ old)⟩ := by
  rw [run_add, runtime_select_countdown B schedule j hj old]
  exact runtime_write_selected B schedule j hj (cntT B j ++ old)
    (2 * B + 2) (scheduleAt schedule j).length (by omega)

theorem runtimeStageCore_halted (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (old : List Bool) :
    (runtimeStageCore B schedule).halt
      (run (runtimeStageCore B schedule)
        (2 * B + 2 + (scheduleAt schedule j).length)
        (init (runtimeStageCore B schedule) (cntT B j ++ old))).st = true := by
  rw [runtimeStageCore_run B schedule j hj old]
  simp [runtimeStageCore, writerState, scheduleAt]

/-! ## Lift behind the fixed output-capacity region -/

theorem runtimeStageCore_move_ne_reset (B : Nat)
    (schedule : List (List Bool))
    (s : (runtimeStageCore B schedule).State) (b : Bool) :
    (runtimeStageCore B schedule).δ s b |>.2.2 ≠ 3 := by
  rcases s with (s | s)
  · rcases s with ⟨⟨ph, hph⟩, ⟨j, hj⟩, carry⟩
    simp only [runtimeStageCore]
    split_ifs <;> simp
  · rcases s with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
    simp only [runtimeStageCore]
    split_ifs <;> simp

theorem runtimeStageCore_move_ne_left (B : Nat)
    (schedule : List (List Bool))
    (s : (runtimeStageCore B schedule).State) (b : Bool) :
    (runtimeStageCore B schedule).δ s b |>.2.2 ≠ 0 := by
  rcases s with (s | s)
  · rcases s with ⟨⟨ph, hph⟩, ⟨j, hj⟩, carry⟩
    simp only [runtimeStageCore]
    split_ifs <;> simp
  · rcases s with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
    simp only [runtimeStageCore]
    split_ifs <;> simp

theorem runtimeStageCore_prefixSafe (B : Nat)
    (schedule : List (List Bool)) (c : Cfg (runtimeStageCore B schedule))
    (n : Nat) : PrefixSafeRun (runtimeStageCore B schedule) c n := by
  intro i hi
  constructor
  · intro _
    exact runtimeStageCore_move_ne_reset B schedule _ _
  · intro _ hleft
    exact False.elim (runtimeStageCore_move_ne_left B schedule _ _ hleft)

/-- The runtime-selected stage lifted behind the fixed-capacity truth output.
This machine depends on the capacity and schedule, but not on the live round
index. -/
def runtimeStageMachine (B : Nat) (schedule : List (List Bool)) : Machine :=
  fixedPrefixAdapter (2 * B + 2) (runtimeStageCore B schedule)

def runtimeStageClock (B : Nat) (schedule : List (List Bool)) (j : Nat) : Nat :=
  (2 * B + 2) + 1 +
    (2 * B + 2 + (scheduleAt schedule j).length)

/-- On the physical verifier layout, the entire output-capacity prefix is
preserved byte-for-byte while the countdown selects and stages its payload. -/
theorem runtimeStageMachine_run (B : Nat) (schedule : List (List Bool))
    (j : Nat) (hj : j ≤ B) (out old : List Bool) (hout : out.length ≤ B) :
    run (runtimeStageMachine B schedule) (runtimeStageClock B schedule j)
        (init (runtimeStageMachine B schedule)
          (outputCap B out ++ (cntT B j ++ old))) =
      embedFixedBody (2 * B + 2) (runtimeStageCore B schedule)
        (outputCap B out)
        ⟨writerState B schedule j hj (scheduleAt schedule j).length (by omega),
          2 * B + 2 + (scheduleAt schedule j).length,
          stagedTape (2 * B + 2) (scheduleAt schedule j)
            (scheduleAt schedule j).length (cntT B j ++ old)⟩ := by
  unfold runtimeStageMachine runtimeStageClock
  calc
    run (fixedPrefixAdapter (2 * B + 2) (runtimeStageCore B schedule))
        ((2 * B + 2) + 1 +
          (2 * B + 2 + (scheduleAt schedule j).length))
        (init (fixedPrefixAdapter (2 * B + 2) (runtimeStageCore B schedule))
          (outputCap B out ++ (cntT B j ++ old))) =
      embedFixedBody (2 * B + 2) (runtimeStageCore B schedule)
        (outputCap B out)
        (run (runtimeStageCore B schedule)
          (2 * B + 2 + (scheduleAt schedule j).length)
          (init (runtimeStageCore B schedule) (cntT B j ++ old))) := by
            exact fixedPrefix_run (2 * B + 2) (runtimeStageCore B schedule)
              (outputCap B out) (cntT B j ++ old)
              (2 * B + 2 + (scheduleAt schedule j).length)
              (outputCap_length B out hout)
              (runtimeStageCore_prefixSafe B schedule _ _)
    _ = _ := by rw [runtimeStageCore_run B schedule j hj old]

/-! ## Canonical schedule specialization -/

/-- All canonical lookup payloads, in runtime schedule order. -/
def literalTapeSchedule (x w : List Bool) : List (List Bool) :=
  (List.range (decodedLiterals x).length).map
    (fun t => literalLookupTape w (scheduledLiteral x t))

theorem literalTapeSchedule_getD (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    scheduleAt (literalTapeSchedule x w) t =
      literalLookupTape w (scheduledLiteral x t) := by
  rw [scheduleAt, literalTapeSchedule, List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_map, List.getElem_range]

/-- One machine, independent of `t`, stages the payload selected by the live
countdown. -/
theorem runtimeStageCore_scheduled (x w old : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    run (runtimeStageCore B schedule)
        (2 * B + 2 + (literalLookupTape w (scheduledLiteral x t)).length)
        (init (runtimeStageCore B schedule) (cntT B t ++ old)) =
      ⟨writerState B schedule t (by omega)
          (literalLookupTape w (scheduledLiteral x t)).length (by
            rw [literalTapeSchedule_getD x w ht]),
        2 * B + 2 + (literalLookupTape w (scheduledLiteral x t)).length,
        stagedTape (2 * B + 2) (literalLookupTape w (scheduledLiteral x t))
          (literalLookupTape w (scheduledLiteral x t)).length
          (cntT B t ++ old)⟩ := by
  dsimp only
  have h := runtimeStageCore_run (decodedLiterals x).length
    (literalTapeSchedule x w) t (by omega) old
  simpa only [literalTapeSchedule_getD x w ht] using h

/-- The same runtime-selected body behind the real fixed output region.  The
machine is unchanged as `t` varies; only the tape countdown varies. -/
theorem runtimeStageMachine_scheduled (x w out old : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (hout : out.length ≤ (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    run (runtimeStageMachine B schedule) (runtimeStageClock B schedule t)
        (init (runtimeStageMachine B schedule)
          (outputCap B out ++ (cntT B t ++ old))) =
      embedFixedBody (2 * B + 2) (runtimeStageCore B schedule)
        (outputCap B out)
        ⟨writerState B schedule t (by omega)
            (literalLookupTape w (scheduledLiteral x t)).length (by
              rw [literalTapeSchedule_getD x w ht]),
          2 * B + 2 + (literalLookupTape w (scheduledLiteral x t)).length,
          stagedTape (2 * B + 2)
            (literalLookupTape w (scheduledLiteral x t))
            (literalLookupTape w (scheduledLiteral x t)).length
            (cntT B t ++ old)⟩ := by
  dsimp only
  have h := runtimeStageMachine_run (decodedLiterals x).length
    (literalTapeSchedule x w) t (by omega) out old hout
  simpa only [literalTapeSchedule_getD x w ht] using h

/-- The fixed-prefix scan, runtime countdown selection, and selected payload
write fit in a small quadratic envelope. -/
theorem runtimeStageClock_scheduled_le (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    runtimeStageClock (decodedLiterals x).length (literalTapeSchedule x w) t
      ≤ 12 * (x.length + 1) ^ 2 := by
  have hcount := decodedLiterals_length_le x
  have hx : 1 ≤ x.length := by
    nlinarith
  have hlmem := scheduledLiteral_mem x ht
  have hlvar := decodedLiterals_var_le x hlmem
  have hlit :
      (literalLookupTape w (scheduledLiteral x t)).length =
        4 * (scheduledLiteral x t).1 + 8 := by
    simp [literalLookupTape, encode, signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  rw [runtimeStageClock, literalTapeSchedule_getD x w ht, hlit]
  nlinarith [Nat.zero_le x.length]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtime_select_countdown
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageCore_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageCore_halted
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageCore_scheduled
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageMachine_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageMachine_scheduled
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage.runtimeStageClock_scheduled_le
