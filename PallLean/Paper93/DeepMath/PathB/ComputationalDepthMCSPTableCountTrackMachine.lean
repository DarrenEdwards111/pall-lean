import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTableExtentGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTableBoundaryProgram

/-!
# MCSP verifier: operational table-length count track

The doubled input codec gives every table bit as `00` or `11` and closes the
table with `01`.  This file exploits that representation directly.

`countTrackProgram` scans one dedicated doubled copy of the table.  It leaves
`11` pairs alone and rewrites each `00` pair to `11`; on the closing `01` it
halts.  Thus, without carrying an unbounded counter in finite control, it
destructively turns

    encodeD table

into

    unaryD table.length.

An adjacent protected `encodeD table ++ witness` suffix is preserved
byte-for-byte.  The resulting unary counter is exactly the input required by
the sound extent gate and its verified destructive comparator.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTableCountTrackMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr

inductive CountState
  | first
  | sawFalse
  | sawTrue
  | writeFirst
  | skipSecond
  | accept
  | reject
  deriving DecidableEq, Fintype

def countProgram : Program where
  Label := CountState
  fin := inferInstance
  dec := inferInstance
  start := .first
  code
    | .first =>
        .act ⟨.sawFalse, none, 1⟩ ⟨.sawTrue, none, 1⟩
    | .sawFalse =>
        .act ⟨.writeFirst, some true, 0⟩ ⟨.accept, none, 1⟩
    | .sawTrue =>
        .act ⟨.reject, none, 1⟩ ⟨.first, none, 1⟩
    | .writeFirst =>
        .act ⟨.skipSecond, some true, 1⟩
          ⟨.skipSecond, some true, 1⟩
    | .skipSecond =>
        .act ⟨.first, none, 1⟩ ⟨.first, none, 1⟩
    | .accept => .halt true
    | .reject => .halt false

def countMachine : Machine :=
  compile countProgram

/-- Exact number of source steps: `11` costs two, `00` costs four, and the
closing marker costs two. -/
def countClock : List Bool → ℕ
  | [] => 2
  | b :: table => (if b then 2 else 4) + countClock table

theorem countClock_le (table : List Bool) :
    countClock table ≤ 4 * table.length + 2 := by
  induction table with
  | nil => rfl
  | cons b table ih =>
      cases b <;> simp [countClock] <;> omega

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

private theorem writeAt_boundary (P R : List Bool) (b : Bool) :
    writeAt (P ++ b :: R) P.length true = P ++ true :: R := by
  rw [writeAt_of_lt true (by simp)]
  simp

theorem step_first_false (P R : List Bool) :
    asmStep countProgram ⟨.first, P.length, P ++ false :: R⟩ =
      ⟨.sawFalse, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .first =
    .act ⟨.sawFalse, none, 1⟩ ⟨.sawTrue, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_first_true (P R : List Bool) :
    asmStep countProgram ⟨.first, P.length, P ++ true :: R⟩ =
      ⟨.sawTrue, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .first =
    .act ⟨.sawFalse, none, 1⟩ ⟨.sawTrue, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_sawTrue_true (P R : List Bool) :
    asmStep countProgram
      ⟨.sawTrue, P.length + 1, P ++ true :: true :: R⟩ =
      ⟨.first, P.length + 2, P ++ true :: true :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .sawTrue =
    .act ⟨.reject, none, 1⟩ ⟨.first, none, 1⟩ from rfl]
  have h :
      (P ++ true :: true :: R).getD (P.length + 1) false = true := by
    rw [show P ++ true :: true :: R =
      (P ++ [true]) ++ true :: R by simp]
    simpa using getD_boundary (P ++ [true]) true R
  rw [h]
  congr 1

theorem step_sawFalse_false (P R : List Bool) :
    asmStep countProgram
      ⟨.sawFalse, P.length + 1, P ++ false :: false :: R⟩ =
      ⟨.writeFirst, P.length, P ++ false :: true :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .sawFalse =
    .act ⟨.writeFirst, some true, 0⟩ ⟨.accept, none, 1⟩ from rfl]
  have h :
      (P ++ false :: false :: R).getD (P.length + 1) false = false := by
    rw [show P ++ false :: false :: R =
      (P ++ [false]) ++ false :: R by simp]
    simpa using getD_boundary (P ++ [false]) false R
  rw [h]
  simp only [Instr.select]
  rw [show moveHead (P.length + 1) 0 = P.length by
    simp [moveHead]]
  rw [show writeAt (P ++ false :: false :: R) (P.length + 1) true =
      P ++ false :: true :: R by
    rw [show P ++ false :: false :: R =
      (P ++ [false]) ++ false :: R by simp]
    simpa using writeAt_boundary (P ++ [false]) R false]

theorem step_writeFirst (P R : List Bool) :
    asmStep countProgram
      ⟨.writeFirst, P.length, P ++ false :: true :: R⟩ =
      ⟨.skipSecond, P.length + 1, P ++ true :: true :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .writeFirst =
    .act ⟨.skipSecond, some true, 1⟩
      ⟨.skipSecond, some true, 1⟩ from rfl]
  cases h : (P ++ false :: true :: R).getD P.length false <;>
    simp only [Instr.select] <;>
    rw [writeAt_boundary P (true :: R) false] <;> rfl

theorem step_skipSecond (P R : List Bool) :
    asmStep countProgram
      ⟨.skipSecond, P.length + 1, P ++ true :: true :: R⟩ =
      ⟨.first, P.length + 2, P ++ true :: true :: R⟩ := by
  unfold asmStep
  rw [show countProgram.code .skipSecond =
    .act ⟨.first, none, 1⟩ ⟨.first, none, 1⟩ from rfl]
  cases h : (P ++ true :: true :: R).getD (P.length + 1) false <;>
    simp only [Instr.select] <;> congr 1 <;> omega

/-- A `11` data pair is already one doubled unary token. -/
theorem convert_true_pair (P R : List Bool) :
    asmRun countProgram 2
      ⟨.first, P.length, P ++ true :: true :: R⟩ =
      ⟨.first, P.length + 2, P ++ true :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep countProgram
    (asmStep countProgram
      ⟨.first, P.length, P ++ true :: true :: R⟩) = _
  rw [step_first_true P (true :: R)]
  rw [step_sawTrue_true]

/-- A `00` data pair is rewritten locally to one `11` unary token. -/
theorem convert_false_pair (P R : List Bool) :
    asmRun countProgram 4
      ⟨.first, P.length, P ++ false :: false :: R⟩ =
      ⟨.first, P.length + 2, P ++ true :: true :: R⟩ := by
  rw [show 4 = 1 + 1 + 1 + 1 by omega, asmRun_add,
    asmRun_add, asmRun_add]
  change asmStep countProgram
    (asmStep countProgram
      (asmStep countProgram
        (asmStep countProgram
          ⟨.first, P.length, P ++ false :: false :: R⟩))) = _
  rw [step_first_false P (false :: R)]
  rw [step_sawFalse_false, step_writeFirst, step_skipSecond]

/-- The `01` marker is preserved and enters the accepting halt state. -/
theorem consume_marker (P R : List Bool) :
    asmRun countProgram 2
      ⟨.first, P.length, P ++ false :: true :: R⟩ =
      ⟨.accept, P.length + 2, P ++ false :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep countProgram
    (asmStep countProgram
      ⟨.first, P.length, P ++ false :: true :: R⟩) = _
  rw [step_first_false P (true :: R)]
  unfold asmStep
  rw [show countProgram.code .sawFalse =
    .act ⟨.writeFirst, some true, 0⟩ ⟨.accept, none, 1⟩ from rfl]
  have hmarker :
      (P ++ false :: true :: R).getD (P.length + 1) false = true := by
    rw [show P ++ false :: true :: R =
      (P ++ [false]) ++ true :: R by simp]
    simpa using getD_boundary (P ++ [false]) true R
  rw [hmarker]
  congr 1

/-- The complete destructive conversion behind an already-converted prefix. -/
theorem asmRun_countTrack_from (P table suffix : List Bool) :
    asmRun countProgram (countClock table)
      ⟨.first, P.length, P ++ encodeD table ++ suffix⟩ =
      ⟨.accept, P.length + 2 * table.length + 2,
        P ++ unaryD table.length ++ suffix⟩ := by
  induction table generalizing P with
  | nil =>
      simpa [countClock, unaryD, List.append_assoc] using
        consume_marker P suffix
  | cons b table ih =>
      cases b with
      | false =>
          rw [show countClock (false :: table) =
            4 + countClock table by rfl, asmRun_add]
          change asmRun countProgram (countClock table)
            (asmRun countProgram 4
              ⟨.first, P.length,
                P ++ false :: false :: encodeD table ++ suffix⟩) = _
          rw [show P ++ false :: false :: encodeD table ++ suffix =
            P ++ false :: false :: (encodeD table ++ suffix) by
              simp [List.append_assoc]]
          rw [convert_false_pair P (encodeD table ++ suffix)]
          have h := ih (P ++ [true, true])
          simpa [unaryD, List.append_assoc, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h
      | true =>
          rw [show countClock (true :: table) =
            2 + countClock table by rfl, asmRun_add]
          change asmRun countProgram (countClock table)
            (asmRun countProgram 2
              ⟨.first, P.length,
                P ++ true :: true :: encodeD table ++ suffix⟩) = _
          rw [show P ++ true :: true :: encodeD table ++ suffix =
            P ++ true :: true :: (encodeD table ++ suffix) by
              simp [List.append_assoc]]
          rw [convert_true_pair P (encodeD table ++ suffix)]
          have h := ih (P ++ [true, true])
          simpa [unaryD, List.append_assoc, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h

/-- The complete destructive conversion from forced initialization, preserving
the protected suffix byte-for-byte. -/
theorem asmRun_countTrack (table suffix : List Bool) :
    asmRun countProgram (countClock table)
      (asmInit countProgram (encodeD table ++ suffix)) =
      ⟨.accept, 2 * table.length + 2,
        unaryD table.length ++ suffix⟩ := by
  simpa using asmRun_countTrack_from [] table suffix

/-- Exact compiled-machine run on a destructive count track followed by a
protected table/witness copy. -/
theorem machine_run_countTrack (table witness : List Bool) :
    run countMachine (countClock table)
      (init countMachine
        (encodeD table ++ (encodeD table ++ witness))) =
      ⟨.accept, 2 * table.length + 2,
        unaryD table.length ++ (encodeD table ++ witness)⟩ := by
  unfold countMachine
  rw [compile_run_init, asmRun_countTrack]
  rfl

theorem machine_halts_countTrack (table witness : List Bool) :
    HaltsBy countMachine
      (encodeD table ++ (encodeD table ++ witness))
      (countClock table) := by
  unfold HaltsBy
  rw [machine_run_countTrack]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPTableCountTrackMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountTrackMachine.machine_run_countTrack
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountTrackMachine.machine_halts_countTrack
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountTrackMachine.countClock_le
