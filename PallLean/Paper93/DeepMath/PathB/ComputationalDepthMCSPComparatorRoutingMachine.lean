import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorReadyLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFiniteControlCompiler

/-!
# MCSP verifier: finite-control routing across the comparator layout

The comparator-ready tape is not obtained by swapping two variable-length
blocks in place.  Instead, the two scratch tracks are prepared in the order
in which they are consumed:

    reverse track = tableLength, 2^n
    forward track = 2^n, tableLength.

Their concatenation is exactly

    tableLength, 2^n, 2^n, tableLength, payload.

This file supplies the operational head-routing pass over that layout.  A
fixed finite-control program checks the doubled alphabet of all four unary
counters, rejects malformed `10` and `00` pairs, preserves the complete tape,
and halts with its head exactly at the first payload cell.  Thus later phases
have a proved handoff position rather than a list-level assumed offset.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout

inductive RouteState
  | scan (track : Fin 4)
  | sawFalse (track : Fin 4)
  | sawTrue (track : Fin 4)
  | accept
  | reject
  deriving DecidableEq, Fintype

/-- After a counter marker, enter the next track or accept after track four. -/
def afterTrack (i : Fin 4) : RouteState :=
  if h : i.val + 1 < 4 then .scan ⟨i.val + 1, h⟩ else .accept

/-- Scan four doubled unary counters without modifying the tape. -/
def routeProgram : Program where
  Label := RouteState
  fin := inferInstance
  dec := inferInstance
  start := .scan 0
  code
    | .scan i =>
        .act ⟨.sawFalse i, none, 1⟩ ⟨.sawTrue i, none, 1⟩
    | .sawFalse i =>
        .act ⟨.reject, none, 1⟩ ⟨afterTrack i, none, 1⟩
    | .sawTrue i =>
        .act ⟨.reject, none, 1⟩ ⟨.scan i, none, 1⟩
    | .accept => .halt true
    | .reject => .halt false

def routeMachine : Machine :=
  compile routeProgram

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem step_scan_true (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.scan i, P.length, P ++ true :: R⟩ =
      ⟨.sawTrue i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.scan i) =
    .act ⟨.sawFalse i, none, 1⟩
      ⟨.sawTrue i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_sawTrue_true (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.sawTrue i, P.length, P ++ true :: R⟩ =
      ⟨.scan i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.sawTrue i) =
    .act ⟨.reject, none, 1⟩ ⟨.scan i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_scan_false (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.scan i, P.length, P ++ false :: R⟩ =
      ⟨.sawFalse i, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.scan i) =
    .act ⟨.sawFalse i, none, 1⟩
      ⟨.sawTrue i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_sawFalse_true (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.sawFalse i, P.length, P ++ true :: R⟩ =
      ⟨afterTrack i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.sawFalse i) =
    .act ⟨.reject, none, 1⟩ ⟨afterTrack i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_sawTrue_false (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.sawTrue i, P.length, P ++ false :: R⟩ =
      ⟨.reject, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.sawTrue i) =
    .act ⟨.reject, none, 1⟩ ⟨.scan i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

theorem step_sawFalse_false (i : Fin 4) (P R : List Bool) :
    asmStep routeProgram
      ⟨.sawFalse i, P.length, P ++ false :: R⟩ =
      ⟨.reject, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show routeProgram.code (.sawFalse i) =
    .act ⟨.reject, none, 1⟩ ⟨afterTrack i, none, 1⟩ from rfl]
  rw [getD_boundary]
  rfl

/-- One legal doubled data pair advances by two cells. -/
theorem run_data_pair (i : Fin 4) (P R : List Bool) :
    asmRun routeProgram 2
      ⟨.scan i, P.length, P ++ true :: true :: R⟩ =
      ⟨.scan i, P.length + 2, P ++ true :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep routeProgram
    (asmStep routeProgram
      ⟨.scan i, P.length, P ++ true :: true :: R⟩) = _
  rw [step_scan_true i P (true :: R)]
  rw [show P ++ true :: true :: R =
    (P ++ [true]) ++ true :: R by simp]
  simpa using step_sawTrue_true i (P ++ [true]) R

/-- The legal `01` marker advances to the next routed track. -/
theorem run_marker (i : Fin 4) (P R : List Bool) :
    asmRun routeProgram 2
      ⟨.scan i, P.length, P ++ false :: true :: R⟩ =
      ⟨afterTrack i, P.length + 2, P ++ false :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep routeProgram
    (asmStep routeProgram
      ⟨.scan i, P.length, P ++ false :: true :: R⟩) = _
  rw [step_scan_false i P (true :: R)]
  rw [show P ++ false :: true :: R =
    (P ++ [false]) ++ true :: R by simp]
  simpa using step_sawFalse_true i (P ++ [false]) R

/-- The malformed doubled symbol `10` enters the rejecting halt state. -/
theorem run_reject_ten (i : Fin 4) (P R : List Bool) :
    asmRun routeProgram 2
      ⟨.scan i, P.length, P ++ true :: false :: R⟩ =
      ⟨.reject, P.length + 2, P ++ true :: false :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep routeProgram
    (asmStep routeProgram
      ⟨.scan i, P.length, P ++ true :: false :: R⟩) = _
  rw [step_scan_true i P (false :: R)]
  rw [show P ++ true :: false :: R =
    (P ++ [true]) ++ false :: R by simp]
  simpa using step_sawTrue_false i (P ++ [true]) R

/-- The malformed doubled symbol `00` enters the rejecting halt state. -/
theorem run_reject_zerozero (i : Fin 4) (P R : List Bool) :
    asmRun routeProgram 2
      ⟨.scan i, P.length, P ++ false :: false :: R⟩ =
      ⟨.reject, P.length + 2, P ++ false :: false :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep routeProgram
    (asmStep routeProgram
      ⟨.scan i, P.length, P ++ false :: false :: R⟩) = _
  rw [step_scan_false i P (false :: R)]
  rw [show P ++ false :: false :: R =
    (P ++ [false]) ++ false :: R by simp]
  simpa using step_sawFalse_false i (P ++ [false]) R

/-- Exact scan of one standard unary counter behind an arbitrary prefix. -/
theorem asmRun_counter (i : Fin 4) (P R : List Bool) (k : ℕ) :
    asmRun routeProgram (2 * k + 2)
      ⟨.scan i, P.length, P ++ unaryD k ++ R⟩ =
      ⟨afterTrack i, P.length + 2 * k + 2,
        P ++ unaryD k ++ R⟩ := by
  rw [unaryD_eq]
  induction k generalizing P with
  | zero =>
      simpa using run_marker i P R
  | succ k ih =>
      rw [show 2 * (k + 1) + 2 = 2 + (2 * k + 2) by omega,
        asmRun_add, show 2 * (k + 1) = 2 + 2 * k by omega,
        List.replicate_add]
      change asmRun routeProgram (2 * k + 2)
        (asmRun routeProgram 2
          ⟨.scan i, P.length,
            P ++ true :: true ::
              (List.replicate (2 * k) true ++ [false, true]) ++ R⟩) = _
      rw [show P ++ true :: true ::
            (List.replicate (2 * k) true ++ [false, true]) ++ R =
          P ++ true :: true ::
            ((List.replicate (2 * k) true ++ [false, true]) ++ R) by
              simp [List.append_assoc]]
      rw [run_data_pair i P
        ((List.replicate (2 * k) true ++ [false, true]) ++ R)]
      have h := ih (P ++ [true, true])
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

@[simp] theorem afterTrack_zero :
    afterTrack (0 : Fin 4) = .scan 1 := rfl

@[simp] theorem afterTrack_one :
    afterTrack (1 : Fin 4) = .scan 2 := rfl

@[simp] theorem afterTrack_two :
    afterTrack (2 : Fin 4) = .scan 3 := rfl

@[simp] theorem afterTrack_three :
    afterTrack (3 : Fin 4) = .accept := rfl

/-- The exact routing time through all four counter blocks. -/
def routeClock (n tableLength : ℕ) : ℕ :=
  4 * tableLength + 4 * (2 ^ n) + 8

/-- The two already-oriented scratch tracks concatenate to the comparator
layout; no variable-length in-place block swap is required. -/
theorem reverse_forward_tracks_eq_layout (n : ℕ)
    (table payload : List Bool) :
    reverseTape n table ++ forwardTape n table ++ payload =
      comparatorLayout n table payload := by
  simp [reverseTape, forwardTape, comparatorLayout, List.append_assoc]

/-- The finite-control router traverses the four counters, preserves the
payload and every counter cell, and stops exactly at the payload boundary. -/
theorem asmRun_comparatorLayout (n : ℕ) (table payload : List Bool) :
    asmRun routeProgram (routeClock n table.length)
      (asmInit routeProgram (comparatorLayout n table payload)) =
      ⟨.accept, routeClock n table.length,
        comparatorLayout n table payload⟩ := by
  unfold asmInit routeClock comparatorLayout
  rw [show 4 * table.length + 4 * 2 ^ n + 8 =
      (2 * table.length + 2) +
        ((2 * 2 ^ n + 2) +
          ((2 * 2 ^ n + 2) + (2 * table.length + 2))) by ring,
    asmRun_add]
  change asmRun routeProgram
      ((2 * 2 ^ n + 2) + ((2 * 2 ^ n + 2) + (2 * table.length + 2)))
      (asmRun routeProgram (2 * table.length + 2)
        ⟨.scan (0 : Fin 4), 0,
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩) = _
  have h0 := asmRun_counter (0 : Fin 4) []
    (unaryD (2 ^ n) ++
      (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))
    table.length
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at h0
  rw [h0]
  simp only [afterTrack_zero]
  rw [asmRun_add]
  have h1 :
      asmRun routeProgram (2 * 2 ^ n + 2)
        ⟨.scan (1 : Fin 4), 2 * table.length + 2,
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ =
        ⟨.scan (2 : Fin 4),
          2 * table.length + 2 + (2 * 2 ^ n + 2),
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ := by
    simpa [List.append_assoc, unaryD_length] using
      (asmRun_counter (1 : Fin 4) (unaryD table.length)
        (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)) (2 ^ n))
  rw [h1]
  rw [asmRun_add]
  have h2 :
      asmRun routeProgram (2 * 2 ^ n + 2)
        ⟨.scan (2 : Fin 4),
          2 * table.length + 2 + (2 * 2 ^ n + 2),
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ =
        ⟨.scan (3 : Fin 4),
          2 * table.length + 2 + (2 * 2 ^ n + 2) +
            (2 * 2 ^ n + 2),
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ := by
    simpa [List.append_assoc, unaryD_length] using
      (asmRun_counter (2 : Fin 4)
        (unaryD table.length ++ unaryD (2 ^ n))
        (unaryD table.length ++ payload) (2 ^ n))
  rw [h2]
  have h3 :
      asmRun routeProgram (2 * table.length + 2)
        ⟨.scan (3 : Fin 4),
          2 * table.length + 2 + (2 * 2 ^ n + 2) +
            (2 * 2 ^ n + 2),
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ =
        ⟨.accept,
          2 * table.length + 2 + (2 * 2 ^ n + 2) +
            (2 * 2 ^ n + 2) + (2 * table.length + 2),
          unaryD table.length ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD table.length ++ payload)))⟩ := by
    have h := asmRun_counter (3 : Fin 4)
        (unaryD table.length ++ unaryD (2 ^ n) ++ unaryD (2 ^ n))
        payload table.length
    simpa [List.append_assoc, unaryD_length, Nat.add_assoc] using h
  rw [h3]
  congr 1 <;> ring

/-- Exact compiled-machine execution of the routing sequencer. -/
theorem machine_run_comparatorLayout (n : ℕ)
    (table payload : List Bool) :
    run routeMachine (routeClock n table.length)
      (init routeMachine (comparatorLayout n table payload)) =
      ⟨.accept, routeClock n table.length,
        comparatorLayout n table payload⟩ := by
  unfold routeMachine
  rw [compile_run_init, asmRun_comparatorLayout]
  rfl

theorem machine_halts_comparatorLayout (n : ℕ)
    (table payload : List Bool) :
    HaltsBy routeMachine (comparatorLayout n table payload)
      (routeClock n table.length) := by
  unfold HaltsBy
  rw [machine_run_comparatorLayout]
  rfl

theorem routeClock_le_layout_length (n : ℕ)
    (table payload : List Bool) :
    routeClock n table.length ≤
      (comparatorLayout n table payload).length := by
  rw [comparatorLayout_length]
  simp [routeClock]

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine.machine_run_comparatorLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine.machine_halts_comparatorLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine.run_reject_ten
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine.run_reject_zerozero
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine.reverse_forward_tracks_eq_layout
