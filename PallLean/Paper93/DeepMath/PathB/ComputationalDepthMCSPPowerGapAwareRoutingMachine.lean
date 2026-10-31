import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareFinishMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorRoutingMachine

/-!
# MCSP verifier: finite-control routing over the physical gapped layout

The ordinary four-counter router rejects the retained internal `00` after the
first table counter.  This file gives the physical router one deliberate,
validated two-cell gap transition after track zero.  All other doubled pairs
retain the ordinary router's legality checks and tape-preserving behavior.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorRoutingMachine
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine

inductive GapRouteState
  | scan (track : Fin 4)
  | sawFalse (track : Fin 4)
  | sawTrue (track : Fin 4)
  | gapLo
  | gapHi
  | accept
  | reject
  deriving DecidableEq, Fintype

open GapRouteState

/-- Track zero is followed by the unique physical gap; later markers advance
normally, and track three accepts. -/
def afterGapTrack (i : Fin 4) : GapRouteState :=
  if i.val = 0 then .gapLo
  else if h : i.val + 1 < 4 then .scan ⟨i.val + 1, h⟩
  else .accept

def gapRouteProgram : Program where
  Label := GapRouteState
  fin := inferInstance
  dec := inferInstance
  start := .scan 0
  code
    | .scan i =>
        .act ⟨.sawFalse i, none, 1⟩ ⟨.sawTrue i, none, 1⟩
    | .sawFalse i =>
        .act ⟨.reject, none, 1⟩ ⟨afterGapTrack i, none, 1⟩
    | .sawTrue i =>
        .act ⟨.reject, none, 1⟩ ⟨.scan i, none, 1⟩
    | .gapLo =>
        .act ⟨.gapHi, none, 1⟩ ⟨.reject, none, 2⟩
    | .gapHi =>
        .act ⟨.scan 1, none, 1⟩ ⟨.reject, none, 2⟩
    | .accept => .halt true
    | .reject => .halt false

def gapRouteMachine : Machine := compile gapRouteProgram

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem step_gapRoute_scan_true (i : Fin 4) (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.scan i, P.length, P ++ true :: R⟩ =
      ⟨.sawTrue i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code (.scan i) =
      .act ⟨.sawFalse i, none, 1⟩
        ⟨.sawTrue i, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_scan_false (i : Fin 4) (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.scan i, P.length, P ++ false :: R⟩ =
      ⟨.sawFalse i, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code (.scan i) =
      .act ⟨.sawFalse i, none, 1⟩
        ⟨.sawTrue i, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_sawTrue_true (i : Fin 4) (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.sawTrue i, P.length, P ++ true :: R⟩ =
      ⟨.scan i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code (.sawTrue i) =
      .act ⟨.reject, none, 1⟩ ⟨.scan i, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_sawFalse_true (i : Fin 4) (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.sawFalse i, P.length, P ++ true :: R⟩ =
      ⟨afterGapTrack i, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code (.sawFalse i) =
      .act ⟨.reject, none, 1⟩ ⟨afterGapTrack i, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_gapLo_false (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.gapLo, P.length, P ++ false :: R⟩ =
      ⟨.gapHi, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code .gapLo =
      .act ⟨.gapHi, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_gapHi_false (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.gapHi, P.length, P ++ false :: R⟩ =
      ⟨.scan 1, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code .gapHi =
      .act ⟨.scan 1, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem run_gapRoute_data (i : Fin 4) (P R : List Bool) :
    asmRun gapRouteProgram 2
      ⟨.scan i, P.length, P ++ true :: true :: R⟩ =
      ⟨.scan i, P.length + 2, P ++ true :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep gapRouteProgram
    (asmStep gapRouteProgram
      ⟨.scan i, P.length, P ++ true :: true :: R⟩) = _
  rw [step_gapRoute_scan_true i P (true :: R)]
  rw [show P ++ true :: true :: R =
    (P ++ [true]) ++ true :: R by simp]
  simpa using step_gapRoute_sawTrue_true i (P ++ [true]) R

theorem run_gapRoute_marker (i : Fin 4) (P R : List Bool) :
    asmRun gapRouteProgram 2
      ⟨.scan i, P.length, P ++ false :: true :: R⟩ =
      ⟨afterGapTrack i, P.length + 2, P ++ false :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep gapRouteProgram
    (asmStep gapRouteProgram
      ⟨.scan i, P.length, P ++ false :: true :: R⟩) = _
  rw [step_gapRoute_scan_false i P (true :: R)]
  rw [show P ++ false :: true :: R =
    (P ++ [false]) ++ true :: R by simp]
  simpa using step_gapRoute_sawFalse_true i (P ++ [false]) R

/-- The unique expected `00` is validated and crossed. -/
theorem run_gapRoute_gap (P R : List Bool) :
    asmRun gapRouteProgram 2
      ⟨.gapLo, P.length, P ++ false :: false :: R⟩ =
      ⟨.scan 1, P.length + 2, P ++ false :: false :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep gapRouteProgram
    (asmStep gapRouteProgram
      ⟨.gapLo, P.length, P ++ false :: false :: R⟩) = _
  rw [step_gapRoute_gapLo_false P (false :: R)]
  rw [show P ++ false :: false :: R =
    (P ++ [false]) ++ false :: R by simp]
  simpa using step_gapRoute_gapHi_false (P ++ [false]) R

theorem step_gapRoute_bad_lo (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.gapLo, P.length, P ++ true :: R⟩ =
      ⟨.reject, P.length, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code .gapLo =
      .act ⟨.gapHi, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem step_gapRoute_bad_hi (P R : List Bool) :
    asmStep gapRouteProgram
      ⟨.gapHi, P.length, P ++ true :: R⟩ =
      ⟨.reject, P.length, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show gapRouteProgram.code .gapHi =
      .act ⟨.scan 1, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem asmRun_gapRoute_counter (i : Fin 4)
    (P R : List Bool) (k : ℕ) :
    asmRun gapRouteProgram (2 * k + 2)
      ⟨.scan i, P.length, P ++ unaryD k ++ R⟩ =
      ⟨afterGapTrack i, P.length + 2 * k + 2,
        P ++ unaryD k ++ R⟩ := by
  rw [unaryD_eq]
  induction k generalizing P with
  | zero =>
      simpa using run_gapRoute_marker i P R
  | succ k ih =>
      rw [show 2 * (k + 1) + 2 = 2 + (2 * k + 2) by omega,
        asmRun_add, show 2 * (k + 1) = 2 + 2 * k by omega,
        List.replicate_add]
      change asmRun gapRouteProgram (2 * k + 2)
        (asmRun gapRouteProgram 2
          ⟨.scan i, P.length,
            P ++ true :: true ::
              (List.replicate (2 * k) true ++ [false, true]) ++ R⟩) = _
      rw [show P ++ true :: true ::
            (List.replicate (2 * k) true ++ [false, true]) ++ R =
          P ++ true :: true ::
            ((List.replicate (2 * k) true ++ [false, true]) ++ R) by
              simp [List.append_assoc],
        run_gapRoute_data i P
          ((List.replicate (2 * k) true ++ [false, true]) ++ R)]
      have h := ih (P ++ [true, true])
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

@[simp] theorem afterGapTrack_zero :
    afterGapTrack (0 : Fin 4) = .gapLo := rfl

@[simp] theorem afterGapTrack_one :
    afterGapTrack (1 : Fin 4) = .scan 2 := rfl

@[simp] theorem afterGapTrack_two :
    afterGapTrack (2 : Fin 4) = .scan 3 := rfl

@[simp] theorem afterGapTrack_three :
    afterGapTrack (3 : Fin 4) = .accept := rfl

def gapRouteClock (n a : ℕ) : ℕ :=
  4 * a + 4 * (2 ^ n) + 10

/-- Exact assembly run across all four counters and the retained gap. -/
theorem asmRun_gappedComparatorLayout (n a : ℕ)
    (payload : List Bool) :
    asmRun gapRouteProgram (gapRouteClock n a)
      (asmInit gapRouteProgram (gappedComparatorLayout n a payload)) =
      ⟨.accept, gapRouteClock n a,
        gappedComparatorLayout n a payload⟩ := by
  unfold asmInit gapRouteClock gappedComparatorLayout powBridge
  rw [show 4 * a + 4 * 2 ^ n + 10 =
      (2 * a + 2) +
        (2 + ((2 * 2 ^ n + 2) +
          ((2 * 2 ^ n + 2) + (2 * a + 2)))) by ring,
    asmRun_add]
  simp only [List.append_assoc]
  change asmRun gapRouteProgram
      (2 + ((2 * 2 ^ n + 2) +
        ((2 * 2 ^ n + 2) + (2 * a + 2))))
      (asmRun gapRouteProgram (2 * a + 2)
        ⟨.scan (0 : Fin 4), 0,
          unaryD a ++ ([false, false] ++
            (unaryD (2 ^ n) ++
              (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩) = _
  have h0 := asmRun_gapRoute_counter (0 : Fin 4) []
    ([false, false] ++
      (unaryD (2 ^ n) ++
        (unaryD (2 ^ n) ++ (unaryD a ++ payload)))) a
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at h0
  rw [h0]
  simp only [afterGapTrack_zero]
  rw [asmRun_add]
  have hgap : asmRun gapRouteProgram 2
      ⟨.gapLo, 2 * a + 2,
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ =
      ⟨.scan 1, 2 * a + 4,
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ := by
    have h := run_gapRoute_gap (unaryD a)
      (unaryD (2 ^ n) ++
        (unaryD (2 ^ n) ++ (unaryD a ++ payload)))
    simpa [unaryD_length, List.append_assoc] using h
  rw [hgap]
  rw [asmRun_add]
  have h1 := asmRun_gapRoute_counter (1 : Fin 4)
    (unaryD a ++ [false, false])
    (unaryD (2 ^ n) ++ (unaryD a ++ payload)) (2 ^ n)
  simp only [afterGapTrack_one] at h1
  have h1' : asmRun gapRouteProgram (2 * 2 ^ n + 2)
      ⟨.scan (1 : Fin 4), 2 * a + 4,
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ =
      ⟨.scan 2, 2 * a + 4 + (2 * 2 ^ n + 2),
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ := by
    simpa [List.append_assoc, unaryD_length] using h1
  rw [h1']
  rw [asmRun_add]
  have h2 := asmRun_gapRoute_counter (2 : Fin 4)
    (unaryD a ++ [false, false] ++ unaryD (2 ^ n))
    (unaryD a ++ payload) (2 ^ n)
  simp only [afterGapTrack_two] at h2
  have h2' : asmRun gapRouteProgram (2 * 2 ^ n + 2)
      ⟨.scan (2 : Fin 4), 2 * a + 4 + (2 * 2 ^ n + 2),
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ =
      ⟨.scan 3,
        2 * a + 4 + (2 * 2 ^ n + 2) + (2 * 2 ^ n + 2),
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ := by
    convert h2 using 1 <;>
      simp [List.append_assoc, unaryD_length] <;> ring
  rw [h2']
  have h3 := asmRun_gapRoute_counter (3 : Fin 4)
    (unaryD a ++ [false, false] ++
      unaryD (2 ^ n) ++ unaryD (2 ^ n)) payload a
  simp only [afterGapTrack_three] at h3
  have h3' : asmRun gapRouteProgram (2 * a + 2)
      ⟨.scan (3 : Fin 4),
        2 * a + 4 + (2 * 2 ^ n + 2) + (2 * 2 ^ n + 2),
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ =
      ⟨.accept,
        2 * a + 4 + (2 * 2 ^ n + 2) +
          (2 * 2 ^ n + 2) + (2 * a + 2),
        unaryD a ++ ([false, false] ++
          (unaryD (2 ^ n) ++
            (unaryD (2 ^ n) ++ (unaryD a ++ payload))))⟩ := by
    convert h3 using 1 <;>
      simp [List.append_assoc, unaryD_length, Nat.add_assoc] <;> ring
  rw [h3']
  congr 1 <;> ring

theorem machine_run_gappedComparatorLayout (n a : ℕ)
    (payload : List Bool) :
    run gapRouteMachine (gapRouteClock n a)
      (init gapRouteMachine (gappedComparatorLayout n a payload)) =
      ⟨.accept, gapRouteClock n a,
        gappedComparatorLayout n a payload⟩ := by
  unfold gapRouteMachine
  rw [compile_run_init, asmRun_gappedComparatorLayout]
  rfl

theorem machine_halts_gappedComparatorLayout (n a : ℕ)
    (payload : List Bool) :
    HaltsBy gapRouteMachine (gappedComparatorLayout n a payload)
      (gapRouteClock n a) := by
  unfold HaltsBy
  rw [machine_run_gappedComparatorLayout]
  rfl

/-! ## Exact comparison windows derived from the physical layout -/

def gappedReverseTape (n : ℕ) (table : List Bool) : List Bool :=
  unaryD table.length ++ [false, false] ++ unaryD (2 ^ n)

def gappedForwardTape (n : ℕ) (table : List Bool) : List Bool :=
  unaryD (2 ^ n) ++ unaryD table.length

private theorem take_two_blocks (A B R : List Bool) :
    (A ++ B ++ R).take (A.length + B.length) = A ++ B := by
  rw [← List.length_append]
  simpa [List.append_assoc] using
    (@List.take_left Bool (A ++ B) R)

private theorem drop_two_blocks (A B R : List Bool) :
    (A ++ B ++ R).drop (A.length + B.length) = R := by
  rw [← List.length_append]
  simpa [List.append_assoc] using
    (@List.drop_left Bool (A ++ B) R)

theorem gappedLayout_reverse_prefix (n : ℕ)
    (table payload : List Bool) :
    (gappedComparatorLayout n table.length payload).take
        ((unaryD table.length).length + 2 + (unaryD (2 ^ n)).length) =
      gappedReverseTape n table := by
  have h := take_two_blocks
    (unaryD table.length ++ [false, false]) (unaryD (2 ^ n))
    (unaryD (2 ^ n) ++ unaryD table.length ++ payload)
  simpa [gappedComparatorLayout, gappedReverseTape, powBridge,
    List.append_assoc] using h

/-- The reverse comparison input is obtained by the one explicit two-cell
gap skip; no other cell is removed or reordered. -/
theorem eraseGap_gappedReverseTape (n : ℕ) (table : List Bool) :
    erasePowerHome table.length (gappedReverseTape n table) =
      reverseTape n table := by
  simp [erasePowerHome, gappedReverseTape, reverseTape,
    List.append_assoc]

theorem gappedLayout_after_reverse (n : ℕ)
    (table payload : List Bool) :
    (gappedComparatorLayout n table.length payload).drop
        ((unaryD table.length).length + 2 + (unaryD (2 ^ n)).length) =
      gappedForwardTape n table ++ payload := by
  have h := drop_two_blocks
    (unaryD table.length ++ [false, false]) (unaryD (2 ^ n))
    (unaryD (2 ^ n) ++ unaryD table.length ++ payload)
  simpa [gappedComparatorLayout, gappedForwardTape, powBridge,
    List.append_assoc] using h

theorem gappedLayout_forward_window (n : ℕ)
    (table payload : List Bool) :
    ((gappedComparatorLayout n table.length payload).drop
        ((unaryD table.length).length + 2 +
          (unaryD (2 ^ n)).length)).take
            ((unaryD (2 ^ n)).length +
              (unaryD table.length).length) =
      gappedForwardTape n table := by
  rw [gappedLayout_after_reverse]
  have h := take_two_blocks (unaryD (2 ^ n))
    (unaryD table.length) payload
  simpa [gappedForwardTape, List.append_assoc] using h

/-- Both verified destructive comparator calls, with their inputs extracted
from the exact physical gapped layout.  The reverse input uses precisely the
proved two-cell gap erasure; the forward input is already contiguous. -/
def gappedRoutedExtentDecision (n : ℕ) (table : List Bool) : Bool :=
  decideOut compareMachine
      (erasePowerHome table.length (gappedReverseTape n table))
      (cmpClock table.length (2 ^ n)) &&
    decideOut compareMachine (gappedForwardTape n table)
      (cmpClock (2 ^ n) table.length)

theorem gappedRoutedExtentDecision_eq (n : ℕ) (table : List Bool) :
    gappedRoutedExtentDecision n table =
      (decide (table.length ≤ 2 ^ n) &&
        decide (2 ^ n ≤ table.length)) := by
  unfold gappedRoutedExtentDecision decideOut
  rw [eraseGap_gappedReverseTape]
  simp only [reverseTape, gappedForwardTape]
  rw [compare_decides, compare_decides]

theorem gappedRoutedExtentDecision_true_iff (n : ℕ)
    (table : List Bool) :
    gappedRoutedExtentDecision n table = true ↔
      table.length = 2 ^ n := by
  rw [gappedRoutedExtentDecision_eq]
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · intro h
    simp [h]

theorem gapped_reverse_comparator_halts (n : ℕ)
    (table : List Bool) :
    HaltsBy compareMachine
      (erasePowerHome table.length (gappedReverseTape n table))
      (cmpClock table.length (2 ^ n)) := by
  rw [eraseGap_gappedReverseTape]
  exact reverse_routed_halts n table

theorem gapped_forward_comparator_halts (n : ℕ)
    (table : List Bool) :
    HaltsBy compareMachine (gappedForwardTape n table)
      (cmpClock (2 ^ n) table.length) := by
  simpa [gappedForwardTape, forwardTape] using
    forward_routed_halts n table

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.machine_run_gappedComparatorLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.machine_halts_gappedComparatorLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.step_gapRoute_bad_lo
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.step_gapRoute_bad_hi
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.gappedRoutedExtentDecision_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.gapped_reverse_comparator_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine.gapped_forward_comparator_halts
