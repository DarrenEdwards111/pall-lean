import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareRoutingMachine

/-!
# MCSP verifier: physical local-home adapter for the forward comparator

The destructive unary comparator uses move `3`, an absolute reset to tape cell
zero.  The forward comparison in `gappedComparatorLayout`, however, begins at
the second power-counter track.  This file supplies the missing physical
adapter: one fixed finite controller resets to zero, scans two possibly
destructively marked `10/11` counter tracks, validates and crosses the retained
`00`, and halts exactly on the low cell of the untouched forward counter.

The proofs allow arbitrary legal marking depths in both consumed tracks.  Thus
the adapter is reusable after every local reset of a future in-place comparator
wrapper; it does not rely on either consumed counter remaining all `11`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareRoutingMachine

/-- `workD a j` is one doubled unary counter after `j` destructive marks:
`10^j 11^(a-j) 01`. -/
def workD (a j : ℕ) : List Bool :=
  markedD j ++ List.replicate (2 * (a - j)) true ++ [false, true]

theorem workD_zero (a : ℕ) : workD a 0 = unaryD a := by
  simp [workD, markedD, unaryD_eq, List.append_assoc]

theorem workD_length (a j : ℕ) (hj : j ≤ a) :
    (workD a j).length = 2 * a + 2 := by
  simp [workD, markedD_length]
  omega

/-- Exact physical tape seen by the local-home adapter.  `rest` begins with
the untouched forward-comparison counter. -/
def compareHomeTape (a b jA jB : ℕ) (rest : List Bool) : List Bool :=
  workD a jA ++ [false, false] ++ workD b jB ++ rest

inductive CompareHomeState
  | reset
  | scan (rightTrack : Bool)
  | sawFalse (rightTrack : Bool)
  | sawTrue (rightTrack : Bool)
  | gapLo
  | gapHi
  | accept
  | reject
  deriving DecidableEq, Fintype

open CompareHomeState

def afterHomeMarker (rightTrack : Bool) : CompareHomeState :=
  if rightTrack then .accept else .gapLo

/-- Fixed finite-control reset/positioning program.  High cells of data pairs
may be either `true` (`11`) or `false` (`10`); boundary and gap cells remain
fully validated. -/
def compareHomeProgram : Program where
  Label := CompareHomeState
  fin := inferInstance
  dec := inferInstance
  start := .reset
  code
    | .reset => .act ⟨.scan false, none, 3⟩ ⟨.scan false, none, 3⟩
    | .scan t => .act ⟨.sawFalse t, none, 1⟩ ⟨.sawTrue t, none, 1⟩
    | .sawFalse t => .act ⟨.reject, none, 2⟩ ⟨afterHomeMarker t, none, 1⟩
    | .sawTrue t => .act ⟨.scan t, none, 1⟩ ⟨.scan t, none, 1⟩
    | .gapLo => .act ⟨.gapHi, none, 1⟩ ⟨.reject, none, 2⟩
    | .gapHi => .act ⟨.scan true, none, 1⟩ ⟨.reject, none, 2⟩
    | .accept => .halt true
    | .reject => .halt false

def compareHomeMachine : Machine := compile compareHomeProgram

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem step_home_reset (p : ℕ) (T : List Bool) :
    asmStep compareHomeProgram ⟨.reset, p, T⟩ =
      ⟨.scan false, 0, T⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code .reset =
      .act ⟨.scan false, none, 3⟩
        ⟨.scan false, none, 3⟩ from rfl]
  cases h : T.getD p false <;>
    simp only [Instr.select] <;> rfl

theorem step_home_scan_true (t : Bool) (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.scan t, P.length, P ++ true :: R⟩ =
      ⟨.sawTrue t, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code (.scan t) =
      .act ⟨.sawFalse t, none, 1⟩
        ⟨.sawTrue t, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_home_scan_false (t : Bool) (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.scan t, P.length, P ++ false :: R⟩ =
      ⟨.sawFalse t, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code (.scan t) =
      .act ⟨.sawFalse t, none, 1⟩
        ⟨.sawTrue t, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_home_sawTrue (t b : Bool) (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.sawTrue t, P.length, P ++ b :: R⟩ =
      ⟨.scan t, P.length + 1, P ++ b :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code (.sawTrue t) =
      .act ⟨.scan t, none, 1⟩
        ⟨.scan t, none, 1⟩ from rfl,
    getD_boundary]
  cases b <;> rfl

theorem step_home_sawFalse_true (t : Bool) (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.sawFalse t, P.length, P ++ true :: R⟩ =
      ⟨afterHomeMarker t, P.length + 1, P ++ true :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code (.sawFalse t) =
      .act ⟨.reject, none, 2⟩
        ⟨afterHomeMarker t, none, 1⟩ from rfl,
    getD_boundary]
  rfl

theorem step_home_gapLo_false (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.gapLo, P.length, P ++ false :: R⟩ =
      ⟨.gapHi, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code .gapLo =
      .act ⟨.gapHi, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem step_home_gapHi_false (P R : List Bool) :
    asmStep compareHomeProgram
      ⟨.gapHi, P.length, P ++ false :: R⟩ =
      ⟨.scan true, P.length + 1, P ++ false :: R⟩ := by
  unfold asmStep
  rw [show compareHomeProgram.code .gapHi =
      .act ⟨.scan true, none, 1⟩ ⟨.reject, none, 2⟩ from rfl,
    getD_boundary]
  rfl

theorem run_home_pair (t high : Bool) (P R : List Bool) :
    asmRun compareHomeProgram 2
      ⟨.scan t, P.length, P ++ true :: high :: R⟩ =
      ⟨.scan t, P.length + 2, P ++ true :: high :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep compareHomeProgram
    (asmStep compareHomeProgram
      ⟨.scan t, P.length, P ++ true :: high :: R⟩) = _
  rw [step_home_scan_true t P (high :: R)]
  rw [show P ++ true :: high :: R =
    (P ++ [true]) ++ high :: R by simp]
  simpa using step_home_sawTrue t high (P ++ [true]) R

theorem run_home_marker (t : Bool) (P R : List Bool) :
    asmRun compareHomeProgram 2
      ⟨.scan t, P.length, P ++ false :: true :: R⟩ =
      ⟨afterHomeMarker t, P.length + 2,
        P ++ false :: true :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep compareHomeProgram
    (asmStep compareHomeProgram
      ⟨.scan t, P.length, P ++ false :: true :: R⟩) = _
  rw [step_home_scan_false t P (true :: R)]
  rw [show P ++ false :: true :: R =
    (P ++ [false]) ++ true :: R by simp]
  simpa using step_home_sawFalse_true t (P ++ [false]) R

theorem run_home_gap (P R : List Bool) :
    asmRun compareHomeProgram 2
      ⟨.gapLo, P.length, P ++ false :: false :: R⟩ =
      ⟨.scan true, P.length + 2, P ++ false :: false :: R⟩ := by
  rw [show 2 = 1 + 1 by omega, asmRun_add]
  change asmStep compareHomeProgram
    (asmStep compareHomeProgram
      ⟨.gapLo, P.length, P ++ false :: false :: R⟩) = _
  rw [step_home_gapLo_false P (false :: R)]
  rw [show P ++ false :: false :: R =
    (P ++ [false]) ++ false :: R by simp]
  simpa using step_home_gapHi_false (P ++ [false]) R

theorem asmRun_home_marked (t : Bool) (P R : List Bool) (j : ℕ) :
    asmRun compareHomeProgram (2 * j)
      ⟨.scan t, P.length, P ++ markedD j ++ R⟩ =
      ⟨.scan t, P.length + 2 * j, P ++ markedD j ++ R⟩ := by
  induction j generalizing P with
  | zero => simp [markedD]
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 + 2 * j by omega,
        asmRun_add]
      change asmRun compareHomeProgram (2 * j)
        (asmRun compareHomeProgram 2
          ⟨.scan t, P.length,
            P ++ true :: false :: markedD j ++ R⟩) = _
      rw [show P ++ true :: false :: markedD j ++ R =
          P ++ true :: false :: (markedD j ++ R) by
            simp [List.append_assoc],
        run_home_pair t false P (markedD j ++ R)]
      have h := ih (P ++ [true, false])
      simpa [markedD, List.append_assoc, Nat.add_assoc] using h

theorem asmRun_home_data (t : Bool) (P R : List Bool) (k : ℕ) :
    asmRun compareHomeProgram (2 * k)
      ⟨.scan t, P.length,
        P ++ List.replicate (2 * k) true ++ R⟩ =
      ⟨.scan t, P.length + 2 * k,
        P ++ List.replicate (2 * k) true ++ R⟩ := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega,
        asmRun_add, List.replicate_add]
      simp only [List.replicate_succ, List.replicate_zero,
        List.nil_append, List.cons_append]
      rw [show P ++ true :: true :: List.replicate (2 * k) true ++ R =
          P ++ true :: true :: (List.replicate (2 * k) true ++ R) by
            simp [List.append_assoc]]
      change asmRun compareHomeProgram (2 * k)
        (asmRun compareHomeProgram 2
          ⟨.scan t, P.length,
            P ++ true :: true ::
              (List.replicate (2 * k) true ++ R)⟩) = _
      rw [run_home_pair t true P
        (List.replicate (2 * k) true ++ R)]
      have h := ih (P ++ [true, true])
      simpa [List.append_assoc, Nat.add_assoc] using h

theorem asmRun_home_counter (t : Bool) (P R : List Bool)
    (a j : ℕ) (hj : j ≤ a) :
    asmRun compareHomeProgram (2 * a + 2)
      ⟨.scan t, P.length, P ++ workD a j ++ R⟩ =
      ⟨afterHomeMarker t, P.length + 2 * a + 2,
        P ++ workD a j ++ R⟩ := by
  unfold workD
  simp only [List.append_assoc]
  rw [show 2 * a + 2 =
      2 * j + (2 * (a - j) + 2) by omega,
    asmRun_add]
  have hm := asmRun_home_marked t P
    (List.replicate (2 * (a - j)) true ++ ([false, true] ++ R)) j
  have hm' : asmRun compareHomeProgram (2 * j)
      ⟨.scan t, P.length,
        P ++ (markedD j ++
          (List.replicate (2 * (a - j)) true ++
            ([false, true] ++ R)))⟩ =
      ⟨.scan t, P.length + 2 * j,
        P ++ (markedD j ++
          (List.replicate (2 * (a - j)) true ++
            ([false, true] ++ R)))⟩ := by
    simpa only [List.append_assoc] using hm
  rw [hm']
  rw [show 2 * (a - j) + 2 = 2 * (a - j) + 2 by rfl,
    asmRun_add]
  have hd := asmRun_home_data t (P ++ markedD j)
    ([false, true] ++ R) (a - j)
  have hd' : asmRun compareHomeProgram (2 * (a - j))
      ⟨.scan t, P.length + 2 * j,
        P ++ (markedD j ++
          (List.replicate (2 * (a - j)) true ++
            ([false, true] ++ R)))⟩ =
      ⟨.scan t, P.length + 2 * j + 2 * (a - j),
        P ++ (markedD j ++
          (List.replicate (2 * (a - j)) true ++
            ([false, true] ++ R)))⟩ := by
    convert hd using 1 <;>
      simp [List.append_assoc, markedD_length]
  rw [hd']
  have he := run_home_marker t
    (P ++ markedD j ++ List.replicate (2 * (a - j)) true) R
  convert he using 1 <;>
    simp [List.append_assoc, markedD_length, Nat.add_assoc] <;> omega

@[simp] theorem afterHomeMarker_false :
    afterHomeMarker false = .gapLo := rfl

@[simp] theorem afterHomeMarker_true :
    afterHomeMarker true = .accept := rfl

/-- Exact local-home clock, including the initial absolute reset. -/
def compareHomeClock (a b : ℕ) : ℕ := 2 * a + 2 * b + 7

/-- From any incoming head position, the assembly controller resets, accepts
arbitrary legal marking depths in both consumed tracks, validates the gap, and
lands exactly at the beginning of `rest`. -/
theorem asmRun_compareHome (a b jA jB p : ℕ)
    (hjA : jA ≤ a) (hjB : jB ≤ b) (rest : List Bool) :
    asmRun compareHomeProgram (compareHomeClock a b)
      ⟨.reset, p, compareHomeTape a b jA jB rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b jA jB rest⟩ := by
  unfold compareHomeClock compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 2 * b + 7 =
      1 + ((2 * a + 2) + (2 + (2 * b + 2))) by omega,
    asmRun_add]
  rw [show 1 = 0 + 1 by omega, asmRun_succ, asmRun_zero,
    step_home_reset]
  rw [asmRun_add]
  have hA := asmRun_home_counter false []
    ([false, false] ++ (workD b jB ++ rest)) a jA hjA
  simp only [List.length_nil, List.nil_append, Nat.zero_add,
    afterHomeMarker_false] at hA
  rw [hA]
  rw [asmRun_add]
  have hg := run_home_gap (workD a jA) (workD b jB ++ rest)
  have hlenA := workD_length a jA hjA
  rw [hlenA] at hg
  have hg' : asmRun compareHomeProgram 2
      ⟨.gapLo, 2 * a + 2,
        workD a jA ++ ([false, false] ++ (workD b jB ++ rest))⟩ =
      ⟨.scan true, 2 * a + 4,
        workD a jA ++ ([false, false] ++ (workD b jB ++ rest))⟩ := by
    convert hg using 1 <;>
      simp [List.append_assoc] <;> omega
  rw [hg']
  have hB := asmRun_home_counter true
    (workD a jA ++ [false, false]) rest b jB hjB
  simp only [afterHomeMarker_true] at hB
  have hlenB := workD_length b jB hjB
  convert hB using 1 <;>
    simp [List.append_assoc, hlenA, hlenB] <;> omega

theorem machine_run_compareHome_from (a b jA jB p : ℕ)
    (hjA : jA ≤ a) (hjB : jB ≤ b) (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      ⟨.reset, p, compareHomeTape a b jA jB rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b jA jB rest⟩ := by
  unfold compareHomeMachine
  change run (compile compareHomeProgram) (compareHomeClock a b)
      (lowerCfg compareHomeProgram
        ⟨.reset, p, compareHomeTape a b jA jB rest⟩) =
    lowerCfg compareHomeProgram
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b jA jB rest⟩
  rw [compile_run,
    asmRun_compareHome a b jA jB p hjA hjB rest]

theorem machine_run_compareHome (a b jA jB : ℕ)
    (hjA : jA ≤ a) (hjB : jB ≤ b) (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      (init compareHomeMachine (compareHomeTape a b jA jB rest)) =
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b jA jB rest⟩ := by
  simpa [compareHomeMachine, init] using
    machine_run_compareHome_from a b jA jB 0 hjA hjB rest

theorem compareHome_halts (a b jA jB : ℕ)
    (hjA : jA ≤ a) (hjB : jB ≤ b) (rest : List Bool) :
    HaltsBy compareHomeMachine (compareHomeTape a b jA jB rest)
      (compareHomeClock a b) := by
  unfold HaltsBy
  rw [machine_run_compareHome a b jA jB hjA hjB rest]
  rfl

/-- The landing cell is exactly the beginning of `rest`; the adapter neither
deletes the physical gap nor changes any marked cell. -/
theorem compareHomeTape_drop (a b jA jB : ℕ)
    (hjA : jA ≤ a) (hjB : jB ≤ b) (rest : List Bool) :
    (compareHomeTape a b jA jB rest).drop
        (2 * a + 2 * b + 6) = rest := by
  unfold compareHomeTape
  rw [show 2 * a + 2 * b + 6 =
      (workD a jA ++ [false, false] ++ workD b jB).length by
        simp [workD_length _ _ hjA, workD_length _ _ hjB]
        omega]
  simpa [List.append_assoc] using
    (@List.drop_left Bool
      (workD a jA ++ [false, false] ++ workD b jB) rest)

/-- Local-home invocation after the comparator's accepting endgame
(`a ≤ b`): both work tracks have exactly `a` marks. -/
theorem machine_run_after_reverse_accept (a b p : ℕ)
    (hab : a ≤ b) (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      ⟨.reset, p, compareHomeTape a b a a rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b a a rest⟩ :=
  machine_run_compareHome_from a b a a p (le_refl a) hab rest

/-- Local-home invocation after the comparator's rejecting endgame
(`b < a`): `A` has `b+1` marks and `B` has `b` marks. -/
theorem machine_run_after_reverse_reject (a b p : ℕ)
    (hab : b < a) (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      ⟨.reset, p, compareHomeTape a b (b + 1) b rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        compareHomeTape a b (b + 1) b rest⟩ :=
  machine_run_compareHome_from a b (b + 1) b p
    (by omega) (le_refl b) rest

/-- Specialization to the untouched physical comparator layout: the adapter
lands on the second power counter, whose suffix is exactly the forward
comparison input followed by the payload. -/
theorem machine_run_gappedComparatorLayout_to_forward (n a : ℕ)
    (payload : List Bool) :
    run compareHomeMachine (compareHomeClock a (2 ^ n))
      (init compareHomeMachine (gappedComparatorLayout n a payload)) =
      ⟨.accept, 2 * a + 2 * (2 ^ n) + 6,
        gappedComparatorLayout n a payload⟩ := by
  have h := machine_run_compareHome a (2 ^ n) 0 0
    (Nat.zero_le a) (Nat.zero_le (2 ^ n))
    (unaryD (2 ^ n) ++ unaryD a ++ payload)
  simpa [compareHomeTape, workD_zero, gappedComparatorLayout,
    powBridge, List.append_assoc] using h

theorem forward_suffix_at_compareHome (n : ℕ) (table payload : List Bool) :
    (gappedComparatorLayout n table.length payload).drop
        (2 * table.length + 2 * (2 ^ n) + 6) =
      gappedForwardTape n table ++ payload := by
  convert gappedLayout_after_reverse n table payload using 1 <;>
    simp [unaryD_length] <;> ring

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine.machine_run_gappedComparatorLayout_to_forward
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine.compareHome_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine.machine_run_after_reverse_accept
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine.machine_run_after_reverse_reject
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine.forward_suffix_at_compareHome
