import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeZeroCopyRebase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupNextStage

/-!
# Executable zero-copy runtime source rebase

This file realizes the proved zero-copy splice with the verified finite-control
block writer.  It proves exact tape semantics, halting, and the scheduled
post-cashout specialization.  The writer still receives the proved splice
offset and remaining-block count as parameters; eliminating those parameters
with a runtime locator is the subsequent uniformity step.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinShiftLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupNextStage

/-- The concrete finite-control writer for a splice ending at `R`. -/
def zeroCopyRebaseMachine (R d : Nat) : Machine :=
  stageMachine (R - (zeroCopyRebasePrefix d).length)
    (zeroCopyRebasePrefix d)

def zeroCopyRebaseClock (R d : Nat) : Nat :=
  R - (zeroCopyRebasePrefix d).length +
    (zeroCopyRebasePrefix d).length

theorem stagedTape_length_eq (P : Nat) (bits : List Bool) (k : Nat)
    (T : List Bool) (hk : k ≤ bits.length)
    (hbound : P + k ≤ T.length) :
    (stagedTape P bits k T).length = T.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hprev : (stagedTape P bits k T).length = T.length :=
        ih (by omega) (by omega)
      simp only [stagedTape]
      rw [writeAt_of_lt _ (by rw [hprev]; omega), List.length_set, hprev]

/-- Writes strictly before `R` preserve the complete suffix at `R`. -/
theorem stagedTape_drop_after (P : Nat) (bits : List Bool) (k R : Nat)
    (T : List Bool) (hk : k ≤ bits.length)
    (hwrite : P + k ≤ R) (hR : R ≤ T.length) :
    (stagedTape P bits k T).drop R = T.drop R := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hprev : (stagedTape P bits k T).length = T.length :=
        stagedTape_length_eq P bits k T (by omega) (by omega)
      simp only [stagedTape]
      rw [writeAt_of_lt _ (by rw [hprev]; omega),
        List.drop_set_of_lt (by omega), ih (by omega) (by omega)]

/-- The fully written window, read from its first cell, is the requested block. -/
theorem stagedTape_take_written (P : Nat) (bits T : List Bool)
    (hbound : P + bits.length ≤ T.length) :
    ((stagedTape P bits bits.length T).drop P).take bits.length = bits := by
  let S := stagedTape P bits bits.length T
  have hlen : S.length = T.length :=
    stagedTape_length_eq P bits bits.length T (by omega) hbound
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, hlen, Nat.min_eq_left]
    omega
  · intro i hi1 hi2
    have hi : i < bits.length := by simpa using hi2
    have hPi : P + i < S.length := by rw [hlen]; omega
    have hw := stagedTape_getD_written P bits T hi (by omega)
    rw [List.getElem_take, List.getElem_drop,
      ← List.getD_eq_getElem S false hPi,
      ← List.getD_eq_getElem bits false hi]
    exact hw

/-- Exact suffix semantics of the executable writer. -/
theorem stagedTape_zeroCopy_splice (T : List Bool) (R d : Nat)
    (hfit : (zeroCopyRebasePrefix d).length ≤ R)
    (hR : R ≤ T.length) :
    (stagedTape (R - (zeroCopyRebasePrefix d).length)
        (zeroCopyRebasePrefix d) (zeroCopyRebasePrefix d).length T).drop
        (R - (zeroCopyRebasePrefix d).length) =
      zeroCopyRebasePrefix d ++ T.drop R := by
  let L := (zeroCopyRebasePrefix d).length
  let P := R - L
  let S := stagedTape P (zeroCopyRebasePrefix d) L T
  have hPL : P + L = R := by dsimp [P, L]; omega
  have htake : (S.drop P).take L = zeroCopyRebasePrefix d := by
    dsimp [S]
    apply stagedTape_take_written
    rw [hPL]
    exact hR
  have hdrop : S.drop R = T.drop R := by
    dsimp [S]
    apply stagedTape_drop_after
    · exact le_rfl
    · rw [hPL]
    · exact hR
  calc
    S.drop P = (S.drop P).take L ++ (S.drop P).drop L := by
      exact (List.take_append_drop L (S.drop P)).symm
    _ = zeroCopyRebasePrefix d ++ S.drop R := by
      rw [htake, List.drop_drop, hPL]
    _ = zeroCopyRebasePrefix d ++ T.drop R := by rw [hdrop]

/-- Complete executable run: scan, write the rebase prefix, halt, and expose
the exact zero-copy spliced suffix. -/
theorem zeroCopyRebaseMachine_run (T : List Bool) (R d : Nat)
    (hfit : (zeroCopyRebasePrefix d).length ≤ R)
    (hR : R ≤ T.length) :
    let P := R - (zeroCopyRebasePrefix d).length
    let bits := zeroCopyRebasePrefix d
    let cf := run (zeroCopyRebaseMachine R d) (zeroCopyRebaseClock R d)
      (init (zeroCopyRebaseMachine R d) T)
    (zeroCopyRebaseMachine R d).halt cf.st = true ∧
      cf.tp.drop P = bits ++ T.drop R := by
  dsimp only
  let P := R - (zeroCopyRebasePrefix d).length
  let bits := zeroCopyRebasePrefix d
  have hclock : zeroCopyRebaseClock R d = P + bits.length := by rfl
  have hrun := stageMachine_run P bits T
  constructor
  · rw [zeroCopyRebaseMachine, hclock, hrun]
    exact stageMachine_halt_final P bits
  · rw [zeroCopyRebaseMachine, hclock, hrun]
    exact stagedTape_zeroCopy_splice T R d hfit hR

/-- Scheduled nonterminal specialization: the actual finite-control writer
turns a completed cashout tape into the canonical selector suffix for exactly
the unprocessed schedule. -/
theorem scheduledRuntimeRelativeOutput_zeroCopyRebaseMachine
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) clock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    let P := R - (zeroCopyRebasePrefix rest.length).length
    let cf := run (zeroCopyRebaseMachine R rest.length)
      (zeroCopyRebaseClock R rest.length)
      (init (zeroCopyRebaseMachine R rest.length) rcf.tp)
    (zeroCopyRebaseMachine R rest.length).halt cf.st = true ∧
      cf.tp.drop P = sourceSelectorInput rest.length 0 rest := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let clock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) clock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hfuture : rcf.tp.drop R = selectedTail rest := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      clock, rcf, R] using
      scheduledRuntimeRelativeOutput_futureArchive x w ht
  have hfit0 := scheduled_zeroCopyRebase_fits x w ht
  dsimp only at hfit0
  have hfit : (zeroCopyRebasePrefix rest.length).length ≤ R := by
    have hs : (zeroCopyRebasePrefix rest.length).length ≤
        pre.length + 2 * bits.length + 4 := by
      simpa [B, schedule, preBlocks, l, bits, rest, pre] using hfit0
    dsimp [R]
    omega
  have hR : R ≤ rcf.tp.length := by
    have hrestpos : 0 < (selectedTail rest).length := by
      have hrs : rest ≠ [] := by
        apply List.ne_nil_of_length_pos
        simp [rest, schedule, literalTapeSchedule]
        omega
      obtain ⟨a, as, hr⟩ := List.exists_cons_of_ne_nil hrs
      rw [hr]
      simp [selectedTail, freshSourceBlock, flattenPairs_length]
    have hlen := congrArg List.length hfuture
    simp only [List.length_drop] at hlen
    omega
  have hr := zeroCopyRebaseMachine_run rcf.tp R rest.length hfit hR
  constructor
  · exact hr.1
  · rw [hr.2, hfuture, zeroCopyRebasePrefix_archive]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine.stagedTape_zeroCopy_splice
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine.zeroCopyRebaseMachine_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebaseMachine.scheduledRuntimeRelativeOutput_zeroCopyRebaseMachine
