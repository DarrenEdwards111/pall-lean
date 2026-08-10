import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactChain

/-!
# Charged local lookup: one-machine marked compaction composition

This module places the certified exact-clock clear, pass, and rewind
controllers behind an `.olean` boundary, then recursively composes every
workspace pass with head-preserving physical handoffs.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain

/-- The exact-clock run theorem in the configuration shape consumed by
`headSeq_run_at`. -/
theorem exactClockMachine_run_of_run (M : Machine) (n p p' : Nat)
    (T T' : List Bool) (s : M.State)
    (hlive : ∀ st, M.halt st = false)
    (hrun : run M n ⟨M.start, p, T⟩ = ⟨s, p', T'⟩) :
    run (exactClockMachine M n) n
        ⟨(exactClockMachine M n).start, p, T⟩ =
      ⟨(⟨n, by omega⟩, s), p', T'⟩ := by
  have hclock := exactClockMachine_run M n
    (⟨M.start, p, T⟩ : Cfg M) (fun _ _ => hlive _)
  rw [hrun] at hclock
  simpa [exactClockCfg, exactClockMachine] using hclock

/-- Recursive physical controller for all workspace passes.  A nonfinal
round is one exact-clock bubble pass, one exact-clock rewind, and the
controller for the remaining holes.  The final round omits its rewind. -/
def runtimeCompactPassScheduleMachine
    (workspace : List (Bool × Bool)) : Nat → Machine
  | 0 => exactClockMachine runtimeCompactRewindMachine 0
  | 1 => exactClockMachine runtimeCompactBubbleLoopMachine
      (8 * workspace.length)
  | n + 2 =>
      headSeqMachine
        (exactClockMachine runtimeCompactBubbleLoopMachine
          (8 * workspace.length))
        (headSeqMachine
          (exactClockMachine runtimeCompactRewindMachine
            (2 * (workspace.length + 1)))
          (runtimeCompactPassScheduleMachine workspace (n + 1)))

def runtimeCompactPassScheduleClock
    (workspace : List (Bool × Bool)) : Nat → Nat
  | 0 => 0
  | 1 => 8 * workspace.length
  | n + 2 =>
      8 * workspace.length + 1 +
        (2 * (workspace.length + 1) + 1 +
          runtimeCompactPassScheduleClock workspace (n + 1))

@[simp] theorem runtimeCompactPassScheduleMachine_one
    (workspace : List (Bool × Bool)) :
    runtimeCompactPassScheduleMachine workspace 1 =
      exactClockMachine runtimeCompactBubbleLoopMachine
        (8 * workspace.length) := rfl

@[simp] theorem runtimeCompactPassScheduleMachine_more
    (workspace : List (Bool × Bool)) (n : Nat) :
    runtimeCompactPassScheduleMachine workspace (n + 2) =
      headSeqMachine
        (exactClockMachine runtimeCompactBubbleLoopMachine
          (8 * workspace.length))
        (headSeqMachine
          (exactClockMachine runtimeCompactRewindMachine
            (2 * (workspace.length + 1)))
          (runtimeCompactPassScheduleMachine workspace (n + 1))) := rfl

@[simp] theorem runtimeCompactPassScheduleClock_one
    (workspace : List (Bool × Bool)) :
    runtimeCompactPassScheduleClock workspace 1 =
      8 * workspace.length := rfl

@[simp] theorem runtimeCompactPassScheduleClock_more
    (workspace : List (Bool × Bool)) (n : Nat) :
    runtimeCompactPassScheduleClock workspace (n + 2) =
      8 * workspace.length + 1 +
        (2 * (workspace.length + 1) + 1 +
          runtimeCompactPassScheduleClock workspace (n + 1)) := rfl

theorem flattenPairs_replicate_false (n : Nat) :
    flattenPairs (List.replicate n (false, false)) =
      List.replicate (2 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, flattenPairs, ih]
      rw [show 2 * (n + 1) = 2 + 2 * n by omega]
      rw [List.replicate_add]
      rfl

/-- The recursively nested controller realizes the entire certified pass
schedule as one actual machine run. -/
theorem runtimeCompactAllPasses_machine_run
    (retained tail : List Bool) (workspace : List (Bool × Bool))
    {k : Nat} (h : RuntimeCompactAllPasses retained workspace tail k) :
    ∃ s : (runtimeCompactPassScheduleMachine workspace k).State,
      run (runtimeCompactPassScheduleMachine workspace k)
          (runtimeCompactPassScheduleClock workspace k)
          ⟨(runtimeCompactPassScheduleMachine workspace k).start,
            retained.length + 2 * (k - 1),
            retained ++ List.replicate (2 * k) false ++
              flattenPairs workspace ++ tail⟩ =
        ⟨s, retained.length + 2 * workspace.length,
          retained ++ flattenPairs workspace ++
            List.replicate (2 * k) false ++ tail⟩ ∧
      (runtimeCompactPassScheduleMachine workspace k).halt s = true := by
  induction h with
  | one tail finalRun finalSafe =>
      have hw := exactClockMachine_run_of_run runtimeCompactBubbleLoopMachine
        (8 * workspace.length) retained.length
        (retained.length + 2 * workspace.length)
        (retained ++ [false, false] ++ flattenPairs workspace ++ tail)
        (retained ++ flattenPairs workspace ++ [false, false] ++ tail)
        runtimeCompactBubbleLoopMachine.start (by intro; rfl) finalRun
      refine ⟨(⟨8 * workspace.length, by omega⟩,
        runtimeCompactBubbleLoopMachine.start), ?_, ?_⟩
      · simpa [runtimeCompactPassScheduleMachine,
          runtimeCompactPassScheduleClock, List.append_assoc] using hw
      · exact exactClockMachine_halt_at _ _ _
  | more tail n bridge rest ih =>
      obtain ⟨srest, hrestRun, hrestHalt⟩ := ih
      let bc := 8 * workspace.length
      let rc := 2 * (workspace.length + 1)
      let passM := exactClockMachine runtimeCompactBubbleLoopMachine bc
      let rewindM := exactClockMachine runtimeCompactRewindMachine rc
      let restM := runtimeCompactPassScheduleMachine workspace (n + 1)
      have hp := exactClockMachine_run_of_run runtimeCompactBubbleLoopMachine
        bc
        ((retained ++ flattenPairs (List.replicate n (false, false))).length + 2)
        ((retained ++ flattenPairs (List.replicate n (false, false))).length +
          2 + 2 * workspace.length)
        (retained ++ flattenPairs (List.replicate n (false, false)) ++
          [false, false, false, false] ++ flattenPairs workspace ++ tail)
        (retained ++ flattenPairs (List.replicate n (false, false)) ++
          [false, false] ++ flattenPairs workspace ++ [false, false] ++ tail)
        runtimeCompactBubbleLoopMachine.start (by intro; rfl) bridge.passRun
      have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
        rc
        ((retained ++ flattenPairs (List.replicate n (false, false))).length +
          2 + 2 * workspace.length)
        (retained ++ flattenPairs (List.replicate n (false, false))).length
        (retained ++ flattenPairs (List.replicate n (false, false)) ++
          [false, false] ++ flattenPairs workspace ++ [false, false] ++ tail)
        (retained ++ flattenPairs (List.replicate n (false, false)) ++
          [false, false] ++ flattenPairs workspace ++ [false, false] ++ tail)
        () (by intro; rfl) bridge.rewindRun
      let P := retained ++ flattenPairs (List.replicate n (false, false))
      let T0 := P ++ [false, false, false, false] ++
        flattenPairs workspace ++ tail
      let T1 := P ++ [false, false] ++ flattenPairs workspace ++
        [false, false] ++ tail
      let T2 := retained ++ flattenPairs workspace ++
        List.replicate (2 * (n + 2)) false ++ tail
      have hp' : run passM bc ⟨passM.start, P.length + 2, T0⟩ =
          ⟨(⟨bc, by omega⟩, runtimeCompactBubbleLoopMachine.start),
            P.length + 2 + 2 * workspace.length, T1⟩ := by
        simpa [passM, bc, P, T0, T1, List.append_assoc] using hp
      have hr' : run rewindM rc
          ⟨rewindM.start, P.length + 2 + 2 * workspace.length, T1⟩ =
        ⟨(⟨rc, by omega⟩, ()), P.length, T1⟩ := by
        simpa [rewindM, rc, P, T1, List.append_assoc] using hr
      have hrestRun' : run restM
          (runtimeCompactPassScheduleClock workspace (n + 1))
          ⟨restM.start, P.length, T1⟩ =
        ⟨srest, retained.length + 2 * workspace.length, T2⟩ := by
        simpa [restM, P, T1, T2, flattenPairs_replicate_false,
          List.replicate_add, Nat.mul_add, List.append_assoc] using hrestRun
      have hinner := headSeq_run_at rewindM restM T1 T1 T2
        (P.length + 2 + 2 * workspace.length) rc
        (runtimeCompactPassScheduleClock workspace (n + 1))
        P.length (retained.length + 2 * workspace.length)
        (⟨rc, by omega⟩, ()) srest hr'
        (exactClockMachine_halt_at _ _ _)
        hrestRun' hrestHalt
      have hall := headSeq_run_at passM (headSeqMachine rewindM restM)
        T0 T1 T2 (P.length + 2) bc
        (rc + 1 + runtimeCompactPassScheduleClock workspace (n + 1))
        (P.length + 2 + 2 * workspace.length)
        (retained.length + 2 * workspace.length)
        (⟨bc, by omega⟩, runtimeCompactBubbleLoopMachine.start)
        (Sum.inr srest) hp' (exactClockMachine_halt_at _ _ _)
        hinner (by simpa [headSeqMachine] using hrestHalt)
      refine ⟨Sum.inr (Sum.inr srest), ?_, ?_⟩
      · simpa [runtimeCompactPassScheduleMachine,
          runtimeCompactPassScheduleClock, passM, rewindM, restM,
          bc, rc, P, T0, T2, flattenPairs_replicate_false,
          List.replicate_add, Nat.mul_add, List.append_assoc] using hall
      · simpa [runtimeCompactPassScheduleMachine, headSeqMachine,
          rewindM, restM] using hrestHalt

/-! ## Archive-side composition -/

/-- After the final pass, traverse the trailing zero-hole block to the
archive origin, then run the existing archive-return seed controller. -/
def runtimeCompactArchiveTailMachine
    (workspace : List (Bool × Bool)) (k : Nat) : Machine :=
  headSeqMachine (runtimeCompactPassScheduleMachine workspace k)
    (headSeqMachine
      (exactClockMachine runtimeCompactClearLoopMachine (2 * k))
      runtimeArchiveReturnSeedMachine)

def runtimeCompactArchiveTailClock
    (workspace : List (Bool × Bool)) (k : Nat)
    (rest : List (List Bool)) : Nat :=
  runtimeCompactPassScheduleClock workspace k + 1 +
    (2 * k + 1 + runtimeArchiveReturnSeedClock rest)

set_option maxHeartbeats 4000000 in
/-- Complete pass schedule, physical archive advance, and archive-return
seed are one head-preserving machine run. -/
theorem runtimeCompactArchiveTail_run
    (retained : List Bool) (workspace : List (Bool × Bool))
    (first : List Bool) (more : List (List Bool))
    {k : Nat} (h : RuntimeCompactAllPasses retained workspace
      (selectedTail (first :: more)) k) :
    ∃ s : (runtimeCompactArchiveTailMachine workspace k).State,
      run (runtimeCompactArchiveTailMachine workspace k)
          (runtimeCompactArchiveTailClock workspace k (first :: more))
          ⟨(runtimeCompactArchiveTailMachine workspace k).start,
            retained.length + 2 * (k - 1),
            retained ++ List.replicate (2 * k) false ++
              flattenPairs workspace ++ selectedTail (first :: more)⟩ =
        ⟨s, retained.length + 2 * workspace.length + 2 * k,
          retained ++ flattenPairs workspace ++
            List.replicate (2 * (k - 1)) false ++ [false, true] ++
              selectedTail (first :: more)⟩ ∧
      (runtimeCompactArchiveTailMachine workspace k).halt s = true := by
  have hk : 0 < k := by cases h <;> omega
  obtain ⟨spass, hpass, hpassHalt⟩ :=
    runtimeCompactAllPasses_machine_run retained
      (selectedTail (first :: more)) workspace h
  let Tcompact := retained ++ flattenPairs workspace ++
    List.replicate (2 * k) false ++ selectedTail (first :: more)
  let Tseed := retained ++ flattenPairs workspace ++
    List.replicate (2 * (k - 1)) false ++ [false, true] ++
      selectedTail (first :: more)
  let P := retained ++ flattenPairs workspace
  let advanceM := exactClockMachine runtimeCompactClearLoopMachine (2 * k)
  have ha0 := runtimeCompactClearLoop_run P
    (List.replicate (2 * k) false) (selectedTail (first :: more))
  have ha := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * k) (retained.length + 2 * workspace.length)
    (retained.length + 2 * workspace.length + 2 * k)
    Tcompact Tcompact () (by intro; rfl) (by
      simpa [P, Tcompact, flattenPairs_length, List.append_assoc] using ha0)
  have har0 := runtimeArchiveReturnSeed_run_prefixed
    (retained ++ flattenPairs workspace ++
      List.replicate (2 * (k - 1)) false) false false first more
  have hsplit : List.replicate (2 * k) false =
      List.replicate (2 * (k - 1)) false ++ [false, false] := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, List.replicate_add]
    simp
  have hR : retained.length + 2 * workspace.length + 2 * k =
      retained.length + (2 * workspace.length + 2 * (k - 1)) + 2 := by
    omega
  have har : run runtimeArchiveReturnSeedMachine
      (runtimeArchiveReturnSeedClock (first :: more))
      ⟨runtimeArchiveReturnSeedMachine.start,
        retained.length + 2 * workspace.length + 2 * k, Tcompact⟩ =
    ⟨Sum.inr RuntimeRebaseSeedState.done,
      retained.length + 2 * workspace.length + 2 * k, Tseed⟩ := by
    simpa [Tcompact, Tseed, hsplit, hR, flattenPairs_length,
      List.append_assoc] using har0
  have hright := headSeq_run_at advanceM runtimeArchiveReturnSeedMachine
    Tcompact Tcompact Tseed
    (retained.length + 2 * workspace.length) (2 * k)
    (runtimeArchiveReturnSeedClock (first :: more))
    (retained.length + 2 * workspace.length + 2 * k)
    (retained.length + 2 * workspace.length + 2 * k)
    (⟨2 * k, by omega⟩, ()) (Sum.inr RuntimeRebaseSeedState.done)
    ha (exactClockMachine_halt_at _ _ _) har rfl
  have hall := headSeq_run_at
    (runtimeCompactPassScheduleMachine workspace k)
    (headSeqMachine advanceM runtimeArchiveReturnSeedMachine)
    (retained ++ List.replicate (2 * k) false ++
      flattenPairs workspace ++ selectedTail (first :: more))
    Tcompact Tseed (retained.length + 2 * (k - 1))
    (runtimeCompactPassScheduleClock workspace k)
    (2 * k + 1 + runtimeArchiveReturnSeedClock (first :: more))
    (retained.length + 2 * workspace.length)
    (retained.length + 2 * workspace.length + 2 * k)
    spass (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    hpass hpassHalt hright rfl
  refine ⟨Sum.inr (Sum.inr (Sum.inr RuntimeRebaseSeedState.done)), ?_, ?_⟩
  · simpa [runtimeCompactArchiveTailMachine,
      runtimeCompactArchiveTailClock, advanceM, Tcompact, Tseed,
      Nat.add_assoc] using hall
  · rfl

/-! ## Full marked compactor through archive seed -/

def runtimeMarkedCompactArchiveMachine
    (workspace : List (Bool × Bool)) (d : Nat) : Machine :=
  headSeqMachine
    (exactClockMachine runtimeCompactClearLoopMachine (2 * (d + 3)))
    (headSeqMachine
      (exactClockMachine runtimeCompactRewindMachine 2)
      (runtimeCompactArchiveTailMachine workspace (d + 3)))

def runtimeMarkedCompactArchiveClock
    (workspace : List (Bool × Bool)) (d : Nat)
    (rest : List (List Bool)) : Nat :=
  2 * (d + 3) + 1 +
    (2 + 1 + runtimeCompactArchiveTailClock workspace (d + 3) rest)

set_option maxHeartbeats 4000000 in
/-- The entire marked-to-compact repair is now one concrete machine run:
clear the stale marker/selector region, rewind onto the rightmost hole,
execute every pass/rewind, advance across the trailing holes, and invoke the
existing archive-return seed controller. -/
theorem runtimeMarkedCompactArchive_run
    (retained : List Bool) (workspace : List (Bool × Bool))
    (first : List Bool) (more : List (List Bool)) (d : Nat) :
    ∃ s : (runtimeMarkedCompactArchiveMachine workspace d).State,
      run (runtimeMarkedCompactArchiveMachine workspace d)
          (runtimeMarkedCompactArchiveClock workspace d (first :: more))
          ⟨(runtimeMarkedCompactArchiveMachine workspace d).start,
            retained.length,
            retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
              flattenPairs workspace ++ selectedTail (first :: more)⟩ =
        ⟨s, retained.length + 2 * workspace.length + 2 * (d + 3),
          retained ++ flattenPairs workspace ++
            List.replicate (2 * (d + 2)) false ++ [false, true] ++
              selectedTail (first :: more)⟩ ∧
      (runtimeMarkedCompactArchiveMachine workspace d).halt s = true := by
  let T0 := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let Tclear := retained ++ List.replicate (2 * (d + 3)) false ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let Tseed := retained ++ flattenPairs workspace ++
    List.replicate (2 * (d + 2)) false ++ [false, true] ++
      selectedTail (first :: more)
  let clearM := exactClockMachine runtimeCompactClearLoopMachine (2 * (d + 3))
  let rewindM := exactClockMachine runtimeCompactRewindMachine 2
  let tailM := runtimeCompactArchiveTailMachine workspace (d + 3)
  have hb := runtimeMarkedClearFirstHoleBridge_certificate retained
    (selectedTail (first :: more)) workspace d
  have hc := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * (d + 3)) retained.length (retained.length + 2 * (d + 3))
    T0 Tclear () (by intro; rfl) (by simpa [T0, Tclear] using hb.clearRun)
  have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
    2 (retained.length + 2 * (d + 3))
    (retained.length + 2 * (d + 2)) Tclear Tclear ()
    (by intro; rfl) (by simpa [Tclear] using hb.rewindRun)
  have hsched := runtimeMarkedAllPasses_certificate retained
    (selectedTail (first :: more)) workspace d
  obtain ⟨stail, ht, htHalt⟩ := runtimeCompactArchiveTail_run
    retained workspace first more hsched
  have ht' : run tailM
      (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
      ⟨tailM.start, retained.length + 2 * (d + 2), Tclear⟩ =
    ⟨stail, retained.length + 2 * workspace.length + 2 * (d + 3),
      Tseed⟩ := by
    simpa [tailM, Tclear, Tseed] using ht
  have hright := headSeq_run_at rewindM tailM Tclear Tclear Tseed
    (retained.length + 2 * (d + 3)) 2
    (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
    (retained.length + 2 * (d + 2))
    (retained.length + 2 * workspace.length + 2 * (d + 3))
    (⟨2, by omega⟩, ()) stail hr
    (exactClockMachine_halt_at _ _ _) ht' htHalt
  have hall := headSeq_run_at clearM (headSeqMachine rewindM tailM)
    T0 Tclear Tseed retained.length (2 * (d + 3))
    (2 + 1 + runtimeCompactArchiveTailClock workspace (d + 3)
      (first :: more))
    (retained.length + 2 * (d + 3))
    (retained.length + 2 * workspace.length + 2 * (d + 3))
    (⟨2 * (d + 3), by omega⟩, ()) (Sum.inr stail)
    hc (exactClockMachine_halt_at _ _ _) hright
    (by simpa [headSeqMachine] using htHalt)
  refine ⟨Sum.inr (Sum.inr stail), ?_, ?_⟩
  · simpa [runtimeMarkedCompactArchiveMachine,
      runtimeMarkedCompactArchiveClock, clearM, rewindM, tailM,
      T0, Tclear, Tseed, Nat.add_assoc] using hall
  · simpa [runtimeMarkedCompactArchiveMachine, headSeqMachine,
      rewindM, tailM] using htHalt

/-! ## Unary-rebase continuation -/

def runtimeMarkedCompactArchiveUnaryMachine
    (workspace : List (Bool × Bool)) (d : Nat) : Machine :=
  headSeqMachine (runtimeMarkedCompactArchiveMachine workspace d)
    runtimeUnaryRebaseMachine

set_option maxHeartbeats 4000000 in
/-- With the existing unary-writer scratch bound, the repaired marked
layout now flows through compaction, archive return, and physical unary
rebase as one concrete machine run. -/
theorem runtimeMarkedCompactArchiveUnary_run
    (retained : List Bool) (workspace : List (Bool × Bool))
    (first : List Bool) (more : List (List Bool)) (d : Nat)
    (hfit : 2 * (first :: more).length + 4 ≤
      (retained ++ flattenPairs workspace ++
        List.replicate (2 * (d + 2)) false).length) :
    ∃ base unaryClock s,
      base.IsPrefix
        (retained ++ flattenPairs workspace ++
          List.replicate (2 * (d + 2)) false) ∧
      run (runtimeMarkedCompactArchiveUnaryMachine workspace d)
          (runtimeMarkedCompactArchiveClock workspace d (first :: more) +
            1 + unaryClock)
          ⟨(runtimeMarkedCompactArchiveUnaryMachine workspace d).start,
            retained.length,
            retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
              flattenPairs workspace ++ selectedTail (first :: more)⟩ =
        ⟨s,
          (retained ++ flattenPairs workspace ++
              List.replicate (2 * (d + 2)) false).length + 2 +
            (selectedTail (first :: more)).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput (first :: more).length 0 (first :: more)⟩ ∧
      (runtimeMarkedCompactArchiveUnaryMachine workspace d).halt s = true := by
  let phys := retained ++ flattenPairs workspace ++
    List.replicate (2 * (d + 2)) false
  let T0 := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let Tseed := phys ++ [false, true] ++ selectedTail (first :: more)
  obtain ⟨sc, hc, hcHalt⟩ := runtimeMarkedCompactArchive_run
    retained workspace first more d
  have hphysHead : phys.length + 2 =
      retained.length + 2 * workspace.length + 2 * (d + 3) := by
    simp [phys, flattenPairs_length]
    omega
  have hc' : run (runtimeMarkedCompactArchiveMachine workspace d)
      (runtimeMarkedCompactArchiveClock workspace d (first :: more))
      ⟨(runtimeMarkedCompactArchiveMachine workspace d).start,
        retained.length, T0⟩ =
    ⟨sc, phys.length + 2, Tseed⟩ := by
    rw [hphysHead]
    simpa [phys, T0, Tseed, flattenPairs_length,
      List.append_assoc] using hc
  obtain ⟨base, unaryClock, hbase, hbaseLen, hu⟩ :=
    runtimeUnaryRebase_run_physical_prefix phys first more hfit
  have hjoin := headSeq_run_at
    (runtimeMarkedCompactArchiveMachine workspace d)
    runtimeUnaryRebaseMachine T0 Tseed
    (base ++ [false, true, false, true] ++
      sourceSelectorInput (first :: more).length 0 (first :: more))
    retained.length
    (runtimeMarkedCompactArchiveClock workspace d (first :: more))
    unaryClock (phys.length + 2)
    (phys.length + 2 + (selectedTail (first :: more)).length)
    sc RuntimeUnaryRebaseState.done hc' hcHalt hu rfl
  refine ⟨base, unaryClock, Sum.inr RuntimeUnaryRebaseState.done,
    hbase, ?_, ?_⟩
  · simpa [runtimeMarkedCompactArchiveUnaryMachine, T0, phys,
      Nat.add_assoc] using hjoin
  · rfl

#print axioms exactClockMachine_run_of_run
#print axioms runtimeCompactAllPasses_machine_run
#print axioms runtimeCompactArchiveTail_run
#print axioms runtimeMarkedCompactArchive_run
#print axioms runtimeMarkedCompactArchiveUnary_run

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition
