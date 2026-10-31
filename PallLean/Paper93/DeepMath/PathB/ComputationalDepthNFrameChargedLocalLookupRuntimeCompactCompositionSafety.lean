import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalLeftSafety

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-- The complete exact-clock pass schedule preserves the left boundary. -/
theorem runtimeCompactAllPasses_machine_leftSafe
    (retained tail : List Bool) (workspace : List (Bool × Bool))
    {k : Nat} (h : RuntimeCompactAllPasses retained workspace tail k) :
    LeftSafeRun (runtimeCompactPassScheduleMachine workspace k)
      ⟨(runtimeCompactPassScheduleMachine workspace k).start,
        retained.length + 2 * (k - 1),
        retained ++ List.replicate (2 * k) false ++
          flattenPairs workspace ++ tail⟩
      (runtimeCompactPassScheduleClock workspace k) := by
  induction h with
  | one tail finalRun finalSafe =>
      simpa [runtimeCompactPassScheduleMachine,
        runtimeCompactPassScheduleClock] using
        exactClockMachine_leftSafe runtimeCompactBubbleLoopMachine
          (8 * workspace.length)
          ⟨runtimeCompactBubbleLoopMachine.start, retained.length,
            retained ++ [false, false] ++ flattenPairs workspace ++ tail⟩
          (by intro; rfl) finalSafe
  | more tail n bridge rest ih =>
      let bc := 8 * workspace.length
      let rc := 2 * (workspace.length + 1)
      let passM := exactClockMachine runtimeCompactBubbleLoopMachine bc
      let rewindM := exactClockMachine runtimeCompactRewindMachine rc
      let restM := runtimeCompactPassScheduleMachine workspace (n + 1)
      let P := retained ++ flattenPairs (List.replicate n (false, false))
      let T0 := P ++ [false, false, false, false] ++ flattenPairs workspace ++ tail
      let T1 := P ++ [false, false] ++ flattenPairs workspace ++ [false, false] ++ tail
      have hp := exactClockMachine_run_of_run runtimeCompactBubbleLoopMachine
        bc (P.length + 2) (P.length + 2 + 2 * workspace.length)
        T0 T1 runtimeCompactBubbleLoopMachine.start (by intro; rfl)
        (by simpa [P, T0, T1, List.append_assoc] using bridge.passRun)
      have hpSafe : LeftSafeRun passM ⟨passM.start, P.length + 2, T0⟩ bc := by
        simpa [passM, exactClockCfg, P, T0, List.append_assoc] using
          exactClockMachine_leftSafe runtimeCompactBubbleLoopMachine bc _
          (by intro; rfl)
          (by simpa [P, T0, List.append_assoc] using bridge.passSafe)
      have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
        rc (P.length + 2 + 2 * workspace.length) P.length T1 T1 ()
        (by intro; rfl)
        (by simpa [P, T1, List.append_assoc] using bridge.rewindRun)
      have hrSafe : LeftSafeRun rewindM
          ⟨rewindM.start, P.length + 2 + 2 * workspace.length, T1⟩ rc := by
        simpa [rewindM, exactClockCfg, P, T1, List.append_assoc] using
          exactClockMachine_leftSafe runtimeCompactRewindMachine rc _
          (by intro; rfl)
          (by simpa [P, T1, List.append_assoc] using bridge.rewindSafe)
      obtain ⟨srest, hrestRun, hrestHalt⟩ :=
        runtimeCompactAllPasses_machine_run retained
          ([false, false] ++ tail) workspace rest
      have hrestRun' : run restM
          (runtimeCompactPassScheduleClock workspace (n + 1))
          ⟨restM.start, P.length, T1⟩ =
        ⟨srest, retained.length + 2 * workspace.length,
          retained ++ flattenPairs workspace ++
            List.replicate (2 * (n + 1)) false ++ [false, false] ++ tail⟩ := by
        simpa [restM, P, T1, flattenPairs_replicate_false,
          List.replicate_add, Nat.mul_add, List.append_assoc] using hrestRun
      have hinner : LeftSafeRun (headSeqMachine rewindM restM)
          ⟨(headSeqMachine rewindM restM).start,
            P.length + 2 + 2 * workspace.length, T1⟩
          (rc + 1 + runtimeCompactPassScheduleClock workspace (n + 1)) := by
        exact headSeq_leftSafe_at rewindM restM T1 T1
          (P.length + 2 + 2 * workspace.length) rc
          (runtimeCompactPassScheduleClock workspace (n + 1)) P.length
          (⟨rc, by omega⟩, ())
          hr (exactClockMachine_halt_at _ _ _) hrSafe
          (by simpa [restM, P, T1, flattenPairs_replicate_false,
              List.replicate_add, Nat.mul_add, List.append_assoc] using ih)
          (by rw [hrestRun']; simpa [restM] using hrestHalt)
      have hall := headSeq_leftSafe_at passM (headSeqMachine rewindM restM)
        T0 T1 (P.length + 2) bc
        (rc + 1 + runtimeCompactPassScheduleClock workspace (n + 1))
        (P.length + 2 + 2 * workspace.length)
        (⟨bc, by omega⟩, runtimeCompactBubbleLoopMachine.start)
        hp (exactClockMachine_halt_at _ _ _) hpSafe hinner
        (by
          rw [headSeq_run_at rewindM restM T1 T1
            (retained ++ flattenPairs workspace ++
              List.replicate (2 * (n + 1)) false ++ [false, false] ++ tail)
            (P.length + 2 + 2 * workspace.length) rc
            (runtimeCompactPassScheduleClock workspace (n + 1)) P.length
            (retained.length + 2 * workspace.length) (⟨rc, by omega⟩, ())
            srest hr (exactClockMachine_halt_at _ _ _) hrestRun' hrestHalt]
          simpa [headSeqMachine, restM] using hrestHalt)
      simpa [runtimeCompactPassScheduleMachine,
        runtimeCompactPassScheduleClock, passM, rewindM, restM, bc, rc,
        P, T0, flattenPairs_replicate_false, List.replicate_add,
        Nat.mul_add, List.append_assoc] using hall

set_option maxHeartbeats 4000000 in
/-- The pass schedule, trailing-hole advance, and archive return are safe
whenever the compacted layout retains the two-cell reverse budget. -/
theorem runtimeCompactArchiveTail_leftSafe
    (retained : List Bool) (workspace : List (Bool × Bool))
    (first : List Bool) (more : List (List Bool))
    {k : Nat} (hk : 2 ≤ k)
    (h : RuntimeCompactAllPasses retained workspace
      (selectedTail (first :: more)) k) :
    LeftSafeRun (runtimeCompactArchiveTailMachine workspace k)
      ⟨(runtimeCompactArchiveTailMachine workspace k).start,
        retained.length + 2 * (k - 1),
        retained ++ List.replicate (2 * k) false ++
          flattenPairs workspace ++ selectedTail (first :: more)⟩
      (runtimeCompactArchiveTailClock workspace k (first :: more)) := by
  obtain ⟨spass, hpass, hpassHalt⟩ :=
    runtimeCompactAllPasses_machine_run retained
      (selectedTail (first :: more)) workspace h
  let Tcompact := retained ++ flattenPairs workspace ++
    List.replicate (2 * k) false ++ selectedTail (first :: more)
  let P := retained ++ flattenPairs workspace
  let advanceM := exactClockMachine runtimeCompactClearLoopMachine (2 * k)
  have ha0 := runtimeCompactClearLoop_run P
    (List.replicate (2 * k) false) (selectedTail (first :: more))
  have ha := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * k) (retained.length + 2 * workspace.length)
    (retained.length + 2 * workspace.length + 2 * k)
    Tcompact Tcompact () (by intro; rfl) (by
      simpa [P, Tcompact, flattenPairs_length, List.append_assoc] using ha0)
  have haSafe : LeftSafeRun advanceM
      ⟨advanceM.start, retained.length + 2 * workspace.length, Tcompact⟩
      (2 * k) := by
    have hs0 := runtimeCompactClearLoop_leftSafe P
      (List.replicate (2 * k) false) (selectedTail (first :: more))
    have hs : LeftSafeRun runtimeCompactClearLoopMachine
        ⟨runtimeCompactClearLoopMachine.start, P.length,
          P ++ List.replicate (2 * k) false ++ selectedTail (first :: more)⟩
        (2 * k) := by simpa using hs0
    simpa [advanceM, exactClockCfg, P, Tcompact, flattenPairs_length,
      List.append_assoc] using
      exactClockMachine_leftSafe runtimeCompactClearLoopMachine (2 * k) _
        (by intro; rfl) hs
  have hsplit : List.replicate (2 * k) false =
      List.replicate (2 * (k - 1)) false ++ [false, false] := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, List.replicate_add]
    simp
  let pre := retained ++ flattenPairs workspace ++
    List.replicate (2 * (k - 1)) false
  have hpre : 2 ≤ pre.length := by simp [pre, flattenPairs_length]; omega
  have har0 := runtimeArchiveReturnSeed_run_prefixed pre false false first more
  have hR : retained.length + (2 * workspace.length + 2 * (k - 1)) + 2 =
      retained.length + 2 * workspace.length + 2 * k := by omega
  have har : run runtimeArchiveReturnSeedMachine
      (runtimeArchiveReturnSeedClock (first :: more))
      ⟨runtimeArchiveReturnSeedMachine.start,
        retained.length + 2 * workspace.length + 2 * k, Tcompact⟩ =
    ⟨Sum.inr RuntimeRebaseSeedState.done,
      retained.length + 2 * workspace.length + 2 * k,
      pre ++ [false, true] ++ selectedTail (first :: more)⟩ := by
    dsimp [pre] at har0 ⊢
    rw [← hR]
    simpa [Tcompact, hsplit, flattenPairs_length,
      List.append_assoc] using har0
  have harSafe0 := runtimeArchiveReturnSeed_leftSafe_prefixed
    pre false false first more hpre
  have harSafe : LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start,
        retained.length + 2 * workspace.length + 2 * k, Tcompact⟩
      (runtimeArchiveReturnSeedClock (first :: more)) := by
    dsimp [pre] at harSafe0 ⊢
    rw [← hR]
    simpa [Tcompact, hsplit, flattenPairs_length,
      List.append_assoc] using harSafe0
  have hright := headSeq_leftSafe_at advanceM runtimeArchiveReturnSeedMachine
    Tcompact Tcompact (retained.length + 2 * workspace.length) (2 * k)
    (runtimeArchiveReturnSeedClock (first :: more))
    (retained.length + 2 * workspace.length + 2 * k)
    (⟨2 * k, by omega⟩, ()) ha (exactClockMachine_halt_at _ _ _)
    haSafe harSafe (by rw [har]; rfl)
  have hrightRun := headSeq_run_at advanceM runtimeArchiveReturnSeedMachine
    Tcompact Tcompact (pre ++ [false, true] ++ selectedTail (first :: more))
    (retained.length + 2 * workspace.length) (2 * k)
    (runtimeArchiveReturnSeedClock (first :: more))
    (retained.length + 2 * workspace.length + 2 * k)
    (retained.length + 2 * workspace.length + 2 * k)
    (⟨2 * k, by omega⟩, ()) (Sum.inr RuntimeRebaseSeedState.done)
    ha (exactClockMachine_halt_at _ _ _) har rfl
  have hall := headSeq_leftSafe_at
    (runtimeCompactPassScheduleMachine workspace k)
    (headSeqMachine advanceM runtimeArchiveReturnSeedMachine)
    (retained ++ List.replicate (2 * k) false ++
      flattenPairs workspace ++ selectedTail (first :: more)) Tcompact
    (retained.length + 2 * (k - 1))
    (runtimeCompactPassScheduleClock workspace k)
    (2 * k + 1 + runtimeArchiveReturnSeedClock (first :: more))
    (retained.length + 2 * workspace.length) spass hpass hpassHalt
    (runtimeCompactAllPasses_machine_leftSafe retained
      (selectedTail (first :: more)) workspace h)
    hright (by rw [hrightRun]; rfl)
  simpa [runtimeCompactArchiveTailMachine, runtimeCompactArchiveTailClock,
    advanceM, Tcompact, Nat.add_assoc] using hall

set_option maxHeartbeats 4000000 in
/-- The complete marked compactor through archive seed is left-safe. -/
theorem runtimeMarkedCompactArchive_leftSafe
    (retained : List Bool) (workspace : List (Bool × Bool))
    (first : List Bool) (more : List (List Bool)) (d : Nat) :
    LeftSafeRun (runtimeMarkedCompactArchiveMachine workspace d)
      ⟨(runtimeMarkedCompactArchiveMachine workspace d).start,
        retained.length,
        retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
          flattenPairs workspace ++ selectedTail (first :: more)⟩
      (runtimeMarkedCompactArchiveClock workspace d (first :: more)) := by
  let T0 := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let Tclear := retained ++ List.replicate (2 * (d + 3)) false ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let clearM := exactClockMachine runtimeCompactClearLoopMachine (2 * (d + 3))
  let rewindM := exactClockMachine runtimeCompactRewindMachine 2
  let tailM := runtimeCompactArchiveTailMachine workspace (d + 3)
  have hb := runtimeMarkedClearFirstHoleBridge_certificate retained
    (selectedTail (first :: more)) workspace d
  have hc := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * (d + 3)) retained.length (retained.length + 2 * (d + 3))
    T0 Tclear () (by intro; rfl) (by simpa [T0, Tclear] using hb.clearRun)
  have hcSafe : LeftSafeRun clearM ⟨clearM.start, retained.length, T0⟩
      (2 * (d + 3)) := by
    simpa [clearM, exactClockCfg, T0] using
      exactClockMachine_leftSafe runtimeCompactClearLoopMachine (2 * (d + 3)) _
        (by intro; rfl) hb.clearSafe
  have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
    2 (retained.length + 2 * (d + 3))
    (retained.length + 2 * (d + 2)) Tclear Tclear ()
    (by intro; rfl) (by simpa [Tclear] using hb.rewindRun)
  have hrSafe : LeftSafeRun rewindM
      ⟨rewindM.start, retained.length + 2 * (d + 3), Tclear⟩ 2 := by
    simpa [rewindM, exactClockCfg, Tclear] using
      exactClockMachine_leftSafe runtimeCompactRewindMachine 2 _
        (by intro; rfl) hb.rewindSafe
  have hsched := runtimeMarkedAllPasses_certificate retained
    (selectedTail (first :: more)) workspace d
  have htSafe : LeftSafeRun tailM
      ⟨tailM.start, retained.length + 2 * (d + 2), Tclear⟩
      (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more)) := by
    simpa [tailM, Tclear] using
      runtimeCompactArchiveTail_leftSafe retained workspace first more
        (by omega) hsched
  obtain ⟨stail, ht0, htHalt⟩ := runtimeCompactArchiveTail_run
    retained workspace first more hsched
  have ht : run tailM
      (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
      ⟨tailM.start, retained.length + 2 * (d + 2), Tclear⟩ =
    ⟨stail, retained.length + 2 * workspace.length + 2 * (d + 3),
      retained ++ flattenPairs workspace ++
        List.replicate (2 * (d + 2)) false ++ [false, true] ++
          selectedTail (first :: more)⟩ := by
    simpa [tailM, Tclear] using ht0
  have hright := headSeq_leftSafe_at rewindM tailM Tclear Tclear
    (retained.length + 2 * (d + 3)) 2
    (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
    (retained.length + 2 * (d + 2)) (⟨2, by omega⟩, ())
    hr (exactClockMachine_halt_at _ _ _) hrSafe htSafe
    (by rw [ht]; simpa [tailM] using htHalt)
  have hrightRun := headSeq_run_at rewindM tailM Tclear Tclear
    (retained ++ flattenPairs workspace ++
      List.replicate (2 * (d + 2)) false ++ [false, true] ++
        selectedTail (first :: more))
    (retained.length + 2 * (d + 3)) 2
    (runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
    (retained.length + 2 * (d + 2))
    (retained.length + 2 * workspace.length + 2 * (d + 3))
    (⟨2, by omega⟩, ()) stail hr (exactClockMachine_halt_at _ _ _)
    ht htHalt
  have hall := headSeq_leftSafe_at clearM (headSeqMachine rewindM tailM)
    T0 Tclear retained.length (2 * (d + 3))
    (2 + 1 + runtimeCompactArchiveTailClock workspace (d + 3) (first :: more))
    (retained.length + 2 * (d + 3)) (⟨2 * (d + 3), by omega⟩, ())
    hc (exactClockMachine_halt_at _ _ _) hcSafe hright
    (by rw [hrightRun]; simpa [headSeqMachine, tailM] using htHalt)
  simpa [runtimeMarkedCompactArchiveMachine,
    runtimeMarkedCompactArchiveClock, clearM, rewindM, tailM, T0, Tclear,
    Nat.add_assoc] using hall

set_option maxHeartbeats 4000000 in
/-- The marked repair through physical unary rebase has a single exact run
and a safety certificate over that same composed clock. -/
theorem runtimeMarkedCompactArchiveUnary_safeRun
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
      (runtimeMarkedCompactArchiveUnaryMachine workspace d).halt s = true ∧
      LeftSafeRun (runtimeMarkedCompactArchiveUnaryMachine workspace d)
        ⟨(runtimeMarkedCompactArchiveUnaryMachine workspace d).start,
          retained.length,
          retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
            flattenPairs workspace ++ selectedTail (first :: more)⟩
        (runtimeMarkedCompactArchiveClock workspace d (first :: more) +
          1 + unaryClock) := by
  let phys := retained ++ flattenPairs workspace ++
    List.replicate (2 * (d + 2)) false
  let T0 := retained ++ flattenPairs (runtimeMarkedStalePairs d) ++
    flattenPairs workspace ++ selectedTail (first :: more)
  let Tseed := phys ++ [false, true] ++ selectedTail (first :: more)
  obtain ⟨sc, hc0, hcHalt⟩ := runtimeMarkedCompactArchive_run
    retained workspace first more d
  have hc : run (runtimeMarkedCompactArchiveMachine workspace d)
      (runtimeMarkedCompactArchiveClock workspace d (first :: more))
      ⟨(runtimeMarkedCompactArchiveMachine workspace d).start,
        retained.length, T0⟩ =
    ⟨sc, phys.length + 2, Tseed⟩ := by
    convert hc0 using 1 <;>
      simp [phys, T0, Tseed, flattenPairs_length, List.append_assoc] <;> omega
  obtain ⟨base, unaryClock, hbase, hbaseLen, hu, huSafe⟩ :=
    runtimeUnaryRebase_physical_safeRun phys first more (by simpa [phys] using hfit)
  have hsafeCompact : LeftSafeRun
      (runtimeMarkedCompactArchiveMachine workspace d)
      ⟨(runtimeMarkedCompactArchiveMachine workspace d).start,
        retained.length, T0⟩
      (runtimeMarkedCompactArchiveClock workspace d (first :: more)) := by
    simpa [T0] using runtimeMarkedCompactArchive_leftSafe
      retained workspace first more d
  have hu' : run runtimeUnaryRebaseMachine unaryClock
      ⟨runtimeUnaryRebaseMachine.start, phys.length + 2, Tseed⟩ =
    ⟨RuntimeUnaryRebaseState.done,
      phys.length + 2 + (selectedTail (first :: more)).length,
      base ++ [false, true, false, true] ++
        sourceSelectorInput (first :: more).length 0 (first :: more)⟩ := by
    simpa [Tseed] using hu
  have hsafe := headSeq_leftSafe_at
    (runtimeMarkedCompactArchiveMachine workspace d) runtimeUnaryRebaseMachine
    T0 Tseed retained.length
    (runtimeMarkedCompactArchiveClock workspace d (first :: more)) unaryClock
    (phys.length + 2) sc hc hcHalt hsafeCompact
    (by simpa [Tseed] using huSafe) (by rw [hu']; rfl)
  have hrun := headSeq_run_at
    (runtimeMarkedCompactArchiveMachine workspace d) runtimeUnaryRebaseMachine
    T0 Tseed
    (base ++ [false, true, false, true] ++
      sourceSelectorInput (first :: more).length 0 (first :: more))
    retained.length
    (runtimeMarkedCompactArchiveClock workspace d (first :: more)) unaryClock
    (phys.length + 2)
    (phys.length + 2 + (selectedTail (first :: more)).length)
    sc RuntimeUnaryRebaseState.done hc hcHalt
    hu' rfl
  refine ⟨base, unaryClock, Sum.inr RuntimeUnaryRebaseState.done, ?_, ?_, ?_, ?_⟩
  · simpa [phys] using hbase
  · simpa [runtimeMarkedCompactArchiveUnaryMachine, T0, phys,
      Nat.add_assoc] using hrun
  · rfl
  · simpa [runtimeMarkedCompactArchiveUnaryMachine, T0, Nat.add_assoc] using hsafe



#print axioms runtimeCompactAllPasses_machine_leftSafe
#print axioms runtimeCompactArchiveTail_leftSafe
#print axioms runtimeMarkedCompactArchive_leftSafe
#print axioms runtimeMarkedCompactArchiveUnary_safeRun

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition
