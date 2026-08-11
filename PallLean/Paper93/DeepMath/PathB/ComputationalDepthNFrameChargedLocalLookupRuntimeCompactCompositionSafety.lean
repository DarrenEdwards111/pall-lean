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



#print axioms runtimeCompactAllPasses_machine_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition

