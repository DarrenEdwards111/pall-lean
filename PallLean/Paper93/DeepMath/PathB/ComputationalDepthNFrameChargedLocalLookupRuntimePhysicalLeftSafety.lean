import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeContinuationDispatch

/-!
# Physical runtime locator left safety

The physical archive controller begins with three structural parsers.  This
file certifies their actual head-preserving composition.  The proofs are
independent of semantic offsets: the two forward parsers never move left,
while each one-cell backup state is shown to have been entered only after a
right move.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter

/-- The output-capacity parser has no left-moving transition. -/
theorem outputSourceLocator_leftSafe (T : List Bool) (n : Nat) :
    LeftSafeRun outputSourceLocatorMachine
      (init outputSourceLocatorMachine T) n := by
  intro i hi hlive hmove
  generalize hc : run outputSourceLocatorMachine i
    (init outputSourceLocatorMachine T) = c at hlive hmove ⊢
  rcases c with ⟨s, p, tp⟩
  cases s <;>
    simp [outputSourceLocatorMachine] at hmove <;>
    split_ifs at hmove <;> simp_all

/-- The workspace parser's only left-moving state is reachable only at a
strictly positive head. -/
def RuntimeWorkspaceSafeInv
    (c : Cfg runtimeWorkspaceLocatorMachine) : Prop :=
  c.st = RuntimeWorkspaceLocatorState.blockHi → 0 < c.hd

theorem runtimeWorkspaceSafeInv_step
    (c : Cfg runtimeWorkspaceLocatorMachine)
    (h : RuntimeWorkspaceSafeInv c) :
    RuntimeWorkspaceSafeInv (step runtimeWorkspaceLocatorMachine c) := by
  intro hb
  by_cases hh : runtimeWorkspaceLocatorMachine.halt c.st = true
  · rw [step_of_halted _ hh] at hb ⊢
    exact h hb
  · have hh' : runtimeWorkspaceLocatorMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false] at hb ⊢
    cases hs : c.st <;>
      simp [runtimeWorkspaceLocatorMachine, moveHead, hs] at hb ⊢ <;>
      split_ifs at hb <;> simp_all [RuntimeWorkspaceSafeInv]

theorem runtimeWorkspaceSafeInv_run
    (c : Cfg runtimeWorkspaceLocatorMachine)
    (h : RuntimeWorkspaceSafeInv c) (n : Nat) :
    RuntimeWorkspaceSafeInv (run runtimeWorkspaceLocatorMachine n c) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [run_succ]
      exact runtimeWorkspaceSafeInv_step _ ih

/-- Workspace discovery is left safe from every physical starting head. -/
theorem runtimeWorkspaceLocator_leftSafe
    (T : List Bool) (p n : Nat) :
    LeftSafeRun runtimeWorkspaceLocatorMachine
      ⟨RuntimeWorkspaceLocatorState.countLo, p, T⟩ n := by
  intro i hi hlive hmove
  have hinv := runtimeWorkspaceSafeInv_run
    (⟨RuntimeWorkspaceLocatorState.countLo, p, T⟩ :
      Cfg runtimeWorkspaceLocatorMachine) (by
        simp [RuntimeWorkspaceSafeInv]) i
  generalize hc : run runtimeWorkspaceLocatorMachine i
    ⟨RuntimeWorkspaceLocatorState.countLo, p, T⟩ = c at hinv
  rw [hc] at hlive hmove
  rcases c with ⟨s, q, tp⟩
  cases s <;>
    simp [runtimeWorkspaceLocatorMachine] at hmove <;>
    split_ifs at hmove <;> simp_all [RuntimeWorkspaceSafeInv]

/-- Exact composed safety for the output-origin to workspace-origin parser. -/
theorem outputWorkspaceLocator_leftSafe
    (T phys workspace : List Bool) (d : Nat)
    (preBlocks : List (List Bool)) (clock1 : Nat)
    (hT : T = phys ++ selectedPrefix d preBlocks ++ workspace)
    (hsource : run outputSourceLocatorMachine clock1
        (init outputSourceLocatorMachine T) =
      ⟨OutputSourceLocatorState.done, phys.length, T⟩)
    (h0 : workspace.getD 0 false = true)
    (h1 : workspace.getD 1 false = false) :
    LeftSafeRun outputWorkspaceLocatorMachine
      (init outputWorkspaceLocatorMachine T)
      (clock1 + 1 + ((selectedPrefix d preBlocks).length + 2)) := by
  have hwork : run runtimeWorkspaceLocatorMachine
      ((selectedPrefix d preBlocks).length + 2)
      ⟨RuntimeWorkspaceLocatorState.countLo, phys.length, T⟩ =
      ⟨RuntimeWorkspaceLocatorState.done,
        phys.length + (selectedPrefix d preBlocks).length, T⟩ := by
    rw [hT]
    simpa using runtimeWorkspaceLocator_run_prefixed phys d preBlocks workspace
      h0 h1
  exact headSeq_leftSafe outputSourceLocatorMachine
    runtimeWorkspaceLocatorMachine T T clock1
    ((selectedPrefix d preBlocks).length + 2) phys.length
    OutputSourceLocatorState.done hsource (by
      simp [outputSourceLocatorMachine])
    (outputSourceLocator_leftSafe T clock1)
    (by simpa [runtimeWorkspaceLocatorMachine] using
      (runtimeWorkspaceLocator_leftSafe T phys.length
        ((selectedPrefix d preBlocks).length + 2))) (by
        change runtimeWorkspaceLocatorMachine.halt
          (run runtimeWorkspaceLocatorMachine
            ((selectedPrefix d preBlocks).length + 2)
            ⟨RuntimeWorkspaceLocatorState.countLo, phys.length, T⟩).st = true
        rw [hwork]
        simp [runtimeWorkspaceLocatorMachine])

/-- The completed-workspace tail parser's sole backup state is likewise
strictly right of physical origin. -/
def RuntimeWorkspaceTailSafeInv
    (c : Cfg runtimeWorkspaceTailLocatorMachine) : Prop :=
  (∀ b, c.st = RuntimeWorkspaceTailLocatorState.paddingHi b → 0 < c.hd)

theorem runtimeWorkspaceTailSafeInv_step
    (c : Cfg runtimeWorkspaceTailLocatorMachine)
    (h : RuntimeWorkspaceTailSafeInv c) :
    RuntimeWorkspaceTailSafeInv (step runtimeWorkspaceTailLocatorMachine c) := by
  intro b hb
  by_cases hh : runtimeWorkspaceTailLocatorMachine.halt c.st = true
  · rw [step_of_halted _ hh] at hb ⊢
    exact h b hb
  · have hh' : runtimeWorkspaceTailLocatorMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false] at hb ⊢
    cases hs : c.st <;>
      simp [runtimeWorkspaceTailLocatorMachine, moveHead, hs] at hb ⊢ <;>
      split_ifs at hb <;> simp_all [RuntimeWorkspaceTailSafeInv]

theorem runtimeWorkspaceTailSafeInv_run
    (c : Cfg runtimeWorkspaceTailLocatorMachine)
    (h : RuntimeWorkspaceTailSafeInv c) (n : Nat) :
    RuntimeWorkspaceTailSafeInv (run runtimeWorkspaceTailLocatorMachine n c) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [run_succ]
      exact runtimeWorkspaceTailSafeInv_step _ ih

/-- Tail discovery is left safe from every physical starting head. -/
theorem runtimeWorkspaceTailLocator_leftSafe
    (T : List Bool) (p n : Nat) :
    LeftSafeRun runtimeWorkspaceTailLocatorMachine
      ⟨RuntimeWorkspaceTailLocatorState.boot0, p, T⟩ n := by
  intro i hi hlive hmove
  have hinv := runtimeWorkspaceTailSafeInv_run
    (⟨RuntimeWorkspaceTailLocatorState.boot0, p, T⟩ :
      Cfg runtimeWorkspaceTailLocatorMachine) (by
        simp [RuntimeWorkspaceTailSafeInv]) i
  generalize hc : run runtimeWorkspaceTailLocatorMachine i
    ⟨RuntimeWorkspaceTailLocatorState.boot0, p, T⟩ = c at hinv
  rw [hc] at hlive hmove
  rcases c with ⟨s, q, tp⟩
  cases s <;>
    simp [runtimeWorkspaceTailLocatorMachine] at hmove <;>
    split_ifs at hmove <;> simp_all [RuntimeWorkspaceTailSafeInv]

/-- Generic safety compositor for the actual workspace/tail locator chain. -/
theorem outputWorkspaceTailLocator_leftSafe
    (T : List Bool) (workspaceClock tailClock workspaceHead tailHead : Nat)
    (hworkspace : run outputWorkspaceLocatorMachine workspaceClock
        (init outputWorkspaceLocatorMachine T) =
      ⟨Sum.inr RuntimeWorkspaceLocatorState.done, workspaceHead, T⟩)
    (hsafeWorkspace : LeftSafeRun outputWorkspaceLocatorMachine
      (init outputWorkspaceLocatorMachine T) workspaceClock)
    (htail : run runtimeWorkspaceTailLocatorMachine tailClock
        ⟨RuntimeWorkspaceTailLocatorState.boot0, workspaceHead, T⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done, tailHead, T⟩) :
    LeftSafeRun outputWorkspaceTailLocatorMachine
      (init outputWorkspaceTailLocatorMachine T)
      (workspaceClock + 1 + tailClock) := by
  exact headSeq_leftSafe outputWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine T T workspaceClock tailClock
    workspaceHead (Sum.inr RuntimeWorkspaceLocatorState.done)
    hworkspace (by simp [outputWorkspaceLocatorMachine, headSeqMachine,
      runtimeWorkspaceLocatorMachine]) hsafeWorkspace
    (by simpa [runtimeWorkspaceTailLocatorMachine] using
      runtimeWorkspaceTailLocator_leftSafe T workspaceHead tailClock) (by
      simpa [runtimeWorkspaceTailLocatorMachine] using congrArg
        (fun c => runtimeWorkspaceTailLocatorMachine.halt c.st) htail
      )

/-! ## Archive discovery and reverse return -/

/-- The forward archive parser has no left-moving transition. -/
theorem runtimeArchiveLocator_leftSafe
    (T : List Bool) (p n : Nat) :
    LeftSafeRun runtimeArchiveLocatorMachine
      ⟨RuntimeArchiveLocatorState.headerLo, p, T⟩ n := by
  intro i hi hlive hmove
  generalize hc : run runtimeArchiveLocatorMachine i
    ⟨RuntimeArchiveLocatorState.headerLo, p, T⟩ = c
  rw [hc] at hlive hmove
  rcases c with ⟨s, q, tp⟩
  cases s <;>
    simp [runtimeArchiveLocatorMachine] at hmove <;>
    split_ifs at hmove <;> simp_all

/-- Every live reverse-parser step decreases its head by at most one. -/
theorem moveHead_lower_of_ne_reset (p : Nat) (m : Move) (hm : m ≠ 3) :
    p ≤ moveHead p m + 1 := by
  fin_cases m <;> simp [moveHead] at hm ⊢ <;> omega

theorem runtimeArchiveReverse_step_head_lower
    (c : Cfg runtimeArchiveReverseMachine) :
    c.hd ≤ (step runtimeArchiveReverseMachine c).hd + 1 := by
  by_cases hh : runtimeArchiveReverseMachine.halt c.st = true
  · rw [step_of_halted _ hh]
    omega
  · have hh' : runtimeArchiveReverseMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false]
    apply moveHead_lower_of_ne_reset
    cases c.st <;>
      simp [runtimeArchiveReverseMachine] <;>
      split_ifs <;> simp

/-- After `i` reverse-parser steps, the initial head is at most the current
head plus `i`.  This remains true if malformed input halts early. -/
theorem runtimeArchiveReverse_run_head_lower
    (c : Cfg runtimeArchiveReverseMachine) (i : Nat) :
    c.hd ≤ (run runtimeArchiveReverseMachine i c).hd + i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [run_succ]
      have hs := runtimeArchiveReverse_step_head_lower
        (run runtimeArchiveReverseMachine i c)
      omega

/-- A reverse run whose clock does not exceed its starting head is physically
left safe, independently of the inspected tape symbols. -/
theorem runtimeArchiveReverse_leftSafe
    (T : List Bool) (E n : Nat) (hn : n ≤ E) :
    LeftSafeRun runtimeArchiveReverseMachine
      ⟨RuntimeArchiveReverseState.boot0, E, T⟩ n := by
  intro i hi hlive hmove
  have hlower := runtimeArchiveReverse_run_head_lower
    (⟨RuntimeArchiveReverseState.boot0, E, T⟩ :
      Cfg runtimeArchiveReverseMachine) i
  change E ≤ (run runtimeArchiveReverseMachine i
    ⟨RuntimeArchiveReverseState.boot0, E, T⟩).hd + i at hlower
  omega

/-- The exact nonempty canonical archive return satisfies that clock budget
as soon as the physical archive origin is at least four cells from zero. -/
theorem runtimeArchiveReverse_canonical_leftSafe
    (pre tail : List Bool) (first : List Bool) (more : List (List Bool))
    (hR : 4 ≤ pre.length + 2) :
    let rest := first :: more
    let T := pre ++ [true, true] ++ selectedTail rest ++ tail
    let R := pre.length + 2
    LeftSafeRun runtimeArchiveReverseMachine
      ⟨RuntimeArchiveReverseState.boot0,
        R + (selectedTail rest).length + 2, T⟩
      (runtimeArchiveReverseClock rest) := by
  dsimp only
  apply runtimeArchiveReverse_leftSafe
  unfold runtimeArchiveReverseClock
  omega

/-- The temporary `11` boundary writer's two backups are safe at every
runtime archive origin. -/
theorem runtimeRebaseMark_leftSafe
    (T : List Bool) (R : Nat) (hR : 2 ≤ R) :
    LeftSafeRun runtimeRebaseMarkMachine
      ⟨RuntimeRebaseSeedState.back1, R, T⟩ 4 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeRebaseMarkMachine, moveHead] at hlive hmove ⊢ <;>
    omega

/-- The final `01` boundary writer has the identical safe head walk. -/
theorem runtimeRebaseSeed_leftSafe
    (T : List Bool) (R : Nat) (hR : 2 ≤ R) :
    LeftSafeRun runtimeRebaseSeedMachine
      ⟨RuntimeRebaseSeedState.back1, R, T⟩ 4 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeRebaseSeedMachine, moveHead] at hlive hmove ⊢ <;>
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.outputWorkspaceTailLocator_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReverse_canonical_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeRebaseSeed_leftSafe
