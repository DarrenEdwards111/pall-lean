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
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
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
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-! ## Head-preserving safety from an already discovered head -/

theorem headSeq_leftSafe_inl_at (M1 M2 : Machine) (c : Cfg M1)
    (t : Nat) (hno : ∀ i < t, M1.halt (run M1 i c).st = false)
    (hsafe : LeftSafeRun M1 c t) :
    LeftSafeRun (headSeqMachine M1 M2) (headInlCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  have hr := headSeq_run_inl M1 M2 c i
    (fun j hj => hno j (by omega))
  rw [hr] at hhalt hmove ⊢
  have hh1 : M1.halt (run M1 i c).st = false := hno i hi
  have hm1 : (M1.δ (run M1 i c).st
      ((run M1 i c).tp.getD (run M1 i c).hd false)).2.2 = 0 := by
    simpa [headSeqMachine, headInlCfg, hh1] using hmove
  exact hsafe i hi hh1 hm1

theorem headSeq_leftSafe_handoff_at (M1 M2 : Machine) (c : Cfg M1)
    (hh : M1.halt c.st = true) :
    LeftSafeRun (headSeqMachine M1 M2) (headInlCfg M1 M2 c) 1 := by
  apply leftSafeRun_one_of_not_left
  simp [headSeqMachine, headInlCfg, hh]

theorem headSeq_leftSafe_inr_at (M1 M2 : Machine) (c : Cfg M2)
    (t : Nat) (hsafe : LeftSafeRun M2 c t) :
    LeftSafeRun (headSeqMachine M1 M2) (headInrCfg M1 M2 c) t := by
  intro i hi hhalt hmove
  rw [headSeq_run_inr M1 M2 c i] at hhalt hmove ⊢
  have hh2 : M2.halt (run M2 i c).st = false := by
    simpa [headSeqMachine, headInrCfg] using hhalt
  have hm2 : (M2.δ (run M2 i c).st
      ((run M2 i c).tp.getD (run M2 i c).hd false)).2.2 = 0 := by
    simpa [headSeqMachine, headInrCfg] using hmove
  exact hsafe i hi hh2 hm2

/-- `headSeqMachine` safety composition from an arbitrary physical head,
including least-halt slack exactly as in its execution theorem. -/
theorem headSeq_leftSafe_at (M1 M2 : Machine) (T0 T1 : List Bool)
    (p0 t1 t2 p1 : Nat) (s1 : M1.State)
    (h1 : run M1 t1 ⟨M1.start, p0, T0⟩ = ⟨s1, p1, T1⟩)
    (hh1 : M1.halt s1 = true)
    (hsafe1 : LeftSafeRun M1 ⟨M1.start, p0, T0⟩ t1)
    (hsafe2 : LeftSafeRun M2 ⟨M2.start, p1, T1⟩ t2)
    (hh2 : M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st = true) :
    LeftSafeRun (headSeqMachine M1 M2)
      ⟨(headSeqMachine M1 M2).start, p0, T0⟩ (t1 + 1 + t2) := by
  let c0 : Cfg M1 := ⟨M1.start, p0, T0⟩
  have hex : ∃ t, M1.halt (run M1 t c0).st = true :=
    ⟨t1, by rw [h1]; exact hh1⟩
  let tm := Nat.find hex
  have htm : M1.halt (run M1 tm c0).st = true := Nat.find_spec hex
  have htmle : tm ≤ t1 := Nat.find_le (by rw [h1]; exact hh1)
  have hfrozen : run M1 tm c0 = ⟨s1, p1, T1⟩ := by
    rw [← run_stable_cfg M1 c0 htmle htm, h1]
  have hno : ∀ i < tm, M1.halt (run M1 i c0).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hs1 : LeftSafeRun (headSeqMachine M1 M2)
      ⟨(headSeqMachine M1 M2).start, p0, T0⟩ tm := by
    change LeftSafeRun (headSeqMachine M1 M2) (headInlCfg M1 M2 c0) tm
    exact headSeq_leftSafe_inl_at M1 M2 c0 tm hno
      (fun i hi => hsafe1 i (by omega))
  have hrun1 : run (headSeqMachine M1 M2) tm
      ⟨(headSeqMachine M1 M2).start, p0, T0⟩ =
      headInlCfg M1 M2 (⟨s1, p1, T1⟩ : Cfg M1) := by
    change run (headSeqMachine M1 M2) tm (headInlCfg M1 M2 c0) = _
    rw [headSeq_run_inl M1 M2 _ tm hno, hfrozen]
  have hsSwitch : LeftSafeRun (headSeqMachine M1 M2)
      (run (headSeqMachine M1 M2) tm
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩) 1 := by
    rw [hrun1]
    exact headSeq_leftSafe_handoff_at M1 M2 _ hh1
  have hafter : run (headSeqMachine M1 M2) 1
      (run (headSeqMachine M1 M2) tm
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩) =
      headInrCfg M1 M2 ⟨M2.start, p1, T1⟩ := by
    rw [hrun1, run_succ, run_zero]
    exact headSeq_step_handoff M1 M2 _ hh1
  have hs2 : LeftSafeRun (headSeqMachine M1 M2)
      (run (headSeqMachine M1 M2) (tm + 1)
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩) t2 := by
    rw [run_add, hafter]
    exact headSeq_leftSafe_inr_at M1 M2 _ t2 hsafe2
  have hsMain : LeftSafeRun (headSeqMachine M1 M2)
      ⟨(headSeqMachine M1 M2).start, p0, T0⟩ (tm + 1 + t2) :=
    leftSafeRun_add (leftSafeRun_add hs1 hsSwitch) hs2
  have hhaltAt : (headSeqMachine M1 M2).halt
      (run (headSeqMachine M1 M2) (tm + 1 + t2)
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩).st =
      M2.halt (run M2 t2 ⟨M2.start, p1, T1⟩).st := by
    rw [show tm + 1 + t2 = (tm + 1) + t2 by omega, run_add]
    rw [run_add, hafter, headSeq_run_inr]
    rfl
  have hsSlack : LeftSafeRun (headSeqMachine M1 M2)
      (run (headSeqMachine M1 M2) (tm + 1 + t2)
        ⟨(headSeqMachine M1 M2).start, p0, T0⟩) (t1 - tm) :=
    leftSafeRun_of_halted _ (by rw [hhaltAt, hh2])
  have hsAll := leftSafeRun_add hsMain hsSlack
  convert hsAll using 1 <;> omega

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

/-- Phase-exact safety of marker installation, forward archive discovery,
reverse return, and final seed installation as their real nested controller.
The reverse clock premise is purely physical and is discharged by the
reachable archive geometry. -/
theorem runtimeArchiveReturnSeed_leftSafe_of_runs
    (T0 Tm T1 : List Bool) (R E locatorClock reverseClock : Nat)
    (hR : 2 ≤ R)
    (hm : run runtimeRebaseMarkMachine 4
      ⟨runtimeRebaseMarkMachine.start, R, T0⟩ =
      ⟨RuntimeRebaseSeedState.done, R, Tm⟩)
    (hf : run runtimeArchiveLocatorMachine locatorClock
      ⟨runtimeArchiveLocatorMachine.start, R, Tm⟩ =
      ⟨RuntimeArchiveLocatorState.done, E, Tm⟩)
    (hr : run runtimeArchiveReverseMachine reverseClock
      ⟨runtimeArchiveReverseMachine.start, E, Tm⟩ =
      ⟨RuntimeArchiveReverseState.done, R, Tm⟩)
    (hbudget : reverseClock ≤ E)
    (hs : run runtimeRebaseSeedMachine 4
      ⟨runtimeRebaseSeedMachine.start, R, Tm⟩ =
      ⟨RuntimeRebaseSeedState.done, R, T1⟩) :
    LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, T0⟩
      (4 + 1 + locatorClock + 1 + reverseClock + 1 + 4) := by
  have hsafeMarkLocate : LeftSafeRun runtimeArchiveMarkLocateMachine
      ⟨runtimeArchiveMarkLocateMachine.start, R, T0⟩
      (4 + 1 + locatorClock) := by
    simpa [runtimeArchiveMarkLocateMachine] using
      headSeq_leftSafe_at runtimeRebaseMarkMachine runtimeArchiveLocatorMachine
        T0 Tm R 4 locatorClock R RuntimeRebaseSeedState.done hm rfl
        (by simpa [runtimeRebaseMarkMachine] using
          runtimeRebaseMark_leftSafe T0 R hR)
        (by simpa [runtimeArchiveLocatorMachine] using
          runtimeArchiveLocator_leftSafe Tm R locatorClock)
        (by rw [hf]; simp [runtimeArchiveLocatorMachine])
  have hmf := headSeq_run_at runtimeRebaseMarkMachine
    runtimeArchiveLocatorMachine T0 Tm Tm R 4 locatorClock R E
    RuntimeRebaseSeedState.done RuntimeArchiveLocatorState.done
    hm rfl hf rfl
  have hsafeMarkLocateReturn :
      LeftSafeRun runtimeArchiveMarkLocateReturnMachine
        ⟨runtimeArchiveMarkLocateReturnMachine.start, R, T0⟩
        (4 + 1 + locatorClock + 1 + reverseClock) := by
    simpa [runtimeArchiveMarkLocateReturnMachine] using
      headSeq_leftSafe_at runtimeArchiveMarkLocateMachine
        runtimeArchiveReverseMachine T0 Tm R
        (4 + 1 + locatorClock) reverseClock E
        (Sum.inr RuntimeArchiveLocatorState.done)
        (by simpa [runtimeArchiveMarkLocateMachine] using hmf) rfl
        (by simpa [runtimeArchiveMarkLocateMachine] using hsafeMarkLocate)
        (by simpa [runtimeArchiveReverseMachine] using
          runtimeArchiveReverse_leftSafe Tm E reverseClock hbudget)
        (by rw [hr]; simp [runtimeArchiveReverseMachine])
  have hmfr := headSeq_run_at runtimeArchiveMarkLocateMachine
    runtimeArchiveReverseMachine T0 Tm Tm R
    (4 + 1 + locatorClock) reverseClock E R
    (Sum.inr RuntimeArchiveLocatorState.done)
    RuntimeArchiveReverseState.done
    (by simpa [runtimeArchiveMarkLocateMachine] using hmf) rfl hr rfl
  simpa [runtimeArchiveReturnSeedMachine, Nat.add_assoc] using
    headSeq_leftSafe_at runtimeArchiveMarkLocateReturnMachine
      runtimeRebaseSeedMachine T0 Tm R
      (4 + 1 + locatorClock + 1 + reverseClock) 4 R
      (Sum.inr RuntimeArchiveReverseState.done)
      (by simpa [runtimeArchiveMarkLocateReturnMachine] using hmfr) rfl
      (by simpa [runtimeArchiveMarkLocateReturnMachine] using
        hsafeMarkLocateReturn)
      (by simpa [runtimeRebaseSeedMachine] using
        runtimeRebaseSeed_leftSafe Tm R hR)
      (by rw [hs]; simp [runtimeRebaseSeedMachine])

/-- Canonical specialization for a nonempty archive behind a physical prefix.
Two prefix cells suffice to discharge the reverse clock budget. -/
theorem runtimeArchiveReturnSeed_leftSafe_prefixed
    (pre : List Bool) (a b : Bool) (first : List Bool)
    (more : List (List Bool)) (hpre : 2 ≤ pre.length) :
    let rest := first :: more
    let T0 := pre ++ [a, b] ++ selectedTail rest
    let R := pre.length + 2
    LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, T0⟩
      (runtimeArchiveReturnSeedClock rest) := by
  dsimp only
  let rest := first :: more
  let T0 := pre ++ [a, b] ++ selectedTail rest
  let Tm := pre ++ [true, true] ++ selectedTail rest
  let T1 := pre ++ [false, true] ++ selectedTail rest
  let R := pre.length + 2
  let E := R + (selectedTail rest).length + 2
  have hm0 := runtimeRebaseMark_run T0 R (by simp [R])
  have hm : run runtimeRebaseMarkMachine 4
      ⟨runtimeRebaseMarkMachine.start, R, T0⟩ =
      ⟨RuntimeRebaseSeedState.done, R, Tm⟩ := by
    dsimp [T0, Tm, R, runtimeRebaseMarkMachine] at hm0 ⊢
    rw [markArchiveBoundary_prefixed] at hm0
    exact hm0
  have hf0 := runtimeArchiveLocator_run_prefixed
    (pre ++ [true, true]) rest
  have hf : run runtimeArchiveLocatorMachine
      (runtimeArchiveLocatorClock rest)
      ⟨runtimeArchiveLocatorMachine.start, R, Tm⟩ =
      ⟨RuntimeArchiveLocatorState.done, E, Tm⟩ := by
    simpa [Tm, R, E, List.append_assoc] using hf0
  have hr0 := runtimeArchiveReverse_run_markedPrefixed pre [] first more
  have hr : run runtimeArchiveReverseMachine
      (runtimeArchiveReverseClock rest)
      ⟨runtimeArchiveReverseMachine.start, E, Tm⟩ =
      ⟨RuntimeArchiveReverseState.done, R, Tm⟩ := by
    simpa [rest, Tm, R, E, List.append_assoc] using hr0
  have hs0 := runtimeRebaseSeed_run Tm R (by simp [R])
  have hs : run runtimeRebaseSeedMachine 4
      ⟨runtimeRebaseSeedMachine.start, R, Tm⟩ =
      ⟨RuntimeRebaseSeedState.done, R, T1⟩ := by
    dsimp [Tm, T1, R, runtimeRebaseSeedMachine] at hs0 ⊢
    rw [seedRebaseBoundary_prefixed] at hs0
    exact hs0
  have hsafe := runtimeArchiveReturnSeed_leftSafe_of_runs
    T0 Tm T1 R E (runtimeArchiveLocatorClock rest)
    (runtimeArchiveReverseClock rest) (by simp [R]) hm hf hr
    (by unfold runtimeArchiveReverseClock; simp [E, R]; omega) hs
  dsimp [rest, T0, R] at hsafe ⊢
  simpa [runtimeArchiveReturnSeedClock, Nat.add_assoc] using hsafe

/-! ## Unary writer boundary phases -/

/-- Every unary-writer step loses at most one physical head cell.  The
controller has no reset transition, so the statement also covers rejection
and already-halted configurations. -/
theorem runtimeUnaryRebase_step_head_lower
    (c : Cfg runtimeUnaryRebaseMachine) :
    c.hd ≤ (step runtimeUnaryRebaseMachine c).hd + 1 := by
  by_cases hh : runtimeUnaryRebaseMachine.halt c.st = true
  · rw [step_of_halted _ hh]
    omega
  · have hh' : runtimeUnaryRebaseMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false]
    apply moveHead_lower_of_ne_reset
    cases c.st <;>
      simp [runtimeUnaryRebaseMachine] <;>
      split_ifs <;> simp

theorem runtimeUnaryRebase_run_head_lower
    (c : Cfg runtimeUnaryRebaseMachine) (i : Nat) :
    c.hd ≤ (run runtimeUnaryRebaseMachine i c).hd + i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [run_succ]
      have hs := runtimeUnaryRebase_step_head_lower
        (run runtimeUnaryRebaseMachine i c)
      omega

/-- A unary-writer phase whose clock does not exceed its entry head is
automatically safe, irrespective of the tape it inspects. -/
theorem runtimeUnaryRebase_leftSafe_of_clock
    (s : RuntimeUnaryRebaseState) (T : List Bool) (p n : Nat)
    (hn : n ≤ p) :
    LeftSafeRun runtimeUnaryRebaseMachine ⟨s, p, T⟩ n := by
  intro i hi hlive hmove
  have hlower := runtimeUnaryRebase_run_head_lower
    (⟨s, p, T⟩ : Cfg runtimeUnaryRebaseMachine) i
  change p ≤ (run runtimeUnaryRebaseMachine i
    ⟨s, p, T⟩).hd + i at hlower
  omega

/-- A doubled marked region can be traversed backwards without reaching
physical origin. -/
theorem runtimeUnaryRebase_revPairs_leftSafe
    (T : List Bool) (H n : Nat) (last : Bool) (hH : 1 ≤ H) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.revHi last, H + 2 * n - 1, T⟩
      (2 * n) := by
  apply runtimeUnaryRebase_leftSafe_of_clock
  omega

/-- The unary tally traverses its doubled `11` region under the same exact
head budget as the marked-body reverse walk. -/
theorem runtimeUnaryRebase_tallyPairs_leftSafe
    (T : List Bool) (H n : Nat) (last : Bool) (hH : 1 ≤ H) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi last, H + 2 * n - 1, T⟩
      (2 * n) := by
  apply runtimeUnaryRebase_leftSafe_of_clock
  omega

/-- The eight-step inter-block turn stays within its concrete marked
separator. -/
theorem runtimeUnaryRebase_boundaryInter_leftSafe
    (pre tail : List Bool) (last : Bool) (hpre : 4 ≤ pre.length) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.revHi last, pre.length + 1,
        pre ++ [false, true, true, true] ++ tail⟩ 8 := by
  have h0 : (pre ++ [false, true, true, true] ++ tail).getD
      pre.length false = false := by simp
  have h1 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 1) false = true := by simp
  have h2 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 2) false = true := by simp
  have h3 : (pre ++ [false, true, true, true] ++ tail).getD
      (pre.length + 3) false = true := by simp
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt,
      h0, h1, h2, h3, Nat.add_assoc]
      at hlive hmove ⊢ <;>
    omega

/-- The eight-step origin turn reaches the tally without crossing the
physical prefix. -/
theorem runtimeUnaryRebase_boundaryOrigin_leftSafe
    (pre tail : List Bool) (last : Bool) (hpre : 4 ≤ pre.length) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.revHi last, pre.length + 1,
        pre ++ [false, true, false, false] ++ tail⟩ 8 := by
  have h0 : (pre ++ [false, true, false, false] ++ tail).getD
      pre.length false = false := by simp
  have h1 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 1) false = true := by simp
  have h2 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 2) false = false := by simp
  have h3 : (pre ++ [false, true, false, false] ++ tail).getD
      (pre.length + 3) false = false := by simp
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt,
      h0, h1, h2, h3, Nat.add_assoc]
      at hlive hmove ⊢ <;>
    omega

/-- The nonfinal four-step frontier write uses three predecessor cells and
never attempts a fourth backup. -/
theorem runtimeUnaryRebase_frontierWrite_leftSafe
    (pre tail : List Bool) (a b : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi false, pre.length + 3,
        pre ++ [a, b, false, true] ++ tail⟩ 4 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]
      at hlive hmove ⊢ <;> omega

/-- The final frontier write consumes the additional reserved marker pair,
but every live backup still occurs at a positive head. -/
theorem runtimeUnaryRebase_finalFrontierWrite_leftSafe
    (pre tail : List Bool) (c d a b : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true, pre.length + 5,
        pre ++ [c, d, a, b, false, true] ++ tail⟩ 8 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]
      at hlive hmove ⊢ <;> omega

/-- Returning across a concrete run of true cells only moves right. -/
theorem runtimeUnaryRebase_returnTrueCells_leftSafe
    (pre tail : List Bool) (n : Nat) (last : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight last, pre.length,
        pre ++ List.replicate n true ++ tail⟩ n := by
  induction n generalizing pre with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by omega]
      apply leftSafeRun_add (a := 1) (b := n)
      · apply leftSafeRun_one_of_not_left
        simp [runtimeUnaryRebaseMachine]
      · have hstep : run runtimeUnaryRebaseMachine 1
            ⟨RuntimeUnaryRebaseState.returnRight last, pre.length,
              pre ++ true :: List.replicate n true ++ tail⟩ =
            ⟨RuntimeUnaryRebaseState.returnRight last, pre.length + 1,
              pre ++ true :: List.replicate n true ++ tail⟩ := by
          simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]
        rw [hstep]
        simpa [List.append_assoc, Nat.add_assoc] using ih (pre ++ [true])

/-- Crossing the concrete `01` seed pair uses two right moves. -/
theorem runtimeUnaryRebase_returnSeed_leftSafe
    (pre archive : List Bool) (last : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight last, pre.length,
        pre ++ [false, true] ++ archive⟩ 2 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]
      at hlive hmove ⊢

/-- The complete nonfinal tally/write/right-return phase is left-safe on the
exact unary frontier produced by a visit. -/
theorem runtimeUnaryRebase_extendFrontier_leftSafe
    (pre archive : List Bool) (a b : Bool) (k : Nat) :
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++ archive
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi false,
        pre.length + 2 * k + 3, T0⟩ (4 * k + 9) := by
  dsimp only
  let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++ archive
  let Tmid := pre ++ [false, true, true, true] ++
    List.replicate (2 * k) true ++ [false, true] ++ archive
  have ht := runtimeUnaryRebase_run_tallyTruePairs T0
    (pre.length + 4) k false (by omega) (by
      intro i hi
      have h := prefixed_replicate_true
        (pre ++ [a, b, false, true]) ([false, true] ++ archive)
        (2 * k) i hi
      simpa [T0, unaryRebaseFrontier, List.append_assoc] using h)
  have ht' : run runtimeUnaryRebaseMachine (2 * k)
      ⟨RuntimeUnaryRebaseState.tallyHi false,
        pre.length + 2 * k + 3, T0⟩ =
      ⟨RuntimeUnaryRebaseState.tallyHi false, pre.length + 3, T0⟩ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
  have hsTally : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi false,
        pre.length + 2 * k + 3, T0⟩ (2 * k) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      runtimeUnaryRebase_tallyPairs_leftSafe
        T0 (pre.length + 4) k false (by omega)
  have hw := runtimeUnaryRebase_run_frontierWrite pre
    (List.replicate (2 * k) true ++ [false, true] ++ archive) a b
  have hw' : run runtimeUnaryRebaseMachine 4
      ⟨RuntimeUnaryRebaseState.tallyHi false, pre.length + 3, T0⟩ =
      ⟨RuntimeUnaryRebaseState.returnRight false,
        pre.length + 1, Tmid⟩ := by
    simpa [T0, Tmid, unaryRebaseFrontier, List.append_assoc] using hw
  have hsWrite : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi false, pre.length + 3, T0⟩ 4 := by
    simpa [T0, unaryRebaseFrontier, List.append_assoc] using
      runtimeUnaryRebase_frontierWrite_leftSafe pre
        (List.replicate (2 * k) true ++ [false, true] ++ archive) a b
  let P := pre ++ [false]
  have hTmid : Tmid =
      P ++ List.replicate (2 * k + 3) true ++ [false, true] ++ archive := by
    rw [show 2 * k + 3 = 3 + 2 * k by omega, List.replicate_add]
    simp [P, Tmid, List.append_assoc]
  have hr := runtimeUnaryRebase_run_returnTrueCells P
    ([false, true] ++ archive) (2 * k + 3) false
  have hr' : run runtimeUnaryRebaseMachine (2 * k + 3)
      ⟨RuntimeUnaryRebaseState.returnRight false,
        pre.length + 1, Tmid⟩ =
      ⟨RuntimeUnaryRebaseState.returnRight false,
        pre.length + 2 * k + 4, Tmid⟩ := by
    rw [hTmid]
    convert hr using 1 <;>
      simp [P, List.append_assoc, Nat.add_assoc] <;> omega
  have hsReturn : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight false,
        pre.length + 1, Tmid⟩ (2 * k + 3) := by
    rw [hTmid]
    simpa [P, List.append_assoc, Nat.add_assoc] using
      runtimeUnaryRebase_returnTrueCells_leftSafe P
        ([false, true] ++ archive) (2 * k + 3) false
  have hsSeed : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight false,
        pre.length + 2 * k + 4, Tmid⟩ 2 := by
    simpa [Tmid, List.append_assoc, Nat.add_assoc] using
      runtimeUnaryRebase_returnSeed_leftSafe
        (pre ++ [false, true, true, true] ++
          List.replicate (2 * k) true) archive false
  rw [show 4 * k + 9 = 2 * k + (4 + ((2 * k + 3) + 2)) by omega]
  apply leftSafeRun_add hsTally
  rw [ht']
  apply leftSafeRun_add hsWrite
  rw [hw']
  apply leftSafeRun_add hsReturn
  rw [hr']
  exact hsSeed

/-! ## Unary writer forward marked-prefix scan -/

/-- A doubled data pair is inspected only by right-moving states, even when
malformed input rejects. -/
theorem runtimeUnaryRebase_dataPair_leftSafe
    (T : List Bool) (p : Nat) (fresh : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.dataLo fresh, p, T⟩ 2 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead]
      at hlive hmove ⊢ <;>
    split_ifs at hlive hmove ⊢ <;> simp_all

/-- Scanning any concrete doubled datum is left-safe. -/
theorem runtimeUnaryRebase_encodeData_leftSafe
    (pre bits tail : List Bool) (fresh : Bool) :
    let T := pre ++ encodeD bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.dataLo fresh, pre.length, T⟩
      (2 * bits.length) := by
  dsimp only
  induction bits generalizing pre with
  | nil =>
      simp [LeftSafeRun]
  | cons bit bits ih =>
      let T := pre ++ bit :: bit :: encodeD bits ++ tail
      have hp := runtimeUnaryRebase_run_equalPair T pre.length fresh bit
        (by simp [T]) (by simp [T])
      have hs : LeftSafeRun runtimeUnaryRebaseMachine
          ⟨RuntimeUnaryRebaseState.dataLo fresh, pre.length, T⟩ 2 :=
        runtimeUnaryRebase_dataPair_leftSafe T pre.length fresh
      rw [show 2 * (bit :: bits).length = 2 + 2 * bits.length by simp; omega]
      apply leftSafeRun_add hs
      rw [hp]
      simpa [T, List.append_assoc] using ih (pre ++ [bit, bit])

/-- The terminating `01` pair is inspected by one right move and then enters
the next forward state. -/
theorem runtimeUnaryRebase_terminator_leftSafe
    (T : List Bool) (p : Nat) (fresh : Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.dataLo fresh, p, T⟩ 2 :=
  runtimeUnaryRebase_dataPair_leftSafe T p fresh

theorem runtimeUnaryRebase_encodeD_processed_leftSafe
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.dataLo false, pre.length, T⟩
      (2 * bits.length + 2) := by
  dsimp only
  let T := pre ++ encodeD bits ++ tail
  have hd := runtimeUnaryRebase_run_encodeData pre bits tail false
  have hsData := runtimeUnaryRebase_encodeData_leftSafe pre bits tail false
  apply leftSafeRun_add hsData
  rw [hd]
  exact runtimeUnaryRebase_terminator_leftSafe T
    (pre.length + 2 * bits.length) false

theorem runtimeUnaryRebase_encodeD_fresh_leftSafe
    (pre bits tail : List Bool) :
    let T := pre ++ encodeD bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.dataLo true, pre.length, T⟩
      (2 * bits.length + 2) := by
  dsimp only
  let T := pre ++ encodeD bits ++ tail
  have hd := runtimeUnaryRebase_run_encodeData pre bits tail true
  have hsData := runtimeUnaryRebase_encodeData_leftSafe pre bits tail true
  apply leftSafeRun_add hsData
  rw [hd]
  exact runtimeUnaryRebase_terminator_leftSafe T
    (pre.length + 2 * bits.length) true

/-- First-header marking is right-moving throughout. -/
theorem runtimeUnaryRebase_markFirstHeader_leftSafe
    (pre bits tail : List Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
        pre ++ [true, false] ++ encodeD bits ++ tail⟩ 4 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]
      at hlive hmove ⊢

theorem runtimeUnaryRebase_skipFirstHeader_leftSafe
    (pre bits tail : List Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
        pre ++ markedSourceBlock true bits ++ tail⟩ 2 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [markedSourceBlock, run_succ, step, runtimeUnaryRebaseMachine,
      moveHead] at hlive hmove ⊢

theorem runtimeUnaryRebase_markHeader_leftSafe
    (pre bits tail : List Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.headerLo, pre.length,
        pre ++ [true, false] ++ encodeD bits ++ tail⟩ 2 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt]
      at hlive hmove ⊢

theorem runtimeUnaryRebase_skipHeader_leftSafe
    (pre bits tail : List Bool) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.headerLo, pre.length,
        pre ++ markedSourceBlock false bits ++ tail⟩ 2 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [markedSourceBlock, run_succ, step, runtimeUnaryRebaseMachine,
      moveHead] at hlive hmove ⊢

/-- A previously marked first archive block is scanned entirely to the right. -/
theorem runtimeUnaryRebase_processedFirstBlock_leftSafe
    (pre bits tail : List Bool) :
    let T := pre ++ markedSourceBlock true bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length, T⟩
      (2 * bits.length + 4) := by
  dsimp only
  let T := pre ++ [false, false] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_skipFirstHeader pre bits tail
  have hsHead := runtimeUnaryRebase_skipFirstHeader_leftSafe pre bits tail
  have hsData := runtimeUnaryRebase_encodeD_processed_leftSafe
    (pre ++ [false, false]) bits tail
  have hh' : run runtimeUnaryRebaseMachine 2
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
        pre ++ markedSourceBlock true bits ++ tail⟩ =
      ⟨RuntimeUnaryRebaseState.dataLo false, pre.length + 2, T⟩ := by
    simpa [T, markedSourceBlock, List.append_assoc] using hh
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega]
  apply leftSafeRun_add hsHead
  rw [hh']
  simpa [T, markedSourceBlock, List.append_assoc] using hsData

/-- Every later previously marked archive block has the same forward-only
safety certificate. -/
theorem runtimeUnaryRebase_processedBlock_leftSafe
    (pre bits tail : List Bool) :
    let T := pre ++ markedSourceBlock false bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T⟩
      (2 * bits.length + 4) := by
  dsimp only
  let T := pre ++ [true, true] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_skipHeader pre bits tail
  have hsHead := runtimeUnaryRebase_skipHeader_leftSafe pre bits tail
  have hsData := runtimeUnaryRebase_encodeD_processed_leftSafe
    (pre ++ [true, true]) bits tail
  have hh' : run runtimeUnaryRebaseMachine 2
      ⟨RuntimeUnaryRebaseState.headerLo, pre.length,
        pre ++ markedSourceBlock false bits ++ tail⟩ =
      ⟨RuntimeUnaryRebaseState.dataLo false, pre.length + 2, T⟩ := by
    simpa [T, markedSourceBlock, List.append_assoc] using hh
  rw [show 2 * bits.length + 4 = 2 + (2 * bits.length + 2) by omega]
  apply leftSafeRun_add hsHead
  rw [hh']
  simpa [T, markedSourceBlock, List.append_assoc] using hsData

/-- Marking and scanning the first fresh archive block is safe, including the
single left move which enters the reverse phase. -/
theorem runtimeUnaryRebase_freshFirstBlock_leftSafe
    (pre bits tail : List Bool) (nextLo : Bool)
    (hnext : tail.getD 0 false = nextLo) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length, T0⟩
      (2 * bits.length + 7) := by
  dsimp only
  let T1 := pre ++ [false, false] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_markFirstHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_fresh
    (pre ++ [false, false]) bits tail
  have hsHead := runtimeUnaryRebase_markFirstHeader_leftSafe pre bits tail
  have hsData := runtimeUnaryRebase_encodeD_fresh_leftSafe
    (pre ++ [false, false]) bits tail
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨RuntimeUnaryRebaseState.dataLo true, pre.length + 2, T1⟩ =
      ⟨RuntimeUnaryRebaseState.checkNext,
        pre.length + 2 * bits.length + 4, T1⟩ := by
    convert hd using 1 <;> simp [T1] <;> omega
  rw [show 2 * bits.length + 7 = 4 + ((2 * bits.length + 2) + 1) by omega]
  apply leftSafeRun_add hsHead
  rw [hh]
  apply leftSafeRun_add
  · simpa [T1, List.append_assoc] using hsData
  · rw [hd']
    exact leftSafeRun_one_of_positive (by simp)

/-- Marking and scanning a later fresh archive block is safe through its
reverse-phase entry. -/
theorem runtimeUnaryRebase_freshBlock_leftSafe
    (pre bits tail : List Bool) (nextLo : Bool)
    (hnext : tail.getD 0 false = nextLo) :
    let T0 := pre ++ [true, false] ++ encodeD bits ++ tail
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T0⟩
      (2 * bits.length + 5) := by
  dsimp only
  let T1 := pre ++ [true, true] ++ encodeD bits ++ tail
  have hh := runtimeUnaryRebase_run_markHeader pre bits tail
  have hd := runtimeUnaryRebase_run_encodeD_fresh
    (pre ++ [true, true]) bits tail
  have hsHead := runtimeUnaryRebase_markHeader_leftSafe pre bits tail
  have hsData := runtimeUnaryRebase_encodeD_fresh_leftSafe
    (pre ++ [true, true]) bits tail
  have hd' : run runtimeUnaryRebaseMachine (2 * bits.length + 2)
      ⟨RuntimeUnaryRebaseState.dataLo true, pre.length + 2, T1⟩ =
      ⟨RuntimeUnaryRebaseState.checkNext,
        pre.length + 2 * bits.length + 4, T1⟩ := by
    convert hd using 1 <;> simp [T1] <;> omega
  rw [show 2 * bits.length + 5 = 2 + ((2 * bits.length + 2) + 1) by omega]
  apply leftSafeRun_add hsHead
  rw [hh]
  apply leftSafeRun_add
  · simpa [T1, List.append_assoc] using hsData
  · rw [hd']
    exact leftSafeRun_one_of_positive (by simp)

/-- The existential clock exported by a processed later-archive scan carries
its safety certificate with it. -/
theorem runtimeUnaryRebase_processedLaterArchive_safeRun
    (pre tail : List Bool) (rest : List (List Bool)) :
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.headerLo, pre.length,
            pre ++ rest.flatMap (markedSourceBlock false) ++ tail⟩ =
        ⟨RuntimeUnaryRebaseState.headerLo,
          pre.length + (rest.flatMap (markedSourceBlock false)).length,
          pre ++ rest.flatMap (markedSourceBlock false) ++ tail⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.headerLo, pre.length,
          pre ++ rest.flatMap (markedSourceBlock false) ++ tail⟩ n := by
  induction rest generalizing pre with
  | nil => exact ⟨0, rfl, by simp [LeftSafeRun]⟩
  | cons bits rest ih =>
      let T := pre ++ markedSourceBlock false bits ++
        rest.flatMap (markedSourceBlock false) ++ tail
      have hb := runtimeUnaryRebase_run_processedBlock pre bits
        (rest.flatMap (markedSourceBlock false) ++ tail)
      have hs := runtimeUnaryRebase_processedBlock_leftSafe pre bits
        (rest.flatMap (markedSourceBlock false) ++ tail)
      obtain ⟨n, hn, hsn⟩ := ih (pre ++ markedSourceBlock false bits)
      have hb' : run runtimeUnaryRebaseMachine (2 * bits.length + 4)
          ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T⟩ =
        ⟨RuntimeUnaryRebaseState.headerLo,
          pre.length + (markedSourceBlock false bits).length, T⟩ := by
        simpa [T, markedSourceBlock_length, List.append_assoc] using hb
      have hn' : run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.headerLo,
            pre.length + (markedSourceBlock false bits).length, T⟩ =
        ⟨RuntimeUnaryRebaseState.headerLo,
          pre.length + (markedSourceBlock false bits).length +
            (rest.flatMap (markedSourceBlock false)).length, T⟩ := by
        simpa [T, List.append_assoc] using hn
      have hs' : LeftSafeRun runtimeUnaryRebaseMachine
          ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T⟩
          (2 * bits.length + 4) := by
        simpa [T, List.append_assoc] using hs
      have hsn' : LeftSafeRun runtimeUnaryRebaseMachine
          ⟨RuntimeUnaryRebaseState.headerLo,
            pre.length + (markedSourceBlock false bits).length, T⟩ n := by
        simpa [T, List.append_assoc] using hsn
      refine ⟨2 * bits.length + 4 + n, ?_, ?_⟩
      · have hrun : run runtimeUnaryRebaseMachine
            (2 * bits.length + 4 + n)
            ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T⟩ =
          ⟨RuntimeUnaryRebaseState.headerLo,
            pre.length + (markedSourceBlock false bits).length +
              (rest.flatMap (markedSourceBlock false)).length, T⟩ := by
          rw [run_add, hb', hn']
        simpa [T, List.flatMap_cons, List.append_assoc,
          Nat.add_assoc] using hrun
      · have hsafe : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.headerLo, pre.length, T⟩
            (2 * bits.length + 4 + n) := by
          apply leftSafeRun_add hs'
          rw [hb']
          exact hsn'
        simpa [T, List.flatMap_cons, List.append_assoc] using hsafe

/-- The whole marked processed prefix, including its distinguished first
block, is returned with one exact safe clock. -/
theorem runtimeUnaryRebase_processedArchive_safeRun
    (pre tail first : List Bool) (more : List (List Bool)) :
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
            pre ++ markedArchive (first :: more) ++ tail⟩ =
        ⟨RuntimeUnaryRebaseState.headerLo,
          pre.length + (markedArchive (first :: more)).length,
          pre ++ markedArchive (first :: more) ++ tail⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
          pre ++ markedArchive (first :: more) ++ tail⟩ n := by
  have hf := runtimeUnaryRebase_run_processedFirstBlock pre first
    (more.flatMap (markedSourceBlock false) ++ tail)
  have hsf := runtimeUnaryRebase_processedFirstBlock_leftSafe pre first
    (more.flatMap (markedSourceBlock false) ++ tail)
  obtain ⟨n, hn, hsn⟩ := runtimeUnaryRebase_processedLaterArchive_safeRun
    (pre ++ markedSourceBlock true first) tail more
  have hf' : run runtimeUnaryRebaseMachine (2 * first.length + 4)
      ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
        pre ++ markedArchive (first :: more) ++ tail⟩ =
    ⟨RuntimeUnaryRebaseState.headerLo,
      pre.length + (markedSourceBlock true first).length,
      pre ++ markedArchive (first :: more) ++ tail⟩ := by
    simpa [markedArchive, markedSourceBlock_length,
      List.append_assoc] using hf
  refine ⟨2 * first.length + 4 + n, ?_, ?_⟩
  · rw [run_add]
    rw [hf']
    simpa [markedArchive, List.append_assoc, Nat.add_assoc] using hn
  · have hsf' : LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo, pre.length,
          pre ++ markedArchive (first :: more) ++ tail⟩
        (2 * first.length + 4) := by
      simpa [markedArchive, List.append_assoc] using hsf
    apply leftSafeRun_add hsf'
    rw [hf']
    simpa [markedArchive, markedSourceBlock_length,
      List.append_assoc, Nat.add_assoc] using hsn

/-- The eight-step unary-writer initialization backs up exactly four cells
before returning to the archive origin. -/
theorem runtimeUnaryRebase_init_leftSafe
    (T : List Bool) (R : Nat) (hR : 4 ≤ R) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, R, T⟩ 8 := by
  intro i hi hlive hmove
  interval_cases i <;>
    simp [run_succ, step, runtimeUnaryRebaseMachine, moveHead, writeAt] at hlive hmove ⊢ <;>
    omega

/-- Control-region invariant for the final archive restoration pass. -/
def RuntimeUnaryRestoreInv (c : Cfg runtimeUnaryRebaseMachine) : Prop :=
  match c.st with
  | .restoreFirstLo | .restoreFirstHi
  | .restoreDataLo | .restoreDataHi _
  | .restoreNext | .restoreHeaderHi | .done | .reject => True
  | _ => False

theorem runtimeUnaryRestoreInv_step
    (c : Cfg runtimeUnaryRebaseMachine) (h : RuntimeUnaryRestoreInv c) :
    RuntimeUnaryRestoreInv (step runtimeUnaryRebaseMachine c) := by
  by_cases hh : runtimeUnaryRebaseMachine.halt c.st = true
  · rw [step_of_halted _ hh]
    exact h
  · have hh' : runtimeUnaryRebaseMachine.halt c.st = false := by
      simpa using hh
    simp only [step, hh', Bool.false_eq_true, if_false]
    cases hs : c.st <;>
      simp [RuntimeUnaryRestoreInv, runtimeUnaryRebaseMachine, hs] at h ⊢ <;>
      split_ifs <;> simp

theorem runtimeUnaryRestoreInv_run
    (c : Cfg runtimeUnaryRebaseMachine) (h : RuntimeUnaryRestoreInv c)
    (n : Nat) :
    RuntimeUnaryRestoreInv (run runtimeUnaryRebaseMachine n c) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [run_succ]
      exact runtimeUnaryRestoreInv_step _ ih

/-- The entire restoration phase is universally left-free, for any tape and
clock; malformed input can only reject, never introduce a backup. -/
theorem runtimeUnaryRebase_restore_leftSafe
    (T : List Bool) (p n : Nat) :
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.restoreFirstLo, p, T⟩ n := by
  intro i hi hlive hmove
  have hinv := runtimeUnaryRestoreInv_run
    (⟨RuntimeUnaryRebaseState.restoreFirstLo, p, T⟩ :
      Cfg runtimeUnaryRebaseMachine) (by simp [RuntimeUnaryRestoreInv]) i
  generalize hc : run runtimeUnaryRebaseMachine i
    ⟨RuntimeUnaryRebaseState.restoreFirstLo, p, T⟩ = c at hinv
  rw [hc] at hlive hmove
  rcases c with ⟨s, q, tp⟩
  cases s <;>
    simp [RuntimeUnaryRestoreInv] at hinv <;>
    simp [runtimeUnaryRebaseMachine] at hmove <;>
    split_ifs at hmove <;> simp_all

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.outputWorkspaceTailLocator_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReverse_canonical_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeRebaseSeed_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReturnSeed_leftSafe_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReturnSeed_leftSafe_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_init_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_boundaryOrigin_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_extendFrontier_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_freshFirstBlock_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_processedArchive_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_restore_leftSafe
