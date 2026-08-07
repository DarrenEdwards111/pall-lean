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
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase

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

set_option maxHeartbeats 1000000 in
/-- The real scheduled origin→workspace→future-archive locator is left-safe
under exactly the clock used by the physical seed controller. -/
theorem scheduled_outputWorkspaceTailLocator_leftSafe
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      ((selectedPrefix (B - t) preBlocks).length + 2)
    let tailClock := 8 * l.1 + 22
    LeftSafeRun outputWorkspaceTailLocatorMachine
      (init outputWorkspaceTailLocatorMachine rcf.tp)
      (locateClock + 1 + tailClock) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let mcf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let W := 2 * B + 2 + pre.length
  let R := W + 2 * bits.length + 4
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hts : t < schedule.length := by simpa [hslen] using ht
  have hget : schedule.getD t [] = bits := by
    dsimp [schedule, bits, l]
    exact literalTapeSchedule_getD x w ht
  have hbit : schedule[t] = bits := by
    rw [← hget, List.getD_eq_getElem schedule [] hts]
  have hsplit : schedule = preBlocks ++ bits :: rest := by
    dsimp [preBlocks, rest]
    conv_lhs => rw [← List.take_append_drop t schedule]
    rw [List.drop_eq_getElem_cons hts, hbit]
  have hprelen : preBlocks.length = t := by
    dsimp [preBlocks]
    rw [List.length_take, Nat.min_eq_left hts.le]
  have hinput : T =
      flattenPairs (progressPairs (B - t) [] preBlocks (bits :: rest)) := by
    dsimp [T]
    rw [sourceSelectorInput, progressPairs, sourceArchive, hsplit]
    simp [hprelen, List.append_assoc]
  have hcf : cf.tp = pre ++ mcf.tp := by
    have hr := sourceRuntimeLookup_run_shape (B - t) preBlocks w l rest
    dsimp [cf, n]
    rw [hinput]
    simpa [bits, pre, trailer, mcf] using congrArg Cfg.tp hr
  have hroute := scheduledRuntimeRelativeOutputSourceRoute x w ht
  have hs := scheduledTruths_take_succ x w ht
  have htp : rcf.tp = outputCap B out' ++ cf.tp := by
    simpa [B, schedule, preBlocks, l, out, out', T, n, cf, M,
      routeClock, rcf, hs] using hroute.2
  have hphysical : rcf.tp = outputCap B out' ++ pre ++ mcf.tp := by
    rw [htp, hcf]
    simp [List.append_assoc]
  have hout : out'.length = t + 1 := by
    dsimp [out']
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using htnext.le)]
  have houtle : out'.length ≤ B := by rw [hout]; exact htnext.le
  have hsource := scheduledRuntimeRelativeOutput_sourceOriginLocate
    x w ht htnext
  have hsource' : run outputSourceLocatorMachine
      (outputSourceLocatorClock B out')
      (init outputSourceLocatorMachine rcf.tp) =
    ⟨OutputSourceLocatorState.done, (outputCap B out').length, rcf.tp⟩ := by
    rw [outputCap_length B out' houtle]
    simpa [B, schedule, preBlocks, l, out, out', T, n, M,
      routeClock, rcf] using hsource
  have htoken : mcf.tp.getD 0 false = true ∧
      mcf.tp.getD 1 false = false := by
    simpa [bits, trailer, mcf] using masterM_literal_startToken w l trailer
  have hworkspace := scheduledRuntimeRelativeOutput_physicalWorkspaceLocate
    x w ht htnext
  have hsafeWorkspace := outputWorkspaceLocator_leftSafe rcf.tp
    (outputCap B out') mcf.tp (B - t) preBlocks
    (outputSourceLocatorClock B out') hphysical hsource' htoken.1 htoken.2
  have htail := scheduledRuntimeRelativeOutput_workspaceTailLocate
    x w ht htnext
  apply outputWorkspaceTailLocator_leftSafe rcf.tp locateClock tailClock W R
  · simpa [B, schedule, preBlocks, l, out, out', T, n, M, routeClock,
      rcf, locateClock, pre] using hworkspace
  · simpa [B, schedule, preBlocks, l, out, out', T, n, M, routeClock,
      rcf, locateClock, pre] using hsafeWorkspace
  · simpa [B, schedule, preBlocks, l, bits, out, T, n, M, routeClock,
      rcf, W, R, tailClock, pre] using htail

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

set_option maxHeartbeats 1000000 in
/-- `markNext` now exports one clock carrying both its exact fresh-block
endpoint and the complete forward-scan safety proof. -/
theorem runtimeUnaryRebase_markNext_safeRun
    (pre : List Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let T0 := pre ++ markedArchive done ++ selectedTail (bits :: more)
    let T1 := pre ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo, pre.length, T0⟩ =
        ⟨RuntimeUnaryRebaseState.revTermHi (more = []),
          pre.length + (markedArchive (done ++ [bits])).length - 1, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo, pre.length, T0⟩ n := by
  dsimp only
  let T0 := pre ++ markedArchive done ++ selectedTail (bits :: more)
  let T1 := pre ++ markedArchive (done ++ [bits]) ++ selectedTail more
  cases done with
  | nil =>
      cases more with
      | nil =>
          have hr := runtimeUnaryRebase_run_freshFirstBlock
            pre bits [] false (by simp)
          have hs := runtimeUnaryRebase_freshFirstBlock_leftSafe
            pre bits [] false (by simp)
          refine ⟨2 * bits.length + 7, ?_, ?_⟩
          · simpa [T0, T1, markedArchive, selectedTail_cons,
              selectedTail_nil, markedSourceBlock_length,
              List.append_assoc] using hr
          · simpa [T0, markedArchive, selectedTail_cons,
              selectedTail_nil, List.append_assoc] using hs
      | cons next later =>
          have hr := runtimeUnaryRebase_run_freshFirstBlock pre bits
            (selectedTail (next :: later)) true (selectedTail_head next later)
          have hs := runtimeUnaryRebase_freshFirstBlock_leftSafe pre bits
            (selectedTail (next :: later)) true (selectedTail_head next later)
          refine ⟨2 * bits.length + 7, ?_, ?_⟩
          · simpa [T0, T1, markedArchive, selectedTail_cons,
              markedSourceBlock_length, List.append_assoc] using hr
          · simpa [T0, markedArchive, selectedTail_cons,
              List.append_assoc] using hs
  | cons first later =>
      obtain ⟨ns, hrs, hss⟩ := runtimeUnaryRebase_processedArchive_safeRun
        pre (selectedTail (bits :: more)) first later
      have happ : markedArchive (first :: later ++ [bits]) =
          markedArchive (first :: later) ++ markedSourceBlock false bits := by
        simpa using markedArchive_append_last (first :: later) bits (by simp)
      cases more with
      | nil =>
          have hrf := runtimeUnaryRebase_run_freshBlock
            (pre ++ markedArchive (first :: later)) bits [] false (by simp)
          have hsf := runtimeUnaryRebase_freshBlock_leftSafe
            (pre ++ markedArchive (first :: later)) bits [] false (by simp)
          refine ⟨ns + (2 * bits.length + 5), ?_, ?_⟩
          · rw [run_add, hrs, happ]
            convert hrf using 1 <;> simp [T0, T1,
              selectedTail_cons, selectedTail_nil,
              List.append_assoc, markedSourceBlock_length] <;> omega
          · apply leftSafeRun_add hss
            rw [hrs]
            simpa [T0, selectedTail_cons, selectedTail_nil,
              List.append_assoc] using hsf
      | cons next later' =>
          have hrf := runtimeUnaryRebase_run_freshBlock
            (pre ++ markedArchive (first :: later)) bits
            (selectedTail (next :: later')) true (selectedTail_head next later')
          have hsf := runtimeUnaryRebase_freshBlock_leftSafe
            (pre ++ markedArchive (first :: later)) bits
            (selectedTail (next :: later')) true (selectedTail_head next later')
          refine ⟨ns + (2 * bits.length + 5), ?_, ?_⟩
          · rw [run_add, hrs, happ]
            convert hrf using 1 <;> simp [T0, T1,
              selectedTail_cons, List.append_assoc,
              markedSourceBlock_length, Bool.not_true] <;> omega
          · apply leftSafeRun_add hss
            rw [hrs]
            simpa [T0, selectedTail_cons, List.append_assoc] using hsf

set_option maxHeartbeats 1000000 in
/-- Reverse traversal of every marked block body exports the same existential
clock for its exact endpoint and safety certificate. -/
theorem runtimeUnaryRebase_reverseMarkedBodies_safeRun
    (pre tail : List Bool) (rest : List (List Bool)) (last : Bool)
    (hne : rest ≠ []) (hpre : 4 ≤ pre.length) :
    let T := pre ++ [false, true] ++ markedArchive rest ++ tail
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.revHi last,
            pre.length + 2 + (markedArchive rest).length - 3, T⟩ =
        ⟨RuntimeUnaryRebaseState.tallyHi last, pre.length - 1, T⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.revHi last,
          pre.length + 2 + (markedArchive rest).length - 3, T⟩ n := by
  dsimp only
  induction rest using List.reverseRecOn generalizing tail with
  | nil => exact absurd rfl hne
  | @append_singleton init bits ih =>
      by_cases hinit : init = []
      · subst init
        let T := pre ++ [false, true] ++ markedSourceBlock true bits ++ tail
        have hp := runtimeUnaryRebase_run_revPairs T
          (pre.length + 2) (bits.length + 1) last (by omega) (by
            intro i hi
            have H := markedRegion_pair_eq
              (pre ++ [false, true]) bits tail true i hi
            simpa [T, List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using H)
        have hp' : run runtimeUnaryRebaseMachine (2 * (bits.length + 1))
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩ =
          ⟨RuntimeUnaryRebaseState.revHi last, pre.length + 1, T⟩ := by
          simpa [markedSourceBlock_length, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hp
        have hsPairs : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩
            (2 * (bits.length + 1)) := by
          simpa [markedSourceBlock_length, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
            runtimeUnaryRebase_revPairs_leftSafe T (pre.length + 2)
              (bits.length + 1) last (by omega)
        have hb := runtimeUnaryRebase_run_boundaryOrigin pre
          (encodeD bits ++ tail) last hpre
        have hb' : run runtimeUnaryRebaseMachine 8
            ⟨RuntimeUnaryRebaseState.revHi last, pre.length + 1, T⟩ =
          ⟨RuntimeUnaryRebaseState.tallyHi last, pre.length - 1, T⟩ := by
          simpa [T, markedSourceBlock, List.append_assoc] using hb
        have hsBoundary : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.revHi last, pre.length + 1, T⟩ 8 := by
          simpa [T, markedSourceBlock, List.append_assoc] using
            runtimeUnaryRebase_boundaryOrigin_leftSafe pre
              (encodeD bits ++ tail) last hpre
        refine ⟨2 * (bits.length + 1) + 8, ?_, ?_⟩
        · have hrun : run runtimeUnaryRebaseMachine
              (2 * (bits.length + 1) + 8)
              ⟨RuntimeUnaryRebaseState.revHi last,
                pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩ =
            ⟨RuntimeUnaryRebaseState.tallyHi last, pre.length - 1, T⟩ := by
            rw [run_add, hp', hb']
          simpa [T, markedArchive] using hrun
        · have hsafe : LeftSafeRun runtimeUnaryRebaseMachine
              ⟨RuntimeUnaryRebaseState.revHi last,
                pre.length + 2 + (markedSourceBlock true bits).length - 3, T⟩
              (2 * (bits.length + 1) + 8) := by
            apply leftSafeRun_add hsPairs
            rw [hp']
            exact hsBoundary
          simpa [T, markedArchive] using hsafe
      · have hneInit : init ≠ [] := hinit
        obtain ⟨core, hcore⟩ := markedArchive_eq_core_term init hneInit
        let P := pre ++ [false, true] ++ core
        let T := pre ++ [false, true] ++ markedArchive (init ++ [bits]) ++ tail
        have hTblock : T =
            (pre ++ [false, true] ++ markedArchive init) ++
              markedSourceBlock false bits ++ tail := by
          simp [T, markedArchive_append_last init bits hinit,
            List.append_assoc]
        have hp := runtimeUnaryRebase_run_revPairs T
          (pre.length + 2 + (markedArchive init).length)
          (bits.length + 1) last (by omega) (by
            intro i hi
            have H := markedRegion_pair_eq
              (pre ++ [false, true] ++ markedArchive init) bits tail false i hi
            rw [hTblock]
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm,
              show 1 + (1 + (2 * i + (markedArchive init).length)) =
                2 + (2 * i + (markedArchive init).length) by omega,
              show 1 + (1 + (1 + (2 * i + (markedArchive init).length))) =
                1 + (2 + (2 * i + (markedArchive init).length)) by omega]
              using H)
        have hp' : run runtimeUnaryRebaseMachine (2 * (bits.length + 1))
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive (init ++ [bits])).length - 3,
              T⟩ =
          ⟨RuntimeUnaryRebaseState.revHi last,
            pre.length + 2 + (markedArchive init).length - 1, T⟩ := by
          rw [markedArchive_append_last init bits hinit, List.length_append,
            markedSourceBlock_length]
          rw [show pre.length + 2 +
              ((markedArchive init).length + (2 * bits.length + 4)) - 3 =
              pre.length + 2 + (markedArchive init).length +
                2 * (bits.length + 1) - 1 by omega]
          exact hp
        have hsPairs : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive (init ++ [bits])).length - 3,
              T⟩ (2 * (bits.length + 1)) := by
          rw [markedArchive_append_last init bits hinit, List.length_append,
            markedSourceBlock_length]
          convert runtimeUnaryRebase_revPairs_leftSafe T
            (pre.length + 2 + (markedArchive init).length)
            (bits.length + 1) last (by omega) using 1 <;>
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
        have hb := runtimeUnaryRebase_run_boundaryInter P
          (encodeD bits ++ tail) last (by simp [P]; omega)
        have hb' : run runtimeUnaryRebaseMachine 8
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive init).length - 1, T⟩ =
          ⟨RuntimeUnaryRebaseState.revHi last,
            pre.length + 2 + (markedArchive init).length - 3, T⟩ := by
          have hT : T = P ++ [false, true, true, true] ++
              encodeD bits ++ tail := by
            simp [T, P, markedArchive_append_last init bits hinit,
              markedSourceBlock, hcore, List.append_assoc]
          rw [hT]
          simpa [P, hcore, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hb
        have hsBoundary : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive init).length - 1, T⟩ 8 := by
          have hT : T = P ++ [false, true, true, true] ++
              encodeD bits ++ tail := by
            simp [T, P, markedArchive_append_last init bits hinit,
              markedSourceBlock, hcore, List.append_assoc]
          rw [hT]
          simpa [P, hcore, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            runtimeUnaryRebase_boundaryInter_leftSafe P
              (encodeD bits ++ tail) last (by simp [P]; omega)
        obtain ⟨n, hn, hsn⟩ := ih
          (markedSourceBlock false bits ++ tail) hneInit
        have hn' : run runtimeUnaryRebaseMachine n
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive init).length - 3, T⟩ =
          ⟨RuntimeUnaryRebaseState.tallyHi last, pre.length - 1, T⟩ := by
          simpa [T, markedArchive_append_last init bits hinit,
            List.append_assoc] using hn
        have hsn' : LeftSafeRun runtimeUnaryRebaseMachine
            ⟨RuntimeUnaryRebaseState.revHi last,
              pre.length + 2 + (markedArchive init).length - 3, T⟩ n := by
          simpa [T, markedArchive_append_last init bits hinit,
            List.append_assoc] using hsn
        refine ⟨2 * (bits.length + 1) + 8 + n, ?_, ?_⟩
        · rw [show 2 * (bits.length + 1) + 8 + n =
            2 * (bits.length + 1) + (8 + n) by omega,
            run_add, hp', run_add, hb', hn']
        · rw [show 2 * (bits.length + 1) + 8 + n =
            2 * (bits.length + 1) + (8 + n) by omega]
          apply leftSafeRun_add hsPairs
          rw [hp']
          apply leftSafeRun_add hsBoundary
          rw [hb']
          exact hsn'

/-- The complete reverse return from the marked archive to the unary tally
frontier shares one exact operational and safe clock. -/
theorem runtimeUnaryRebase_returnMarked_safeRun
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
    let T := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.revTermHi (more = []),
            A.length + (markedArchive (done ++ [bits])).length - 1, T⟩ =
        ⟨RuntimeUnaryRebaseState.tallyHi (more = []),
          pre.length + 2 * done.length + 3, T⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.revTermHi (more = []),
          A.length + (markedArchive (done ++ [bits])).length - 1, T⟩ n := by
  dsimp only
  let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
  let T := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
  let P := pre ++ [a, b] ++ [false, true] ++
    List.replicate (2 * done.length) true
  have hm := markedArchive_append_singleton_length done bits
  have ht := runtimeUnaryRebase_run_revTerm T
    (A.length + (markedArchive (done ++ [bits])).length - 1)
    (more = []) (by simp [A, unaryRebaseFrontier]; omega)
  have hst : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.revTermHi (more = []),
        A.length + (markedArchive (done ++ [bits])).length - 1, T⟩ 2 := by
    apply runtimeUnaryRebase_leftSafe_of_clock
    simp [A, unaryRebaseFrontier]
    omega
  obtain ⟨nr, hr, hsr⟩ := runtimeUnaryRebase_reverseMarkedBodies_safeRun P
    (selectedTail more) (done ++ [bits]) (more = []) (by simp)
    (by simp [P]; omega)
  have hstart : P.length + 2 + (markedArchive (done ++ [bits])).length - 3 =
      A.length + (markedArchive (done ++ [bits])).length - 3 := by
    simp [P, A, unaryRebaseFrontier]
    omega
  have hphead : P.length - 1 = pre.length + 2 * done.length + 3 := by
    simp [P]
    omega
  rw [hstart, hphead] at hr
  rw [hstart] at hsr
  refine ⟨2 + nr, ?_, ?_⟩
  · rw [run_add, ht]
    have hsub : A.length + (markedArchive (done ++ [bits])).length - 1 - 2 =
        A.length + (markedArchive (done ++ [bits])).length - 3 := by omega
    rw [hsub]
    simpa [A, P, T, unaryRebaseFrontier, List.append_assoc] using hr
  · apply leftSafeRun_add hst
    rw [ht]
    have hsub : A.length + (markedArchive (done ++ [bits])).length - 1 - 2 =
        A.length + (markedArchive (done ++ [bits])).length - 3 := by omega
    rw [hsub]
    simpa [A, P, T, unaryRebaseFrontier, List.append_assoc] using hsr

/-- Forward marking and the complete reverse return are now one visit-prefix
certificate, exactly matching `runtimeUnaryRebase_run_markReturn`. -/
theorem runtimeUnaryRebase_markReturn_safeRun
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits : List Bool) (more : List (List Bool)) :
    let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
    let T0 := A ++ markedArchive done ++ selectedTail (bits :: more)
    let T1 := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo, A.length, T0⟩ =
        ⟨RuntimeUnaryRebaseState.tallyHi (more = []),
          pre.length + 2 * done.length + 3, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo, A.length, T0⟩ n := by
  dsimp only
  let A := pre ++ [a, b] ++ unaryRebaseFrontier done.length
  let T0 := A ++ markedArchive done ++ selectedTail (bits :: more)
  let T1 := A ++ markedArchive (done ++ [bits]) ++ selectedTail more
  obtain ⟨nf, hf, hsf⟩ := runtimeUnaryRebase_markNext_safeRun
    A done bits more
  obtain ⟨nb, hb, hsb⟩ := runtimeUnaryRebase_returnMarked_safeRun
    pre a b done bits more
  refine ⟨nf + nb, ?_, ?_⟩
  · rw [run_add, hf, hb]
  · apply leftSafeRun_add hsf
    rw [hf]
    exact hsb

theorem runtimeUnaryRebase_extendMarked_nonfinal_leftSafe
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits next : List Bool) (later : List (List Bool)) :
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier done.length ++
      markedArchive (done ++ [bits]) ++ selectedTail (next :: later)
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi false,
        pre.length + 2 * done.length + 3, T0⟩
      (4 * done.length + 9) := by
  dsimp only
  simpa [List.append_assoc] using
    runtimeUnaryRebase_extendFrontier_leftSafe pre
      (markedArchive (done ++ [bits]) ++ selectedTail (next :: later))
      a b done.length

set_option maxHeartbeats 1000000 in
/-- A complete nonfinal visit now carries its exact endpoint and composed
left-safety certificate under the same clock. -/
theorem runtimeUnaryRebase_visit_nonfinal_safeRun
    (pre : List Bool) (a b : Bool) (done : List (List Bool))
    (bits next : List Bool) (later : List (List Bool)) :
    let k := done.length
    let T0 := pre ++ [a, b] ++ unaryRebaseFrontier k ++
      markedArchive done ++ selectedTail (bits :: next :: later)
    let T1 := pre ++ unaryRebaseFrontier (k + 1) ++
      markedArchive (done ++ [bits]) ++ selectedTail (next :: later)
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo,
            pre.length + 2 * k + 6, T0⟩ =
        ⟨RuntimeUnaryRebaseState.firstLo,
          pre.length + 2 * k + 6, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo,
          pre.length + 2 * k + 6, T0⟩ n := by
  dsimp only
  obtain ⟨nm, hm, hsm⟩ := runtimeUnaryRebase_markReturn_safeRun
    pre a b done bits (next :: later)
  have hm' : run runtimeUnaryRebaseMachine nm
      ⟨RuntimeUnaryRebaseState.firstLo,
        pre.length + 2 * done.length + 6,
        pre ++ [a, b] ++ unaryRebaseFrontier done.length ++
          markedArchive done ++ selectedTail (bits :: next :: later)⟩ =
    ⟨RuntimeUnaryRebaseState.tallyHi false,
      pre.length + 2 * done.length + 3,
      pre ++ [a, b] ++ unaryRebaseFrontier done.length ++
        markedArchive (done ++ [bits]) ++ selectedTail (next :: later)⟩ := by
    simpa [unaryRebaseFrontier, List.append_assoc] using hm
  have hsm' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo,
        pre.length + 2 * done.length + 6,
        pre ++ [a, b] ++ unaryRebaseFrontier done.length ++
          markedArchive done ++ selectedTail (bits :: next :: later)⟩ nm := by
    simpa [unaryRebaseFrontier, List.append_assoc] using hsm
  have he := runtimeUnaryRebase_run_extendMarked_nonfinal
    pre a b done bits next later
  have hse := runtimeUnaryRebase_extendMarked_nonfinal_leftSafe
    pre a b done bits next later
  refine ⟨nm + (4 * done.length + 9), ?_, ?_⟩
  · rw [run_add, hm', he]
  · apply leftSafeRun_add hsm'
    rw [hm']
    exact hse

/-- The final tally and doubled-marker write are safe through the handoff to
the right-return phase. -/
theorem runtimeUnaryRebase_finalFrontier_toReturn_leftSafe
    (pre archive : List Bool) (c d a b : Bool) (k : Nat) :
    let T0 := pre ++ [c, d, a, b] ++ unaryRebaseFrontier k ++ archive
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true,
        pre.length + 2 * k + 5, T0⟩ (2 * k + 8) := by
  dsimp only
  let T0 := pre ++ [c, d, a, b] ++ unaryRebaseFrontier k ++ archive
  have ht : run runtimeUnaryRebaseMachine (2 * k)
      ⟨RuntimeUnaryRebaseState.tallyHi true,
        pre.length + 2 * k + 5, T0⟩ =
    ⟨RuntimeUnaryRebaseState.tallyHi true, pre.length + 5, T0⟩ := by
    have H := runtimeUnaryRebase_run_tallyTruePairs T0
      (pre.length + 6) k true (by omega) (by
        intro i hi
        have h := prefixed_replicate_true
          (pre ++ [c, d, a, b, false, true]) ([false, true] ++ archive)
          (2 * k) i hi
        simpa [T0, unaryRebaseFrontier, List.append_assoc] using h)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using H
  have hsTally : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true,
        pre.length + 2 * k + 5, T0⟩ (2 * k) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      runtimeUnaryRebase_tallyPairs_leftSafe
        T0 (pre.length + 6) k true (by omega)
  have hsWrite : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true, pre.length + 5, T0⟩ 8 := by
    simpa [T0, unaryRebaseFrontier, List.append_assoc] using
      runtimeUnaryRebase_finalFrontierWrite_leftSafe pre
        (List.replicate (2 * k) true ++ [false, true] ++ archive)
        c d a b
  rw [show 2 * k + 8 = 2 * k + 8 by rfl]
  apply leftSafeRun_add hsTally
  rw [ht]
  exact hsWrite

/-- The final right return and seed crossing are both right-moving and enter
restoration at the exact canonical head. -/
theorem runtimeUnaryRebase_finalFrontier_return_leftSafe
    (pre archive : List Bool) (k : Nat) :
    let Tmid := pre ++ [false, true, false, true, true, true] ++
      List.replicate (2 * k) true ++ [false, true] ++ archive
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight true, pre.length + 3, Tmid⟩
      (2 * k + 5) := by
  dsimp only
  let Tmid := pre ++ [false, true, false, true, true, true] ++
    List.replicate (2 * k) true ++ [false, true] ++ archive
  let P := pre ++ [false, true, false]
  have hTmid : Tmid =
      P ++ List.replicate (2 * k + 3) true ++ [false, true] ++ archive := by
    rw [show 2 * k + 3 = 3 + 2 * k by omega, List.replicate_add]
    simp [P, Tmid, List.append_assoc]
  have hr := runtimeUnaryRebase_run_returnTrueCells P
    ([false, true] ++ archive) (2 * k + 3) true
  have hr' : run runtimeUnaryRebaseMachine (2 * k + 3)
      ⟨RuntimeUnaryRebaseState.returnRight true, pre.length + 3, Tmid⟩ =
    ⟨RuntimeUnaryRebaseState.returnRight true,
      pre.length + 2 * k + 6, Tmid⟩ := by
    rw [hTmid]
    simpa [P, List.append_assoc, Nat.add_assoc,
      show 3 + (2 * k + 3) = 2 * k + 6 by omega] using hr
  have hsReturn : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight true, pre.length + 3, Tmid⟩
      (2 * k + 3) := by
    rw [hTmid]
    simpa [P, List.append_assoc, Nat.add_assoc] using
      runtimeUnaryRebase_returnTrueCells_leftSafe P
        ([false, true] ++ archive) (2 * k + 3) true
  have hsSeed : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.returnRight true,
        pre.length + 2 * k + 6, Tmid⟩ 2 := by
    simpa [Tmid, List.append_assoc, Nat.add_assoc] using
      runtimeUnaryRebase_returnSeed_leftSafe
        (pre ++ [false, true, false, true, true, true] ++
          List.replicate (2 * k) true) archive true
  rw [show 2 * k + 5 = (2 * k + 3) + 2 by omega]
  apply leftSafeRun_add hsReturn
  rw [hr']
  exact hsSeed

/-- Complete final-frontier extension, including doubled-marker installation,
is safe under its exact native clock. -/
theorem runtimeUnaryRebase_extendFrontier_final_leftSafe
    (pre archive : List Bool) (c d a b : Bool) (k : Nat) :
    let T0 := pre ++ [c, d, a, b] ++ unaryRebaseFrontier k ++ archive
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true,
        pre.length + 2 * k + 5, T0⟩ (4 * k + 13) := by
  dsimp only
  have hf := runtimeUnaryRebase_run_finalFrontier_toReturn
    pre archive c d a b k
  rw [show 4 * k + 13 = (2 * k + 8) + (2 * k + 5) by omega]
  apply leftSafeRun_add
    (runtimeUnaryRebase_finalFrontier_toReturn_leftSafe
      pre archive c d a b k)
  rw [hf]
  exact runtimeUnaryRebase_finalFrontier_return_leftSafe pre archive k

theorem runtimeUnaryRebase_extendMarked_final_leftSafe
    (pre : List Bool) (c d a b : Bool) (done : List (List Bool))
    (bits : List Bool) :
    let T0 := pre ++ [c, d, a, b] ++ unaryRebaseFrontier done.length ++
      markedArchive (done ++ [bits])
    LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.tallyHi true,
        pre.length + 2 * done.length + 5, T0⟩
      (4 * done.length + 13) := by
  dsimp only
  simpa [List.append_assoc] using
    runtimeUnaryRebase_extendFrontier_final_leftSafe pre
      (markedArchive (done ++ [bits])) c d a b done.length

set_option maxHeartbeats 1000000 in
/-- The last archive visit carries its exact restoration endpoint and complete
left-safety proof under one existential clock. -/
theorem runtimeUnaryRebase_visit_final_safeRun
    (pre : List Bool) (c d a b : Bool) (done : List (List Bool))
    (bits : List Bool) :
    let k := done.length
    let T0 := pre ++ [c, d, a, b] ++ unaryRebaseFrontier k ++
      markedArchive done ++ selectedTail [bits]
    let T1 := pre ++ [false, true] ++ unaryRebaseFrontier (k + 1) ++
      markedArchive (done ++ [bits])
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo,
            pre.length + 2 * k + 8, T0⟩ =
        ⟨RuntimeUnaryRebaseState.restoreFirstLo,
          pre.length + 2 * k + 8, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo,
          pre.length + 2 * k + 8, T0⟩ n := by
  dsimp only
  obtain ⟨nm, hm, hsm⟩ := runtimeUnaryRebase_markReturn_safeRun
    (pre ++ [c, d]) a b done bits []
  have hm' : run runtimeUnaryRebaseMachine nm
      ⟨RuntimeUnaryRebaseState.firstLo,
        pre.length + 2 * done.length + 8,
        pre ++ [c, d, a, b] ++ unaryRebaseFrontier done.length ++
          markedArchive done ++ selectedTail [bits]⟩ =
    ⟨RuntimeUnaryRebaseState.tallyHi true,
      pre.length + 2 * done.length + 5,
      pre ++ [c, d, a, b] ++ unaryRebaseFrontier done.length ++
        markedArchive (done ++ [bits])⟩ := by
    convert hm using 2 <;> simp [unaryRebaseFrontier, selectedTail_nil,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> omega
  have hsm' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo,
        pre.length + 2 * done.length + 8,
        pre ++ [c, d, a, b] ++ unaryRebaseFrontier done.length ++
          markedArchive done ++ selectedTail [bits]⟩ nm := by
    convert hsm using 1 <;> simp [unaryRebaseFrontier,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] <;> omega
  have he := runtimeUnaryRebase_run_extendMarked_final
    pre c d a b done bits
  have hse := runtimeUnaryRebase_extendMarked_final_leftSafe
    pre c d a b done bits
  refine ⟨nm + (4 * done.length + 13), ?_, ?_⟩
  · rw [run_add, hm']
    simpa [List.append_assoc] using he
  · apply leftSafeRun_add hsm'
    rw [hm']
    exact hse

set_option maxHeartbeats 1000000 in
/-- All nonempty archive visits, including the unique final visit, carry one
exact endpoint and one composed safety certificate. -/
theorem runtimeUnaryRebase_visits_safeRun
    (base scratch : List Bool) (done todo : List (List Bool))
    (htodo : todo ≠ []) (hscratch : scratch.length = 2 * todo.length + 2) :
    let R := base.length + scratch.length + 2 * done.length + 4
    let T0 := base ++ scratch ++ unaryRebaseFrontier done.length ++
      markedArchive done ++ selectedTail todo
    let T1 := base ++ [false, true] ++
      unaryRebaseFrontier (done.length + todo.length) ++
      markedArchive (done ++ todo)
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.firstLo, R, T0⟩ =
        ⟨RuntimeUnaryRebaseState.restoreFirstLo, R, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.firstLo, R, T0⟩ n := by
  dsimp only
  induction todo generalizing scratch done with
  | nil => exact absurd rfl htodo
  | cons bits more ih =>
      have hslen : scratch.length = 2 * more.length + 4 := by
        simpa using hscratch
      obtain ⟨pre, a, b, hshape, hpre⟩ := split_last_two hslen
      subst scratch
      have hdoneLen : (done ++ [bits]).length = done.length + 1 := by simp
      cases more with
      | nil =>
          have htodoLen : [bits].length = 1 := rfl
          have hpre2 : pre.length = 2 := by simpa using hpre
          obtain ⟨markerBase, c, d, hmarker, hmarkerLen⟩ :=
            split_last_two (n := 0) hpre2
          have hmarkerNil : markerBase = [] :=
            List.eq_nil_of_length_eq_zero hmarkerLen
          subst markerBase
          subst pre
          obtain ⟨nv, hv, hsv⟩ := runtimeUnaryRebase_visit_final_safeRun
            base c d a b done bits
          refine ⟨nv, ?_, ?_⟩
          · convert hv using 2 <;> simp [selectedTail_nil, List.append_assoc,
              List.length_cons, List.length_nil, Nat.add_assoc,
              hdoneLen, htodoLen, Nat.add_comm, Nat.add_left_comm] <;> omega
          · convert hsv using 1 <;> simp [selectedTail_nil,
              List.append_assoc, List.length_cons, List.length_nil,
              Nat.add_assoc, hdoneLen, htodoLen,
              Nat.add_comm, Nat.add_left_comm] <;> omega
      | cons next later =>
          obtain ⟨nv, hv, hsv⟩ := runtimeUnaryRebase_visit_nonfinal_safeRun
            (base ++ pre) a b done bits next later
          have htodoLen : (bits :: next :: later).length =
              (next :: later).length + 1 := rfl
          have hprelen : pre.length = 2 * (next :: later).length + 2 := by
            simpa using hpre
          obtain ⟨ni, hi, hsi⟩ := ih pre (done ++ [bits]) (by simp) hprelen
          have hv' : run runtimeUnaryRebaseMachine nv
              ⟨RuntimeUnaryRebaseState.firstLo,
                base.length + (pre ++ [a, b]).length +
                  2 * done.length + 4,
                base ++ (pre ++ [a, b]) ++
                  unaryRebaseFrontier done.length ++ markedArchive done ++
                  selectedTail (bits :: next :: later)⟩ =
            ⟨RuntimeUnaryRebaseState.firstLo,
              base.length + pre.length +
                2 * (done ++ [bits]).length + 4,
              base ++ pre ++ unaryRebaseFrontier (done ++ [bits]).length ++
                markedArchive (done ++ [bits]) ++
                selectedTail (next :: later)⟩ := by
            convert hv using 2 <;> simp [List.append_assoc, Nat.add_assoc,
              List.length_cons, List.length_nil, Nat.add_comm,
              hdoneLen, htodoLen, Nat.add_left_comm] <;> omega
          have hsv' : LeftSafeRun runtimeUnaryRebaseMachine
              ⟨RuntimeUnaryRebaseState.firstLo,
                base.length + (pre ++ [a, b]).length +
                  2 * done.length + 4,
                base ++ (pre ++ [a, b]) ++
                  unaryRebaseFrontier done.length ++ markedArchive done ++
                  selectedTail (bits :: next :: later)⟩ nv := by
            convert hsv using 1 <;> simp [List.append_assoc, Nat.add_assoc,
              List.length_cons, List.length_nil, Nat.add_comm,
              hdoneLen, htodoLen, Nat.add_left_comm] <;> omega
          refine ⟨nv + ni, ?_, ?_⟩
          · rw [run_add, hv']
            convert hi using 1 <;> simp [List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] <;> omega
          · apply leftSafeRun_add hsv'
            rw [hv']
            convert hsi using 1 <;> simp [List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] <;> omega

set_option maxHeartbeats 1000000 in
/-- Initialization, every archive visit, and byte-for-byte archive restoration
form one exact complete unary-writer run with one `LeftSafeRun`. -/
theorem runtimeUnaryRebase_complete_safeRun
    (base scratch : List Bool) (a b : Bool)
    (bits : List Bool) (more : List (List Bool))
    (hscratch : scratch.length = 2 * (bits :: more).length + 2) :
    let R := base.length + scratch.length + 4
    let T0 := base ++ scratch ++ [a, b, false, true] ++
      selectedTail (bits :: more)
    let T1 := base ++ [false, true] ++
      unaryRebaseFrontier (bits :: more).length ++ selectedTail (bits :: more)
    ∃ n,
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.init1, R, T0⟩ =
        ⟨RuntimeUnaryRebaseState.done,
          R + (selectedTail (bits :: more)).length, T1⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.init1, R, T0⟩ n := by
  dsimp only
  have hi := runtimeUnaryRebase_run_init (base ++ scratch)
    (selectedTail (bits :: more)) a b
  have hsi : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, base.length + scratch.length + 4,
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more)⟩ 8 := by
    apply runtimeUnaryRebase_leftSafe_of_clock
    simp [hscratch]
    omega
  obtain ⟨nv, hv, hsv⟩ := runtimeUnaryRebase_visits_safeRun
    base scratch [] (bits :: more) (by simp) hscratch
  have hr := runtimeUnaryRebase_run_restoreArchive
    (base ++ [false, true] ++ unaryRebaseFrontier (bits :: more).length)
    bits more
  let nc := 2 * bits.length + 4 + restoreArchiveClock more + 1
  have hi' : run runtimeUnaryRebaseMachine 8
      ⟨RuntimeUnaryRebaseState.init1, base.length + scratch.length + 4,
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more)⟩ =
    ⟨RuntimeUnaryRebaseState.firstLo, base.length + scratch.length + 4,
      base ++ scratch ++ unaryRebaseFrontier 0 ++
        selectedTail (bits :: more)⟩ := by
    simpa [unaryRebaseFrontier_zero, List.append_assoc] using hi
  have hv' : run runtimeUnaryRebaseMachine nv
      ⟨RuntimeUnaryRebaseState.firstLo, base.length + scratch.length + 4,
        base ++ scratch ++ unaryRebaseFrontier 0 ++
          selectedTail (bits :: more)⟩ =
    ⟨RuntimeUnaryRebaseState.restoreFirstLo,
      base.length + scratch.length + 4,
      base ++ [false, true] ++
        unaryRebaseFrontier (bits :: more).length ++
        markedArchive (bits :: more)⟩ := by
    simpa [List.append_assoc] using hv
  have hsv' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.firstLo, base.length + scratch.length + 4,
        base ++ scratch ++ unaryRebaseFrontier 0 ++
          selectedTail (bits :: more)⟩ nv := by
    simpa [List.append_assoc] using hsv
  have hpre : (base ++ [false, true] ++
      unaryRebaseFrontier (bits :: more).length).length =
      base.length + scratch.length + 4 := by
    simp [unaryRebaseFrontier, hscratch]
    omega
  have hr' := hr
  rw [hpre] at hr'
  have hsr : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.restoreFirstLo,
        base.length + scratch.length + 4,
        base ++ [false, true] ++
          unaryRebaseFrontier (bits :: more).length ++
          markedArchive (bits :: more)⟩ nc := by
    let Inv : Cfg runtimeUnaryRebaseMachine → Prop := fun c =>
      match c.st with
      | .restoreFirstLo | .restoreFirstHi
      | .restoreDataLo | .restoreDataHi _
      | .restoreNext | .restoreHeaderHi | .done | .reject => True
      | _ => False
    have hstep : ∀ c, Inv c → Inv (step runtimeUnaryRebaseMachine c) := by
      intro c hc
      by_cases hh : runtimeUnaryRebaseMachine.halt c.st = true
      · rw [step_of_halted _ hh]
        exact hc
      · have hh' : runtimeUnaryRebaseMachine.halt c.st = false := by
          simpa using hh
        simp only [step, hh', Bool.false_eq_true, if_false]
        cases hs : c.st <;>
          simp [Inv, runtimeUnaryRebaseMachine, hs] at hc ⊢ <;>
          split_ifs <;> simp
    have hrunInv : ∀ (c : Cfg runtimeUnaryRebaseMachine), Inv c →
        ∀ n, Inv (run runtimeUnaryRebaseMachine n c) := by
      intro c hc n
      induction n with
      | zero => simpa using hc
      | succ n ih =>
          rw [run_succ]
          exact hstep _ ih
    intro i hi hlive hmove
    have hinv := hrunInv
      (⟨RuntimeUnaryRebaseState.restoreFirstLo,
        base.length + scratch.length + 4,
        base ++ [false, true] ++
          unaryRebaseFrontier (bits :: more).length ++
          markedArchive (bits :: more)⟩ : Cfg runtimeUnaryRebaseMachine)
      (by simp [Inv]) i
    generalize hc : run runtimeUnaryRebaseMachine i
      ⟨RuntimeUnaryRebaseState.restoreFirstLo,
        base.length + scratch.length + 4,
        base ++ [false, true] ++
          unaryRebaseFrontier (bits :: more).length ++
          markedArchive (bits :: more)⟩ = c at hinv
    rw [hc] at hlive hmove
    rcases c with ⟨s, q, tp⟩
    cases s <;>
      simp [Inv] at hinv <;>
      simp [runtimeUnaryRebaseMachine] at hmove <;>
      split_ifs at hmove <;> simp_all
  refine ⟨8 + nv + nc, ?_, ?_⟩
  · rw [show 8 + nv + nc = 8 + (nv + nc) by omega,
      run_add, hi', run_add, hv']
    simpa [nc, selectedTail_nil, List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hr'
  · rw [show 8 + nv + nc = 8 + (nv + nc) by omega]
    apply leftSafeRun_add hsi
    rw [hi']
    apply leftSafeRun_add hsv'
    rw [hv']
    exact hsr

/-- Physical scratch splitting preserves the complete unary writer's exact
endpoint and safety certificate, while exposing the untouched leading base. -/
theorem runtimeUnaryRebase_physical_safeRun
    (phys : List Bool) (bits : List Bool) (more : List (List Bool))
    (hfit : 2 * (bits :: more).length + 4 ≤ phys.length) :
    let R := phys.length + 2
    let T0 := phys ++ [false, true] ++ selectedTail (bits :: more)
    ∃ base n,
      base.IsPrefix phys ∧
      base.length = phys.length - (2 * (bits :: more).length + 4) ∧
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.init1, R, T0⟩ =
        ⟨RuntimeUnaryRebaseState.done,
          R + (selectedTail (bits :: more)).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput (bits :: more).length 0 (bits :: more)⟩ ∧
      LeftSafeRun runtimeUnaryRebaseMachine
        ⟨RuntimeUnaryRebaseState.init1, R, T0⟩ n := by
  dsimp only
  let L := 2 * (bits :: more).length + 4
  let p := phys.length - L
  let suffix := phys.drop p
  have hsuffix : suffix.length = 2 * (bits :: more).length + 4 := by
    simp only [suffix, List.length_drop]
    change phys.length - (phys.length - L) = L
    omega
  obtain ⟨scratch, a, b, hs, hscratch⟩ := split_last_two hsuffix
  let base := phys.take p
  have hphys : phys = base ++ scratch ++ [a, b] := by
    have H := List.take_append_drop p phys
    rw [show phys.drop p = suffix by rfl, hs] at H
    simpa [base, List.append_assoc] using H.symm
  obtain ⟨n, hn, hsn⟩ := runtimeUnaryRebase_complete_safeRun
    base scratch a b bits more hscratch
  refine ⟨base, n, ?_, ?_, ?_, ?_⟩
  · exact ⟨scratch ++ [a, b], by simpa [List.append_assoc] using hphys.symm⟩
  · have hp : p ≤ phys.length := by simp [p]
    simp [base, List.length_take, p, L]
  · have hR : phys.length + 2 = base.length + scratch.length + 4 := by
      rw [hphys]
      simp
      omega
    have hT : phys ++ [false, true] ++ selectedTail (bits :: more) =
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more) := by
      rw [hphys]
      simp [List.append_assoc]
    have hn' := hn
    rw [unaryRebaseFrontier_eq_boundary_prefix] at hn'
    have hout : base ++ [false, true] ++
          ([false, true] ++ zeroCopyRebasePrefix (bits :: more).length) ++
          selectedTail (bits :: more) =
        base ++ [false, true, false, true] ++
          sourceSelectorInput (bits :: more).length 0 (bits :: more) := by
      have hz := zeroCopyRebasePrefix_archive (bits :: more)
      simpa [List.append_assoc] using
        congrArg (fun X => base ++ [false, true, false, true] ++ X) hz
    rw [hout] at hn'
    rw [hR, hT]
    exact hn'
  · have hR : phys.length + 2 = base.length + scratch.length + 4 := by
      rw [hphys]
      simp
      omega
    have hT : phys ++ [false, true] ++ selectedTail (bits :: more) =
        base ++ scratch ++ [a, b, false, true] ++
          selectedTail (bits :: more) := by
      rw [hphys]
      simp [List.append_assoc]
    rw [hR, hT]
    exact hsn

/-- Exact safety compositor for the real physical controller: physical
workspace/archive return and seed installation hand directly to the complete
unary writer without changing the discovered head. -/
theorem outputWorkspaceArchiveReturnUnaryRebase_leftSafe_of_runs
    (T0 Tseed Tout : List Bool) (seedClock unaryClock R finalHead : Nat)
    (hseed : run outputWorkspaceArchiveReturnSeedMachine seedClock
        (init outputWorkspaceArchiveReturnSeedMachine T0) =
      ⟨Sum.inr (Sum.inr RuntimeRebaseSeedState.done), R, Tseed⟩)
    (hsSeed : LeftSafeRun outputWorkspaceArchiveReturnSeedMachine
      (init outputWorkspaceArchiveReturnSeedMachine T0) seedClock)
    (hunary : run runtimeUnaryRebaseMachine unaryClock
        ⟨RuntimeUnaryRebaseState.init1, R, Tseed⟩ =
      ⟨RuntimeUnaryRebaseState.done, finalHead, Tout⟩)
    (hsUnary : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, R, Tseed⟩ unaryClock) :
    LeftSafeRun outputWorkspaceArchiveReturnUnaryRebaseMachine
      (init outputWorkspaceArchiveReturnUnaryRebaseMachine T0)
      (seedClock + 1 + unaryClock) := by
  have hhUnary : runtimeUnaryRebaseMachine.halt
      (run runtimeUnaryRebaseMachine unaryClock
        ⟨runtimeUnaryRebaseMachine.start, R, Tseed⟩).st = true := by
    change runtimeUnaryRebaseMachine.halt
      (run runtimeUnaryRebaseMachine unaryClock
        ⟨RuntimeUnaryRebaseState.init1, R, Tseed⟩).st = true
    rw [hunary]
    rfl
  simpa [outputWorkspaceArchiveReturnUnaryRebaseMachine] using
    headSeq_leftSafe outputWorkspaceArchiveReturnSeedMachine
      runtimeUnaryRebaseMachine T0 Tseed seedClock unaryClock R
      (Sum.inr (Sum.inr RuntimeRebaseSeedState.done)) hseed rfl hsSeed
      hsUnary hhUnary

set_option maxHeartbeats 1000000 in
/-- The scheduled physical workspace/tail locator and canonical archive
return/seed controller form one unconditional safety certificate. -/
theorem scheduled_outputWorkspaceArchiveReturnSeed_leftSafe
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
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    LeftSafeRun outputWorkspaceArchiveReturnSeedMachine
      (init outputWorkspaceArchiveReturnSeedMachine rcf.tp)
      (prefixClock + 1 + runtimeArchiveReturnSeedClock rest) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hrestlen : rest.length = B - (t + 1) := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by
    rw [hrestlen]
    omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  obtain ⟨phys, a, b, hphys, hshape, harchive⟩ :=
    scheduledRuntimeRelativeOutput_archiveReturnSeed x w ht htnext
  have hRphys : R = phys.length + 2 := by
    simp [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      routeClock, rcf, R] at hphys
    rw [hphys]
  have hphys2 : 2 ≤ phys.length := by
    have hB : 2 ≤ B := by
      dsimp [B]
      omega
    simp [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      routeClock, rcf, R] at hphys
    rw [hphys]
    omega
  have hsArchive0 := runtimeArchiveReturnSeed_leftSafe_prefixed
    phys a b first more hphys2
  have hsArchive : LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, R, rcf.tp⟩
      (runtimeArchiveReturnSeedClock rest) := by
    rw [hshape, hRphys]
    change LeftSafeRun runtimeArchiveReturnSeedMachine
      ⟨runtimeArchiveReturnSeedMachine.start, phys.length + 2,
        phys ++ [a, b] ++ selectedTail rest⟩
      (runtimeArchiveReturnSeedClock rest)
    rw [hrest]
    exact hsArchive0
  have hloc := scheduledRuntimeRelativeOutput_physicalWorkspaceTailLocate
    x w ht htnext
  have hsLoc := scheduled_outputWorkspaceTailLocator_leftSafe
    x w ht htnext
  have hhArchive : runtimeArchiveReturnSeedMachine.halt
      (run runtimeArchiveReturnSeedMachine
        (runtimeArchiveReturnSeedClock rest)
        ⟨runtimeArchiveReturnSeedMachine.start, R, rcf.tp⟩).st = true := by
    rw [harchive]
    rfl
  simpa [outputWorkspaceArchiveReturnSeedMachine, B, schedule, preBlocks,
    l, bits, rest, pre, out, out', T, n, M, routeClock, rcf,
    locateClock, tailClock, prefixClock, R] using
    headSeq_leftSafe outputWorkspaceTailLocatorMachine
      runtimeArchiveReturnSeedMachine rcf.tp rcf.tp prefixClock
      (runtimeArchiveReturnSeedClock rest) R
      (Sum.inr RuntimeWorkspaceTailLocatorState.done)
      (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
        n, M, routeClock, rcf, locateClock, tailClock, prefixClock, R]
        using hloc)
      rfl
      (by simpa [B, schedule, preBlocks, l, out, out', T, n, M,
        routeClock, rcf, locateClock, tailClock, prefixClock] using hsLoc)
      hsArchive hhArchive

set_option maxHeartbeats 1000000 in
/-- The complete scheduled physical controller exports one clock carrying
both its exact halted unary endpoint and its full left-safety certificate. -/
theorem scheduled_outputWorkspaceArchiveReturnUnaryRebase_safeRun
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
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let seedClock := runtimeArchiveReturnSeedClock rest
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ base unaryClock,
      run outputWorkspaceArchiveReturnUnaryRebaseMachine
          ((prefixClock + 1 + seedClock) + 1 + unaryClock)
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
          R + (selectedTail rest).length,
          base ++ [false, true, false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ ∧
      LeftSafeRun outputWorkspaceArchiveReturnUnaryRebaseMachine
        (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp)
        ((prefixClock + 1 + seedClock) + 1 + unaryClock) := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let lookupClock := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T lookupClock
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 + (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  obtain ⟨phys, a, b, hphys, hshape, hseedrun⟩ :=
    scheduledRuntimeRelativeOutput_physicalArchiveReturnSeed x w ht htnext
  have hphys' : phys.length = R - 2 := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, R] using hphys
  have hrestlen : rest.length = B - (t + 1) := by
    have hslen : schedule.length = B := by
      simp [schedule, B, literalTapeSchedule]
    simp [rest, hslen]
  have hrestpos : 0 < rest.length := by
    rw [hrestlen]
    omega
  obtain ⟨first, more, hrest⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos hrestpos)
  have hfit0 := scheduled_unaryRebaseScratch_fits_afterOutput x w ht
  have hfit : 2 * rest.length + 4 ≤ phys.length := by
    have hs : 2 * rest.length + 4 ≤ pre.length + 2 * bits.length + 4 := by
      have hs0 : 2 * rest.length + 4 ≤ pre.length + 2 * bits.length + 2 := by
        simpa [B, schedule, preBlocks, bits, rest, pre] using hfit0
      omega
    have hphysLower : pre.length + 2 * bits.length + 4 ≤ phys.length := by
      rw [hphys']
      omega
    exact le_trans hs hphysLower
  obtain ⟨base, unaryClock, hbasePrefix, hbase, hunary, hsunary⟩ :=
    runtimeUnaryRebase_physical_safeRun phys first more
      (by simpa [hrest] using hfit)
  have hR : phys.length + 2 = R := by
    have hRge : 2 ≤ R := by simp [R]
    rw [hphys']
    exact Nat.sub_add_cancel hRge
  have hunary' : run runtimeUnaryRebaseMachine unaryClock
      ⟨RuntimeUnaryRebaseState.init1, R,
        phys ++ [false, true] ++ selectedTail rest⟩ =
    ⟨RuntimeUnaryRebaseState.done,
      R + (selectedTail rest).length,
      base ++ [false, true, false, true] ++
        sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [hrest, hR] using hunary
  have hsunary' : LeftSafeRun runtimeUnaryRebaseMachine
      ⟨RuntimeUnaryRebaseState.init1, R,
        phys ++ [false, true] ++ selectedTail rest⟩ unaryClock := by
    simpa [hrest, hR] using hsunary
  have hsseed := scheduled_outputWorkspaceArchiveReturnSeed_leftSafe
    x w ht htnext
  have hsfull := outputWorkspaceArchiveReturnUnaryRebase_leftSafe_of_runs
    rcf.tp (phys ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true, false, true] ++
      sourceSelectorInput rest.length 0 rest)
    (prefixClock + 1 + seedClock) unaryClock R
    (R + (selectedTail rest).length)
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hseedrun)
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock] using hsseed)
    hunary' hsunary'
  have hjoin := headSeq_run outputWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine rcf.tp
    (phys ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true, false, true] ++
      sourceSelectorInput rest.length 0 rest)
    (prefixClock + 1 + seedClock) unaryClock R
    (R + (selectedTail rest).length)
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    RuntimeUnaryRebaseState.done
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hseedrun)
    rfl hunary' rfl
  refine ⟨base, unaryClock, ?_, ?_⟩
  · convert hjoin using 1 <;> simp [outputWorkspaceArchiveReturnUnaryRebaseMachine,
      outputWorkspaceArchiveReturnUnaryRebaseDone,
      B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R, hrestlen, Nat.add_assoc] <;> omega
  · exact hsfull

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
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.scheduled_outputWorkspaceTailLocator_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReverse_canonical_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeRebaseSeed_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReturnSeed_leftSafe_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeArchiveReturnSeed_leftSafe_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_init_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_boundaryOrigin_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_extendFrontier_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_freshFirstBlock_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_processedArchive_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_markReturn_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_visit_nonfinal_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_visit_final_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_visits_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_complete_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_physical_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.outputWorkspaceArchiveReturnUnaryRebase_leftSafe_of_runs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.scheduled_outputWorkspaceArchiveReturnSeed_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.scheduled_outputWorkspaceArchiveReturnUnaryRebase_safeRun
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety.runtimeUnaryRebase_restore_leftSafe
