import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceTailLocator

/-!
# Physical post-cashout future-archive discovery

The completed-workspace tail locator is translation invariant: it never
resets and never moves left.  This file transports its canonical run behind
an arbitrary physical prefix, joins it head-preservingly after the physical
workspace locator, and then hands the discovered future-block head directly
to the fixed archive parser.  The resulting locator chain starts at physical
tape origin and reaches the blank pair after the untouched future archive
without receiving any semantic boundary as a machine parameter.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalWorkspace
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeWorkspaceTailLocator

/-- State-dependent lower bound on the tail parser's head. -/
def runtimeWorkspaceTailStateLower : RuntimeWorkspaceTailLocatorState → Nat
  | .boot0 => 0
  | .boot1 => 1
  | .boot2 => 2
  | .boot3 => 3
  | .boot4 => 4
  | .boot5 => 5
  | .corridorLo => 6
  | .corridorHi _ => 7
  | .paddingLo => 8
  | .paddingHi _ => 9
  | .done => 0

/-- The parser never moves left of the lower bound associated with its
control phase.  In particular, its final one-cell backup cannot cross origin. -/
theorem runtimeWorkspaceTailLocator_head_lower
    (T : List Bool) (i : Nat) :
    runtimeWorkspaceTailStateLower
        (run runtimeWorkspaceTailLocatorMachine i
          (init runtimeWorkspaceTailLocatorMachine T)).st ≤
      (run runtimeWorkspaceTailLocatorMachine i
        (init runtimeWorkspaceTailLocatorMachine T)).hd := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [run_succ]
      generalize hc : run runtimeWorkspaceTailLocatorMachine i
        (init runtimeWorkspaceTailLocatorMachine T) = c at ih ⊢
      by_cases hh : runtimeWorkspaceTailLocatorMachine.halt c.st = true
      · rw [step_of_halted runtimeWorkspaceTailLocatorMachine hh]
        exact ih
      · rcases c with ⟨s, p, tp⟩
        cases s <;>
          simp [step, runtimeWorkspaceTailLocatorMachine, moveHead]
            at hh ih ⊢
        all_goals try split_ifs at ⊢
        all_goals simp_all [runtimeWorkspaceTailStateLower] <;> omega

/-- The canonical tail execution is prefix safe.  Its only left move is the
final one-cell backup onto the recognized future header, after the six-cell
boot and the nonempty corridor/trailer traversal. -/
theorem runtimeWorkspaceTailLocator_prefixSafe
    (T : List Bool) (n : Nat) :
    PrefixSafeRun runtimeWorkspaceTailLocatorMachine
      (init runtimeWorkspaceTailLocatorMachine T) n := by
  intro i hi
  let c := run runtimeWorkspaceTailLocatorMachine i
    (init runtimeWorkspaceTailLocatorMachine T)
  constructor
  · intro _
    cases c.st <;>
      simp [runtimeWorkspaceTailLocatorMachine] <;> split_ifs <;> simp
  · intro _ hleft
    have hlower := runtimeWorkspaceTailLocator_head_lower T i
    generalize hc : run runtimeWorkspaceTailLocatorMachine i
      (init runtimeWorkspaceTailLocatorMachine T) = cfg at hlower hleft ⊢
    rcases cfg with ⟨s, p, tp⟩
    cases s <;>
      simp [runtimeWorkspaceTailLocatorMachine] at hleft
    all_goals simp [runtimeWorkspaceTailStateLower] at hlower ⊢
    all_goals omega

/-- The canonical workspace-tail execution transports unchanged behind an
arbitrary physical prefix. -/
theorem masterM_literal_workspaceTailLocate_prefixed
    (phys w : List Bool) (l : Lit)
    (next : List Bool) (more : List (List Bool)) :
    let bits := literalLookupTape w l
    let rest := next :: more
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ selectedTail rest
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    run runtimeWorkspaceTailLocatorMachine (8 * l.1 + 22)
        ⟨RuntimeWorkspaceTailLocatorState.boot0, phys.length,
          phys ++ cf.tp⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done,
        phys.length + 2 * bits.length + 4, phys ++ cf.tp⟩ := by
  dsimp only
  let bits := literalLookupTape w l
  let rest := next :: more
  let trailer := [true, false, false, true] ++
    List.replicate bits.length true ++ selectedTail rest
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hlocal := masterM_literal_workspaceTailLocate w l next more
  have hshift := run_shiftCfg runtimeWorkspaceTailLocatorMachine phys
    (init runtimeWorkspaceTailLocatorMachine cf.tp) (8 * l.1 + 22)
    (runtimeWorkspaceTailLocator_prefixSafe cf.tp (8 * l.1 + 22))
  have hlocal' : run runtimeWorkspaceTailLocatorMachine (8 * l.1 + 22)
      (init runtimeWorkspaceTailLocatorMachine cf.tp) =
      ⟨RuntimeWorkspaceTailLocatorState.done,
        2 * bits.length + 4, cf.tp⟩ := by
    simpa [bits, rest, trailer, cf] using hlocal
  rw [hlocal'] at hshift
  simpa [shiftCfg] using hshift

/-- The joined origin-to-workspace parser hands its discovered head directly
to the completed-workspace tail parser. -/
def outputWorkspaceTailLocatorMachine : Machine :=
  headSeqMachine outputWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine

/-- On every genuine nonterminal post-cashout tape, the tail parser begins at
the operationally discovered workspace head and reaches the first untouched
future source block without changing the tape. -/
theorem scheduledRuntimeRelativeOutput_workspaceTailLocate
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let W := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length
    let R := W + 2 * bits.length + 4
    run runtimeWorkspaceTailLocatorMachine (8 * l.1 + 22)
        ⟨RuntimeWorkspaceTailLocatorState.boot0, W, rcf.tp⟩ =
      ⟨RuntimeWorkspaceTailLocatorState.done, R, rcf.tp⟩ := by
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
  have hphysical : rcf.tp = (outputCap B out' ++ pre) ++ mcf.tp := by
    rw [htp, hcf]
    simp [List.append_assoc]
  have hout : out'.length = t + 1 := by
    dsimp [out']
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using htnext.le)]
  have houtle : out'.length ≤ B := by rw [hout]; exact htnext.le
  have hprefLen : (outputCap B out' ++ pre).length = W := by
    rw [List.length_append, outputCap_length B out' houtle]
  have htail := masterM_literal_workspaceTailLocate_prefixed
    (outputCap B out' ++ pre) w l (schedule.getD (t + 1) [])
      (schedule.drop (t + 2))
  have hrest : rest = schedule.getD (t + 1) [] :: schedule.drop (t + 2) := by
    dsimp [rest]
    rw [List.drop_eq_getElem_cons (by simpa [hslen] using htnext)]
    rw [← List.getD_eq_getElem schedule [] (by simpa [hslen] using htnext)]
  rw [hphysical]
  simpa [bits, trailer, mcf, hrest, hprefLen, W, R, Nat.add_assoc] using htail

/-- The complete fixed locator from physical origin to the future-block head. -/
theorem scheduledRuntimeRelativeOutput_physicalWorkspaceTailLocate
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
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
    let R := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length +
      2 * bits.length + 4
    run outputWorkspaceTailLocatorMachine
        (locateClock + 1 + tailClock)
        (init outputWorkspaceTailLocatorMachine rcf.tp) =
      ⟨Sum.inr RuntimeWorkspaceTailLocatorState.done, R, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
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
  let W := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length
  let R := W + 2 * bits.length + 4
  have h1 := scheduledRuntimeRelativeOutput_physicalWorkspaceLocate
    x w ht htnext
  have h2 := scheduledRuntimeRelativeOutput_workspaceTailLocate
    x w ht htnext
  exact headSeq_run outputWorkspaceLocatorMachine
    runtimeWorkspaceTailLocatorMachine rcf.tp rcf.tp rcf.tp
    locateClock tailClock W R
    (Sum.inr RuntimeWorkspaceLocatorState.done)
    RuntimeWorkspaceTailLocatorState.done
    (by simpa [B, schedule, preBlocks, l, bits, out, out', T, n, M,
      routeClock, rcf, locateClock, W] using h1)
    rfl
    (by simpa [B, schedule, preBlocks, l, bits, out, out', T, n, M,
      routeClock, rcf, W, R, tailClock] using h2)
    rfl

/-- The fixed origin parser, workspace-tail parser, and archive parser form
one head-preserving locator chain. -/
def outputWorkspaceArchiveLocatorMachine : Machine :=
  headSeqMachine outputWorkspaceTailLocatorMachine
    runtimeArchiveLocatorMachine

/-- Starting at physical origin on the genuine post-cashout tape, the fixed
locator chain crosses the completed workspace and the complete untouched
future archive and halts immediately after its terminal blank pair. -/
theorem scheduledRuntimeRelativeOutput_physicalArchiveLocate
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) routeClock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let prefixClock := outputSourceLocatorClock B out' + 1 +
      ((selectedPrefix (B - t) preBlocks).length + 2) + 1 +
      (8 * l.1 + 22)
    let R := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length +
      2 * bits.length + 4
    run outputWorkspaceArchiveLocatorMachine
        (prefixClock + 1 + runtimeArchiveLocatorClock rest)
        (init outputWorkspaceArchiveLocatorMachine rcf.tp) =
      ⟨Sum.inr RuntimeArchiveLocatorState.done,
        R + (selectedTail rest).length + 2, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) routeClock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let prefixClock := outputSourceLocatorClock B out' + 1 +
    ((selectedPrefix (B - t) preBlocks).length + 2) + 1 +
    (8 * l.1 + 22)
  let R := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length +
    2 * bits.length + 4
  have h1 := scheduledRuntimeRelativeOutput_physicalWorkspaceTailLocate
    x w ht htnext
  have h2 := scheduledRuntimeRelativeOutput_archiveLocate x w ht htnext
  exact headSeq_run outputWorkspaceTailLocatorMachine
    runtimeArchiveLocatorMachine rcf.tp rcf.tp rcf.tp
    prefixClock (runtimeArchiveLocatorClock rest) R
    (R + (selectedTail rest).length + 2)
    (Sum.inr RuntimeWorkspaceTailLocatorState.done)
    RuntimeArchiveLocatorState.done
    (by exact h1)
    rfl
    (by simpa [B, schedule, preBlocks, l, bits, rest, out, T, n, M,
      routeClock, rcf, R] using h2)
    rfl

/-- Cashout and the complete structural locator chain are one physical
machine.  The cashout handoff performs the sole intended reset to origin;
every subsequent parser handoff preserves the head discovered at runtime. -/
theorem scheduledRuntimeRelativeOutput_physicalArchiveCombined
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let out := (scheduledTruths x w).take t
    let out' := (scheduledTruths x w).take (t + 1)
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
    let routeClock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run M1 routeClock (init M1 (outputCap B out ++ T))
    let locateClock := outputSourceLocatorClock B out' + 1 +
      ((selectedPrefix (B - t) preBlocks).length + 2) + 1 +
      (8 * l.1 + 22) + 1 + runtimeArchiveLocatorClock rest
    let R := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length +
      2 * bits.length + 4
    let M := seqMachine M1 outputWorkspaceArchiveLocatorMachine
    run M (routeClock + 1 + locateClock)
        (init M (outputCap B out ++ T)) =
      ⟨Sum.inr (Sum.inr RuntimeArchiveLocatorState.done),
        R + (selectedTail rest).length + 2, rcf.tp⟩ := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let out := (scheduledTruths x w).take t
  let out' := (scheduledTruths x w).take (t + 1)
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M1 := acceptRouteMachine (runtimeRelativeOutputSourceMachine B)
  let routeClock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run M1 routeClock (init M1 (outputCap B out ++ T))
  let locateClock := outputSourceLocatorClock B out' + 1 +
    ((selectedPrefix (B - t) preBlocks).length + 2) + 1 +
    (8 * l.1 + 22) + 1 + runtimeArchiveLocatorClock rest
  let R := 2 * B + 2 + (selectedPrefix (B - t) preBlocks).length +
    2 * bits.length + 4
  have h1 : run M1 routeClock (init M1 (outputCap B out ++ T)) = rcf := rfl
  have hh1 : M1.halt rcf.st = true := by
    have hr := scheduledRuntimeRelativeOutputSourceRoute x w ht
    simpa [B, schedule, preBlocks, l, bits, rest, out, out', T, n, M1,
      routeClock, rcf] using hr.1
  have h2 := scheduledRuntimeRelativeOutput_physicalArchiveLocate
    x w ht htnext
  exact seq_run M1 outputWorkspaceArchiveLocatorMachine
    (outputCap B out ++ T) rcf.tp rcf.tp routeClock locateClock rcf.st rcf.hd
    (Sum.inr RuntimeArchiveLocatorState.done)
    (R + (selectedTail rest).length + 2)
    h1 hh1
    (by exact h2)
    rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive.masterM_literal_workspaceTailLocate_prefixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive.scheduledRuntimeRelativeOutput_physicalWorkspaceTailLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive.scheduledRuntimeRelativeOutput_physicalArchiveLocate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalArchive.scheduledRuntimeRelativeOutput_physicalArchiveCombined
