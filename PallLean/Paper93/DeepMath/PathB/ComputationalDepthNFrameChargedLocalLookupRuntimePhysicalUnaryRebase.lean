import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-!
# Physical fixed unary-rebase composition

This file joins the runtime-discovered archive seed endpoint to the fixed
archive-counted unary writer.  The only handoff is the ordinary
head-preserving transition of `headSeqMachine`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputSourceLocator
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeUnaryRebaseWriter

/-- One fixed controller from physical tape origin through archive discovery,
seed installation, archive-counted unary rebase, and restoration. -/
def outputWorkspaceArchiveReturnUnaryRebaseMachine : Machine :=
  headSeqMachine outputWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine

def outputWorkspaceArchiveReturnUnaryRebaseDone :
    outputWorkspaceArchiveReturnUnaryRebaseMachine.State := by
  unfold outputWorkspaceArchiveReturnUnaryRebaseMachine
  exact Sum.inr RuntimeUnaryRebaseState.done

/-- The unary frontier fits wholly inside the consumed source/workspace
region.  In particular, its two-cell-per-surviving-block scratch demand never
reaches left into the fixed-capacity truth output. -/
theorem scheduled_unaryRebaseScratch_fits_afterOutput
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let bits := literalLookupTape w (scheduledLiteral x t)
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    2 * rest.length + 2 ≤ pre.length + 2 * bits.length + 2 := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let bits := literalLookupTape w (scheduledLiteral x t)
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hrest : rest.length = B - (t + 1) := by
    simp [rest, hslen]
  have hbitsEq : bits.length = 4 * (scheduledLiteral x t).1 + 8 := by
    simp [bits, literalLookupTape,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.encode,
      signedLookupAssignment_length,
      PallLean.Paper93.DeepMath.PathB.CookLevinInP.double_length]
    ring
  have hbits : 8 ≤ bits.length := by omega
  rw [hrest]
  simp [selectedPrefix, selectedPrefixPairs]
  omega

/-- Prefix-exposing form of the physical unary-rebase theorem.  The writer's
untouched `base` is not merely length-correct: it is the literal leading
prefix of the incoming physical tape. -/
theorem runtimeUnaryRebase_run_physical_prefix
    (phys : List Bool) (bits : List Bool) (more : List (List Bool))
    (hfit : 2 * (bits :: more).length + 2 ≤ phys.length) :
    let R := phys.length + 2
    let T0 := phys ++ [false, true] ++ selectedTail (bits :: more)
    ∃ base n,
      base.IsPrefix phys ∧
      base.length = phys.length - (2 * (bits :: more).length + 2) ∧
      run runtimeUnaryRebaseMachine n
          ⟨RuntimeUnaryRebaseState.init1, R, T0⟩ =
        ⟨RuntimeUnaryRebaseState.done,
          R + (selectedTail (bits :: more)).length,
          base ++ [false, true] ++
            sourceSelectorInput (bits :: more).length 0 (bits :: more)⟩ := by
  dsimp only
  let L := 2 * (bits :: more).length + 2
  let p := phys.length - L
  let suffix := phys.drop p
  have hsuffix : suffix.length = 2 * (bits :: more).length + 2 := by
    simp only [suffix, List.length_drop]
    change phys.length - (phys.length - L) = L
    omega
  obtain ⟨scratch, a, b, hs, hscratch⟩ := split_last_two hsuffix
  let base := phys.take p
  have hphys : phys = base ++ scratch ++ [a, b] := by
    have H := List.take_append_drop p phys
    rw [show phys.drop p = suffix by rfl, hs] at H
    simpa [base, List.append_assoc] using H.symm
  obtain ⟨n, hn⟩ := runtimeUnaryRebase_run_complete
    base scratch a b bits more hscratch
  refine ⟨base, n, ?_, ?_, ?_⟩
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
    have hout : base ++
          ([false, true] ++ zeroCopyRebasePrefix (bits :: more).length) ++
          selectedTail (bits :: more) =
        base ++ [false, true] ++
          sourceSelectorInput (bits :: more).length 0 (bits :: more) := by
      have hz := zeroCopyRebasePrefix_archive (bits :: more)
      simpa [List.append_assoc] using
        congrArg (fun X => base ++ [false, true] ++ X) hz
    rw [hout] at hn'
    rw [hR, hT]
    exact hn'

set_option maxHeartbeats 1000000 in
theorem scheduledRuntimeRelativeOutput_physicalUnaryRebase
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
    let locateClock := outputSourceLocatorClock B out' + 1 +
      (pre.length + 2)
    let tailClock := 8 * l.1 + 22
    let prefixClock := locateClock + 1 + tailClock
    let seedClock := runtimeArchiveReturnSeedClock rest
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    ∃ residue unaryClock,
      run outputWorkspaceArchiveReturnUnaryRebaseMachine
          ((prefixClock + 1 + seedClock) + 1 + unaryClock)
          (init outputWorkspaceArchiveReturnUnaryRebaseMachine rcf.tp) =
        ⟨outputWorkspaceArchiveReturnUnaryRebaseDone,
          R + (selectedTail rest).length,
          outputCap B out' ++ residue ++ [false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ := by
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
  let locateClock := outputSourceLocatorClock B out' + 1 +
    (pre.length + 2)
  let tailClock := 8 * l.1 + 22
  let prefixClock := locateClock + 1 + tailClock
  let seedClock := runtimeArchiveReturnSeedClock rest
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hseed := scheduledRuntimeRelativeOutput_physicalArchiveReturnSeed
    x w ht htnext
  obtain ⟨phys, a, b, hphys, hshape, hseedrun⟩ := hseed
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
  have hfit : 2 * rest.length + 2 ≤ phys.length := by
    have hs : 2 * rest.length + 2 ≤ pre.length + 2 * bits.length + 4 := by
      have hs0 : 2 * rest.length + 2 ≤
          pre.length + 2 * bits.length + 2 := by
        simpa [B, schedule, preBlocks, bits, rest, pre] using hfit0
      omega
    have hphysLower : pre.length + 2 * bits.length + 4 ≤ phys.length := by
      rw [hphys']
      omega
    exact le_trans hs hphysLower
  have hunaryPack : ∃ base unaryClock,
      base.IsPrefix phys ∧
      base.length = phys.length - (2 * rest.length + 2) ∧
      run runtimeUnaryRebaseMachine unaryClock
          ⟨RuntimeUnaryRebaseState.init1, phys.length + 2,
            phys ++ [false, true] ++ selectedTail rest⟩ =
        ⟨RuntimeUnaryRebaseState.done,
          phys.length + 2 + (selectedTail rest).length,
          base ++ [false, true] ++
            sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [hrest] using runtimeUnaryRebase_run_physical_prefix phys first more (by
      simpa [hrest] using hfit)
  obtain ⟨base, unaryClock, hbasePrefix, hbase, hunary⟩ := hunaryPack
  have hR : phys.length + 2 = R := by
    have hRge : 2 ≤ R := by
      simp only [R]
      omega
    rw [hphys']
    exact Nat.sub_add_cancel hRge
  have hunary' : run runtimeUnaryRebaseMachine unaryClock
      ⟨RuntimeUnaryRebaseState.init1, R,
        phys ++ [false, true] ++ selectedTail rest⟩ =
      ⟨RuntimeUnaryRebaseState.done,
        R + (selectedTail rest).length,
        base ++ [false, true] ++ sourceSelectorInput rest.length 0 rest⟩ := by
    simpa [hrest, hR] using hunary
  let cf := run sourceRuntimeLookupCore lookupClock
    (init sourceRuntimeLookupCore T)
  have hroute := scheduledRuntimeRelativeOutputSourceRoute x w ht
  have hrouteTape : rcf.tp = outputCap B out' ++ cf.tp := by
    have hs := scheduledTruths_take_succ x w ht
    simpa [B, schedule, preBlocks, l, out, out', T, lookupClock, cf, M,
      routeClock, rcf, hs] using hroute.2
  have houtlen : out'.length = t + 1 := by
    dsimp [out']
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using htnext.le)]
  have hcaplen : (outputCap B out').length = 2 * B + 2 :=
    outputCap_length B out' (by omega)
  have hcapPhys : (outputCap B out').length ≤ phys.length := by
    rw [hcaplen, hphys']
    simp only [R]
    omega
  have houtputPhys : (outputCap B out').IsPrefix phys := by
    rw [List.prefix_iff_eq_take]
    have heq : phys ++ [a, b] ++ selectedTail rest =
        outputCap B out' ++ cf.tp := hshape.symm.trans hrouteTape
    have htake := congrArg (List.take (outputCap B out').length) heq
    rw [List.take_append_of_le_length (by simp; omega)] at htake
    rw [List.take_append_of_le_length hcapPhys] at htake
    simpa using htake.symm
  have hcapBase : (outputCap B out').length ≤ base.length := by
    have hscratch : (outputCap B out').length +
        (2 * rest.length + 2) ≤ phys.length := by
      rw [hcaplen, hphys']
      have hs0 : 2 * rest.length + 2 ≤
          pre.length + 2 * bits.length + 2 := by
        simpa [B, schedule, preBlocks, bits, rest, pre] using hfit0
      simp only [R]
      omega
    rw [hbase]
    omega
  have houtputBase : (outputCap B out').IsPrefix base := by
    rw [List.prefix_iff_eq_take] at houtputPhys ⊢
    calc
      outputCap B out' = phys.take (outputCap B out').length := houtputPhys
      _ = base.take (outputCap B out').length := by
        obtain ⟨tail, htail⟩ := hbasePrefix
        rw [← htail, List.take_append_of_le_length hcapBase]
  obtain ⟨residue, hbaseEq⟩ := houtputBase
  have hjoin := headSeq_run outputWorkspaceArchiveReturnSeedMachine
    runtimeUnaryRebaseMachine rcf.tp
    (phys ++ [false, true] ++ selectedTail rest)
    (base ++ [false, true] ++ sourceSelectorInput rest.length 0 rest)
    (prefixClock + 1 + seedClock) unaryClock R
    (R + (selectedTail rest).length)
    (Sum.inr (Sum.inr RuntimeRebaseSeedState.done))
    RuntimeUnaryRebaseState.done
    (by simpa [B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
      lookupClock, M, routeClock, rcf, locateClock, tailClock,
      prefixClock, seedClock, R] using hseedrun)
    rfl hunary' rfl
  refine ⟨residue, unaryClock, ?_⟩
  simpa [outputWorkspaceArchiveReturnUnaryRebaseMachine,
    outputWorkspaceArchiveReturnUnaryRebaseDone,
    B, schedule, preBlocks, l, bits, rest, pre, out, out', T,
    lookupClock, M, routeClock, rcf, locateClock, tailClock,
    prefixClock, seedClock, R, hrestlen, hbaseEq,
    List.append_assoc] using hjoin

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase.scheduled_unaryRebaseScratch_fits_afterOutput
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase.runtimeUnaryRebase_run_physical_prefix
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalUnaryRebase.scheduledRuntimeRelativeOutput_physicalUnaryRebase
