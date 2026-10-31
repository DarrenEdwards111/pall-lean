import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactCompositionSafety

/-!
# Universal repair from a duplicated passed source

The completed `masterM` workspace and the adjacent preserved passed block
contain the same number of pairs.  This module certifies the data-independent
physical schedule which clears the former and bubbles the latter left into the
vacated span.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedRepair

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeArchiveReturnWriter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePhysicalLeftSafety
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactChain
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactComposition
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-- Exact physical plan for replacing an arbitrary pair-aligned completed
workspace by an adjacent equally long preserved block. -/
structure RuntimeDuplicatedRepairCertificate
    (retained : List Bool) (old kept : List (Bool × Bool))
    (tail : List Bool) : Prop where
  sameLength : old.length = kept.length
  positive : 0 < old.length
  clearRun :
    run runtimeCompactClearLoopMachine (2 * old.length)
        ⟨runtimeCompactClearLoopMachine.start, retained.length,
          retained ++ flattenPairs old ++ flattenPairs kept ++ tail⟩ =
      ⟨(), retained.length + 2 * old.length,
        retained ++ List.replicate (2 * old.length) false ++
          flattenPairs kept ++ tail⟩
  clearSafe : LeftSafeRun runtimeCompactClearLoopMachine
    ⟨runtimeCompactClearLoopMachine.start, retained.length,
      retained ++ flattenPairs old ++ flattenPairs kept ++ tail⟩
    (2 * old.length)
  rewindRun :
    run runtimeCompactRewindMachine 2
        ⟨runtimeCompactRewindMachine.start,
          retained.length + 2 * old.length,
          retained ++ List.replicate (2 * old.length) false ++
            flattenPairs kept ++ tail⟩ =
      ⟨(), retained.length + 2 * (old.length - 1),
        retained ++ List.replicate (2 * old.length) false ++
          flattenPairs kept ++ tail⟩
  rewindSafe : LeftSafeRun runtimeCompactRewindMachine
    ⟨runtimeCompactRewindMachine.start,
      retained.length + 2 * old.length,
      retained ++ List.replicate (2 * old.length) false ++
        flattenPairs kept ++ tail⟩ 2
  shift : RuntimeCompactAllPasses retained kept tail old.length

/-- Clearing, the two-cell rewind, and every bubble pass are supplied solely
from the two equal spans.  Neither payload is compiled into finite control. -/
theorem runtimeDuplicatedRepair_certificate
    (retained tail : List Bool) (old kept : List (Bool × Bool))
    (hlen : old.length = kept.length) (hpos : 0 < old.length) :
    RuntimeDuplicatedRepairCertificate retained old kept tail := by
  have hflat : (flattenPairs old).length = 2 * old.length :=
    flattenPairs_length old
  have hc := runtimeCompactClearLoop_run retained (flattenPairs old)
    (flattenPairs kept ++ tail)
  have hcs := runtimeCompactClearLoop_leftSafe retained (flattenPairs old)
    (flattenPairs kept ++ tail)
  let pre := retained ++ List.replicate (2 * (old.length - 1)) false
  let suffix := [false, false] ++ flattenPairs kept ++ tail
  have hr := runtimeCompactRewind_run pre suffix 2
  have hrs := runtimeCompactRewind_leftSafe pre suffix 2
  have hmul : 2 * (old.length - 1) + 2 = 2 * old.length := by omega
  have htape : pre ++ suffix =
      retained ++ List.replicate (2 * old.length) false ++
        flattenPairs kept ++ tail := by
    unfold pre suffix
    rw [List.append_assoc]
    have hz : List.replicate (2 * (old.length - 1)) false ++
        [false, false] = List.replicate (2 * old.length) false := by
      rw [show [false, false] = List.replicate 2 false by rfl]
      rw [← List.replicate_add, hmul]
    have hz' := congrArg
      (fun z => retained ++ z ++ flattenPairs kept ++ tail) hz
    simpa [List.append_assoc] using hz'
  have hhead : retained.length + 2 * (old.length - 1) + 2 =
      retained.length + 2 * old.length := by omega
  refine ⟨hlen, hpos, ?_, ?_, ?_, ?_,
    runtimeCompactAllPasses_certificate retained tail kept hpos⟩
  · simpa [hflat, List.append_assoc] using hc
  · simpa [hflat, List.append_assoc] using hcs
  · simpa [pre, htape, hhead] using hr
  · simpa [pre, htape, hhead] using hrs

/-! ## One-machine exact composition -/

/-- Exact-clock composition of the certified clear, one-pair rewind, and
complete shift schedule.  This is the concrete physical handoff used below;
the clocks are proof indices and the three underlying controllers remain the
fixed clear, rewind, and bubble machines. -/
def runtimeDuplicatedRepairMachine
    (old kept : List (Bool × Bool)) : Machine :=
  headSeqMachine
    (exactClockMachine runtimeCompactClearLoopMachine (2 * old.length))
    (headSeqMachine
      (exactClockMachine runtimeCompactRewindMachine 2)
      (runtimeCompactPassScheduleMachine kept old.length))

def runtimeDuplicatedRepairClock
    (old kept : List (Bool × Bool)) : Nat :=
  2 * old.length + 1 +
    (2 + 1 + runtimeCompactPassScheduleClock kept old.length)

/-- The complete equal-span repair is a single genuinely halting nested
machine run with the preserved block in the old workspace position. -/
theorem runtimeDuplicatedRepairMachine_run
    (retained tail : List Bool) (old kept : List (Bool × Bool))
    (c : RuntimeDuplicatedRepairCertificate retained old kept tail) :
    ∃ s : (runtimeDuplicatedRepairMachine old kept).State,
      run (runtimeDuplicatedRepairMachine old kept)
          (runtimeDuplicatedRepairClock old kept)
          ⟨(runtimeDuplicatedRepairMachine old kept).start,
            retained.length,
            retained ++ flattenPairs old ++ flattenPairs kept ++ tail⟩ =
        ⟨s, retained.length + 2 * kept.length,
          retained ++ flattenPairs kept ++
            List.replicate (2 * old.length) false ++ tail⟩ ∧
      (runtimeDuplicatedRepairMachine old kept).halt s = true := by
  let T0 := retained ++ flattenPairs old ++ flattenPairs kept ++ tail
  let Tclear := retained ++ List.replicate (2 * old.length) false ++
    flattenPairs kept ++ tail
  let Tfinal := retained ++ flattenPairs kept ++
    List.replicate (2 * old.length) false ++ tail
  let clearM := exactClockMachine runtimeCompactClearLoopMachine
    (2 * old.length)
  let rewindM := exactClockMachine runtimeCompactRewindMachine 2
  let passM := runtimeCompactPassScheduleMachine kept old.length
  have hc := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * old.length) retained.length (retained.length + 2 * old.length)
    T0 Tclear () (by intro; rfl) (by simpa [T0, Tclear] using c.clearRun)
  have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
    2 (retained.length + 2 * old.length)
    (retained.length + 2 * (old.length - 1)) Tclear Tclear ()
    (by intro; rfl) (by simpa [Tclear] using c.rewindRun)
  obtain ⟨spass, hp, hpHalt⟩ :=
    runtimeCompactAllPasses_machine_run retained tail kept c.shift
  have hp' : run passM (runtimeCompactPassScheduleClock kept old.length)
      ⟨passM.start, retained.length + 2 * (old.length - 1), Tclear⟩ =
    ⟨spass, retained.length + 2 * kept.length, Tfinal⟩ := by
    simpa [passM, Tclear, Tfinal] using hp
  have hright := headSeq_run_at rewindM passM Tclear Tclear Tfinal
    (retained.length + 2 * old.length) 2
    (runtimeCompactPassScheduleClock kept old.length)
    (retained.length + 2 * (old.length - 1))
    (retained.length + 2 * kept.length)
    (⟨2, by omega⟩, ()) spass hr
    (exactClockMachine_halt_at _ _ _) hp' hpHalt
  have hall := headSeq_run_at clearM (headSeqMachine rewindM passM)
    T0 Tclear Tfinal retained.length (2 * old.length)
    (2 + 1 + runtimeCompactPassScheduleClock kept old.length)
    (retained.length + 2 * old.length)
    (retained.length + 2 * kept.length)
    (⟨2 * old.length, by omega⟩, ()) (Sum.inr spass)
    hc (exactClockMachine_halt_at _ _ _) hright
    (by simpa [headSeqMachine] using hpHalt)
  refine ⟨Sum.inr (Sum.inr spass), ?_, ?_⟩
  · simpa [runtimeDuplicatedRepairMachine,
      runtimeDuplicatedRepairClock, clearM, rewindM, passM,
      T0, Tclear, Tfinal, Nat.add_assoc] using hall
  · simpa [runtimeDuplicatedRepairMachine, headSeqMachine,
      rewindM, passM] using hpHalt

/-- The exact outer repair composition stays at or to the right of the
physical origin for precisely the same clock as its exact run theorem. -/
theorem runtimeDuplicatedRepairMachine_leftSafe
    (retained tail : List Bool) (old kept : List (Bool × Bool))
    (c : RuntimeDuplicatedRepairCertificate retained old kept tail) :
    LeftSafeRun (runtimeDuplicatedRepairMachine old kept)
      ⟨(runtimeDuplicatedRepairMachine old kept).start, retained.length,
        retained ++ flattenPairs old ++ flattenPairs kept ++ tail⟩
      (runtimeDuplicatedRepairClock old kept) := by
  let T0 := retained ++ flattenPairs old ++ flattenPairs kept ++ tail
  let Tclear := retained ++ List.replicate (2 * old.length) false ++
    flattenPairs kept ++ tail
  let Tfinal := retained ++ flattenPairs kept ++
    List.replicate (2 * old.length) false ++ tail
  let clearM := exactClockMachine runtimeCompactClearLoopMachine
    (2 * old.length)
  let rewindM := exactClockMachine runtimeCompactRewindMachine 2
  let passM := runtimeCompactPassScheduleMachine kept old.length
  have hc := exactClockMachine_run_of_run runtimeCompactClearLoopMachine
    (2 * old.length) retained.length (retained.length + 2 * old.length)
    T0 Tclear () (by intro; rfl) (by simpa [T0, Tclear] using c.clearRun)
  have hcSafe : LeftSafeRun clearM
      ⟨clearM.start, retained.length, T0⟩ (2 * old.length) := by
    simpa [clearM, exactClockCfg, T0] using
      exactClockMachine_leftSafe runtimeCompactClearLoopMachine
        (2 * old.length)
        ⟨runtimeCompactClearLoopMachine.start, retained.length, T0⟩
        (by intro; rfl) (by simpa [T0] using c.clearSafe)
  have hr := exactClockMachine_run_of_run runtimeCompactRewindMachine
    2 (retained.length + 2 * old.length)
    (retained.length + 2 * (old.length - 1)) Tclear Tclear ()
    (by intro; rfl) (by simpa [Tclear] using c.rewindRun)
  have hrSafe : LeftSafeRun rewindM
      ⟨rewindM.start, retained.length + 2 * old.length, Tclear⟩ 2 := by
    simpa [rewindM, exactClockCfg, Tclear] using
      exactClockMachine_leftSafe runtimeCompactRewindMachine 2
        ⟨runtimeCompactRewindMachine.start,
          retained.length + 2 * old.length, Tclear⟩
        (by intro; rfl) (by simpa [Tclear] using c.rewindSafe)
  obtain ⟨spass, hp, hpHalt⟩ :=
    runtimeCompactAllPasses_machine_run retained tail kept c.shift
  have hp' : run passM (runtimeCompactPassScheduleClock kept old.length)
      ⟨passM.start, retained.length + 2 * (old.length - 1), Tclear⟩ =
    ⟨spass, retained.length + 2 * kept.length, Tfinal⟩ := by
    simpa [passM, Tclear, Tfinal] using hp
  have hpSafe : LeftSafeRun passM
      ⟨passM.start, retained.length + 2 * (old.length - 1), Tclear⟩
      (runtimeCompactPassScheduleClock kept old.length) := by
    simpa [passM, Tclear] using
      runtimeCompactAllPasses_machine_leftSafe retained tail kept c.shift
  have hright : LeftSafeRun (headSeqMachine rewindM passM)
      ⟨(headSeqMachine rewindM passM).start,
        retained.length + 2 * old.length, Tclear⟩
      (2 + 1 + runtimeCompactPassScheduleClock kept old.length) := by
    exact headSeq_leftSafe_at rewindM passM Tclear Tclear
      (retained.length + 2 * old.length) 2
      (runtimeCompactPassScheduleClock kept old.length)
      (retained.length + 2 * (old.length - 1))
      (⟨2, by omega⟩, ()) hr (exactClockMachine_halt_at _ _ _)
      hrSafe hpSafe (by rw [hp']; exact hpHalt)
  have hall := headSeq_leftSafe_at clearM
    (headSeqMachine rewindM passM) T0 Tclear retained.length
    (2 * old.length)
    (2 + 1 + runtimeCompactPassScheduleClock kept old.length)
    (retained.length + 2 * old.length)
    (⟨2 * old.length, by omega⟩, ()) hc
    (exactClockMachine_halt_at _ _ _) hcSafe hright
    (by
      rw [headSeq_run_at rewindM passM Tclear Tclear Tfinal
        (retained.length + 2 * old.length) 2
        (runtimeCompactPassScheduleClock kept old.length)
        (retained.length + 2 * (old.length - 1))
        (retained.length + 2 * kept.length) (⟨2, by omega⟩, ())
        spass hr (exactClockMachine_halt_at _ _ _) hp' hpHalt]
      simpa [headSeqMachine, passM] using hpHalt)
  simpa [runtimeDuplicatedRepairMachine, runtimeDuplicatedRepairClock,
    clearM, rewindM, passM, T0, Nat.add_assoc] using hall

/-- The preserved passed source is always nonempty, so the generic physical
repair plan applies to every completed scheduled lookup endpoint. -/
theorem scheduledDuplicated_repairCertificate (x w : List Bool)
    {t : Nat} (ht : t < (decodedLiterals x).length)
    (retained : List Bool) :
    let schedule := literalTapeSchedule x w
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let tail := flattenPairs (duplicatedSourceArchive rest)
    let trailer := preservedPassedTrailer bits tail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    ∃ value,
      let old := runtimeWorkspaceFrontPairs value
        (2 * l.1 + 2) (2 * l.1 + 4)
      let kept := passedSourceBlock bits
      retained ++ mcf.tp = retained ++ flattenPairs old ++
        flattenPairs kept ++ tail ∧
      RuntimeDuplicatedRepairCertificate retained old kept tail := by
  dsimp only
  obtain ⟨value, hlayout, hflat⟩ :=
    scheduledDuplicated_repairLayout x w ht retained
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let old := runtimeWorkspaceFrontPairs value
    (2 * l.1 + 2) (2 * l.1 + 4)
  let kept := passedSourceBlock bits
  have hlen : old.length = kept.length := by
    rw [flattenPairs_length, flattenPairs_length] at hflat
    change 2 * old.length = 2 * kept.length at hflat
    omega
  have hpos : 0 < old.length := by
    rw [hlen]
    simp [kept, passedSourceBlock]
  exact ⟨value, hlayout,
    runtimeDuplicatedRepair_certificate retained _ old kept hlen hpos⟩

#print axioms runtimeDuplicatedRepair_certificate
#print axioms runtimeDuplicatedRepairMachine_run
#print axioms runtimeDuplicatedRepairMachine_leftSafe
#print axioms scheduledDuplicated_repairCertificate

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedRepair
