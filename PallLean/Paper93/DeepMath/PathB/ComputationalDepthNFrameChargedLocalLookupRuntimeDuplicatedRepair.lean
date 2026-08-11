import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition

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
#print axioms scheduledDuplicated_repairCertificate

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeDuplicatedRepair
