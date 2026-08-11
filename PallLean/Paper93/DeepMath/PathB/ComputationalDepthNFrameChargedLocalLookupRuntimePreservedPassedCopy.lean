import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRoundEntryAdapter

/-!
# Preserve the canonical passed block across `masterM`

The completed workspace loses the original lookup payload.  `masterM` does,
however, preserve every bit after its fixed scratch trailer.  This module
certifies the corrected upstream layout: place one canonical passed-block
copy after that trailer before lookup.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

def preservedPassedTrailer (bits tail : List Bool) : List Bool :=
  [true, false, false, true] ++ List.replicate bits.length true ++
    flattenPairs (passedSourceBlock bits) ++ tail

/-- The appended canonical block and archive tail are untouched by lookup. -/
theorem masterM_literal_preservedPassed_drop (w : List Bool) (l : Lit)
    (tail : List Bool) :
    let bits := literalLookupTape w l
    let trailer := preservedPassedTrailer bits tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    cf.tp.drop (2 * bits.length + 4) =
      flattenPairs (passedSourceBlock bits) ++ tail := by
  dsimp only
  let bits := literalLookupTape w l
  let copy := flattenPairs (passedSourceBlock bits)
  let trailer := preservedPassedTrailer bits tail
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  have hdrop : cf.tp.drop bits.length = trailer := by
    simpa [bits, trailer, cf] using masterM_literal_trailer w l trailer
  rw [show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
    ← List.drop_drop, hdrop]
  change List.drop (4 + bits.length) trailer = copy ++ tail
  simp [trailer, preservedPassedTrailer, copy]

set_option maxHeartbeats 4000000 in
/-- Exact corrected terminal layout: completed workspace, preserved canonical
passed block, then the untouched later archive. -/
theorem masterM_literal_workspace_preservedPassed_decomposition
    (w : List Bool) (l : Lit) (tail : List Bool) :
    let bits := literalLookupTape w l
    let copy := flattenPairs (passedSourceBlock bits)
    let trailer := preservedPassedTrailer bits tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let m := 2 * l.1 + 2
    let n := 2 * l.1 + 4
    ∃ value,
      cf.tp = flattenPairs (runtimeWorkspaceFrontPairs value m n) ++
        copy ++ tail := by
  dsimp only
  let bits := literalLookupTape w l
  let copy := flattenPairs (passedSourceBlock bits)
  let trailer := preservedPassedTrailer bits tail
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  obtain ⟨value, hfront⟩ :=
    masterM_literal_workspaceFrontPairs w l (copy ++ tail)
  have hdrop : cf.tp.drop (2 * bits.length + 4) = copy ++ tail := by
    simpa [bits, copy, trailer, cf] using
      masterM_literal_preservedPassed_drop w l tail
  refine ⟨value, ?_⟩
  rw [← List.take_append_drop (2 * bits.length + 4) cf.tp,
    hdrop]
  simpa [bits, copy, trailer, cf, m, n] using hfront

#print axioms masterM_literal_preservedPassed_drop
#print axioms masterM_literal_workspace_preservedPassed_decomposition

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
