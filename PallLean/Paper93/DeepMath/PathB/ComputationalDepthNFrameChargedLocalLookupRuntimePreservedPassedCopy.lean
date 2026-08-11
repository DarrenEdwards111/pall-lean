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

/-! ## Explicit fixed-controller boundary -/

/-- Two consecutive `00` pairs form a boundary word which cannot occur in a
completed workspace.  A single `00` may encode the selected false value, so
one pair would not be a sound delimiter. -/
def runtimePassedBoundaryMarker : List (Bool × Bool) :=
  [(false, false), (false, false)]

def markedPreservedPassedTrailer (bits tail : List Bool) : List Bool :=
  [true, false, false, true] ++ List.replicate bits.length true ++
    flattenPairs runtimePassedBoundaryMarker ++
      flattenPairs (passedSourceBlock bits) ++ tail

/-- The raw unmarked `11* ++ passedSourceBlock` seam is genuinely ambiguous:
moving one leading all-true payload pair into the workspace padding leaves the
physical suffix unchanged. -/
theorem unmarkedPassedBoundary_collision :
    List.replicate 1 (true, true) ++ passedSourceBlock [true] =
      List.replicate 2 (true, true) ++ passedSourceBlock [] := by
  rfl

/-- `masterM` preserves the explicit marker, canonical passed copy, and all
later archive data verbatim. -/
theorem masterM_literal_workspace_markedPassed_decomposition
    (w : List Bool) (l : Lit) (tail : List Bool) :
    let bits := literalLookupTape w l
    let marker := flattenPairs runtimePassedBoundaryMarker
    let copy := flattenPairs (passedSourceBlock bits)
    let trailer := markedPreservedPassedTrailer bits tail
    let cf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    let m := 2 * l.1 + 2
    let n := 2 * l.1 + 4
    ∃ value,
      cf.tp = flattenPairs (runtimeWorkspaceFrontPairs value m n) ++
        marker ++ copy ++ tail := by
  dsimp only
  let bits := literalLookupTape w l
  let marker := flattenPairs runtimePassedBoundaryMarker
  let copy := flattenPairs (passedSourceBlock bits)
  let trailer := markedPreservedPassedTrailer bits tail
  let cf := run masterM (literalLookupClock w l)
    (init masterM (bits ++ trailer))
  let m := 2 * l.1 + 2
  let n := 2 * l.1 + 4
  have htrailer : trailer = [true, false, false, true] ++
      List.replicate bits.length true ++ (marker ++ copy ++ tail) := by
    simp [trailer, marker, copy, markedPreservedPassedTrailer,
      List.append_assoc]
  have hcf : cf = run masterM (literalLookupClock w l)
      (init masterM (bits ++ ([true, false, false, true] ++
        List.replicate bits.length true ++ (marker ++ copy ++ tail)))) := by
    simp [cf, htrailer]
  obtain ⟨value, hfront⟩ :=
    masterM_literal_workspaceFrontPairs w l (marker ++ copy ++ tail)
  have hdrop0 : cf.tp.drop bits.length = trailer := by
    simpa [bits, trailer, cf] using masterM_literal_trailer w l trailer
  have hdrop : cf.tp.drop (2 * bits.length + 4) =
      marker ++ copy ++ tail := by
    rw [show 2 * bits.length + 4 = bits.length + (4 + bits.length) by omega,
      ← List.drop_drop, hdrop0]
    let front : List Bool :=
      [true, false, false, true] ++ List.replicate bits.length true
    rw [show trailer = front ++ (marker ++ copy ++ tail) by
      simp [trailer, front, marker, copy, markedPreservedPassedTrailer,
        List.append_assoc]]
    have hfrontlen : front.length = 4 + bits.length := by
      simp [front]
      omega
    rw [← hfrontlen,
      List.drop_append_of_le_length
        (l₁ := front) (l₂ := marker ++ copy ++ tail)
        (i := front.length) le_rfl]
    simp
  refine ⟨value, ?_⟩
  calc
    cf.tp = cf.tp.take (2 * bits.length + 4) ++
        cf.tp.drop (2 * bits.length + 4) :=
      (List.take_append_drop (2 * bits.length + 4) cf.tp).symm
    _ = flattenPairs (runtimeWorkspaceFrontPairs value m n) ++
        marker ++ copy ++ tail := by
      rw [show cf.tp.take (2 * bits.length + 4) =
          flattenPairs (runtimeWorkspaceFrontPairs value m n) by
        rw [hcf]
        simpa [bits, m, n] using hfront, hdrop]
      simp [List.append_assoc]

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
  let front : List Bool :=
    [true, false, false, true] ++ List.replicate bits.length true
  rw [show trailer = front ++ (copy ++ tail) by
    simp [trailer, front, copy, preservedPassedTrailer, List.append_assoc]]
  have hfrontlen : front.length = 4 + bits.length := by
    simp [front]
    omega
  rw [← hfrontlen,
    List.drop_append_of_le_length (l₁ := front) (l₂ := copy ++ tail)
      (i := front.length) le_rfl]
  simp

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
  have htrailer : trailer = [true, false, false, true] ++
      List.replicate bits.length true ++ (copy ++ tail) := by
    simp [trailer, copy, preservedPassedTrailer, List.append_assoc]
  have hcf : cf = run masterM (literalLookupClock w l)
      (init masterM (bits ++ ([true, false, false, true] ++
        List.replicate bits.length true ++ (copy ++ tail)))) := by
    simp [cf, htrailer]
  have hfront' : cf.tp.take (2 * bits.length + 4) =
      flattenPairs (runtimeWorkspaceFrontPairs value m n) := by
    rw [hcf]
    exact hfront
  have hdrop : cf.tp.drop (2 * bits.length + 4) = copy ++ tail := by
    simpa [bits, copy, trailer, cf] using
      masterM_literal_preservedPassed_drop w l tail
  refine ⟨value, ?_⟩
  calc
    cf.tp = cf.tp.take (2 * bits.length + 4) ++
        cf.tp.drop (2 * bits.length + 4) :=
      (List.take_append_drop (2 * bits.length + 4) cf.tp).symm
    _ = flattenPairs (runtimeWorkspaceFrontPairs value m n) ++ copy ++ tail := by
      rw [hfront', hdrop]
      simp [List.append_assoc]

#print axioms masterM_literal_preservedPassed_drop
#print axioms masterM_literal_workspace_preservedPassed_decomposition
#print axioms unmarkedPassedBoundary_collision
#print axioms masterM_literal_workspace_markedPassed_decomposition

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimePreservedPassedCopy
