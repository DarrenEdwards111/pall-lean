import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceTranslator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTranslatedComposition

/-!
# Marked compaction semantic integration audit

The physical compactor is certified in the imported module.  This separate
semantic boundary compares the completed `masterM` workspace it moves with
the canonical passed-source block required by the scheduled successor.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactSemanticAudit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryAdapter

/-- The now-physical compactor exposes a second semantic obligation.  The
completed `masterM` workspace is not itself the canonical passed-source
block: its certified leading pair is `10`, while the canonical block's tag
is `11`.  Therefore scheduled adjacency additionally needs a
workspace-to-passed-block translator; positional compaction alone cannot
justify the equality. -/
theorem compactedWorkspace_passedBlock_tag_mismatch
    (w : List Bool) (l : Lit) (tail : List Bool) :
    let bits := literalLookupTape w l
    let trailer := [true, false, false, true] ++
      List.replicate bits.length true ++ tail
    let mcf := run masterM (literalLookupClock w l)
      (init masterM (bits ++ trailer))
    (mcf.tp.take (2 * bits.length + 4)).take 2 = [true, false] ∧
      (flattenPairs (passedSourceBlock bits)).take 2 = [true, true] := by
  dsimp only
  obtain ⟨value, hworkspace⟩ :=
    masterM_literal_workspaceFrontPairs w l tail
  rw [hworkspace]
  constructor
  · simp [runtimeWorkspaceFrontPairs, flattenPairs]
  · simp [passedSourceBlock, flattenPairs]

#print axioms compactedWorkspace_passedBlock_tag_mismatch

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactSemanticAudit
