import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeWorkspaceTranslator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTranslatedComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTranslatedScheduled
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeCompactCompositionSafety
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeParametricRoundCertificate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePreservedPassedCopy
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePassedRetag
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeDuplicatedSourceArchive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeDuplicatedRepair

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

/-- The completed workspace is not merely encoded differently: it has lost
information required by the canonical passed block.  These two witnesses
agree on the selected literal value and therefore have the identical
completed workspace grammar, but their original lookup tapes—and hence their
canonical passed blocks—are different. -/
theorem completedWorkspace_passedBlock_information_collision :
    let l : Lit := (1, true)
    let w₀ := [false, false]
    let w₁ := [true, false]
    let v₀ := evalLit (fun k => w₀.getD k false) l
    let v₁ := evalLit (fun k => w₁.getD k false) l
    v₀ = v₁ ∧
      runtimeWorkspaceFrontPairs v₀ (2 * l.1 + 2) (2 * l.1 + 4) =
        runtimeWorkspaceFrontPairs v₁ (2 * l.1 + 2) (2 * l.1 + 4) ∧
      flattenPairs (passedSourceBlock (literalLookupTape w₀ l)) ≠
        flattenPairs (passedSourceBlock (literalLookupTape w₁ l)) := by
  native_decide

/-- Consequently no deterministic run from the common completed workspace
can be certified as producing both colliding canonical targets at one fixed
clock. -/
theorem commonWorkspace_fixedRun_target_unique
    (M : Machine) (clock head : Nat) (T target₀ target₁ : List Bool)
    (s₀ s₁ : M.State)
    (h₀ : run M clock ⟨M.start, head, T⟩ = ⟨s₀, head, target₀⟩)
    (h₁ : run M clock ⟨M.start, head, T⟩ = ⟨s₁, head, target₁⟩) :
    target₀ = target₁ := by
  rw [h₀] at h₁
  exact congrArg Cfg.tp h₁

#print axioms completedWorkspace_passedBlock_information_collision
#print axioms commonWorkspace_fixedRun_target_unique

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeCompactSemanticAudit
