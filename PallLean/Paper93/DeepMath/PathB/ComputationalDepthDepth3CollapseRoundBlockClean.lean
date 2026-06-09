import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BottomClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalFresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreshClauses
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfFresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SingleRoundOr

/-!
# Block-DT model, route-2 step [170a]: the block round preserves `BottomClean`

The block twin of `leafCollapse_BottomClean`.  Unlike the bit version (clean *unconditionally*,
`toDTree_canonicalDT_fresh` needs no hypothesis), the **block** tree's freshness `canonicalDTree_fresh`
requires the input gate's terms to be variable-`Nodup`.  So the block round preserves `BottomClean`
*conditionally on the input nodup* — which is exactly the nodup half of `BottomClean`, so the invariant
is self-preserving: input clean ⟹ output clean.  Route 2's m-free count needs this (its injectivity
hypotheses are `Consistent` + `Nodup`), whereas the bit tight count did not.

* `leafCollapseBlock_tower_clean` — input bottom gates nodup ⟹ `BottomClean (leafCollapseBlock w F ρ C)`.
* `collapseRoundBlock_BottomClean` — same, through the merge (`mergePass_BottomPred`, tree-agnostic).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- `negDNF` preserves the variable-`Nodup` property of every clause. -/
private theorem negDNF_nodup {cs : List (Clause n)}
    (h : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ T ∈ negDNF cs, (T.lits.map litVarOf).Nodup := by
  intro T hT
  rw [negDNF, List.mem_map] at hT
  obtain ⟨C0, hC0, rfl⟩ := hT
  have hmap : (C0.lits.map negLit).map litVarOf = C0.lits.map litVarOf := by
    rw [List.map_map]; exact List.map_congr_left (fun ℓ _ => litVarOf_negLit ℓ)
  simpa [hmap] using h C0 hC0

-- One leaf collapse sets BottomClean, given the input bottom gates are nodup.
mutual
theorem leafCollapseBlock_tower_clean (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ {C : Layered n},
      BottomPred (fun T => (T.lits.map litVarOf).Nodup) C →
      BottomClean (leafCollapseBlock w F ρ C)
  | dnf cs, hnd => by
      have hndcs : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup :=
        hnd cs (by rw [show bottomGates (dnf cs) = [cs] from rfl]; simp)
      have hfresh := canonicalDTree_fresh cs w hndcs F ρ
      refine ⟨?_, ?_⟩
      · intro cs' hcs' T hT
        rw [show bottomGates (leafCollapseBlock w F ρ (dnf cs))
              = [dtreeToCNF (canonicalDTree cs w F ρ)] from rfl, List.mem_singleton] at hcs'
        subst hcs'; exact dtreeToCNF_consistent _ hfresh T hT
      · intro cs' hcs' T hT
        rw [show bottomGates (leafCollapseBlock w F ρ (dnf cs))
              = [dtreeToCNF (canonicalDTree cs w F ρ)] from rfl, List.mem_singleton] at hcs'
        subst hcs'; exact dtreeToCNF_nodup _ hfresh T hT
  | cnf cs, hnd => by
      have hndcs : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup :=
        hnd cs (by rw [show bottomGates (cnf cs) = [cs] from rfl]; simp)
      have hfresh := DTree.negTree_fresh _ (canonicalDTree_fresh (negDNF cs) w (negDNF_nodup hndcs) F ρ)
      refine ⟨?_, ?_⟩
      · intro cs' hcs' T hT
        rw [show bottomGates (leafCollapseBlock w F ρ (cnf cs))
              = [dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ))] from rfl,
          List.mem_singleton] at hcs'
        subst hcs'; exact dtreeToDNF_consistent _ hfresh T hT
      · intro cs' hcs' T hT
        rw [show bottomGates (leafCollapseBlock w F ρ (cnf cs))
              = [dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ))] from rfl,
          List.mem_singleton] at hcs'
        subst hcs'; exact dtreeToDNF_nodup _ hfresh T hT
  | gAnd gs, hnd => by
      have hlist : ∀ g ∈ gs, BottomPred (fun T => (T.lits.map litVarOf).Nodup) g :=
        fun g' hg' cs hcs T hT => hnd cs (bottomGates_mem_gAnd hg' hcs) T hT
      show BottomClean (gAnd (leafCollapseBlockList w F ρ gs))
      refine ⟨?_, ?_⟩
      · intro cs' hcs' T hT
        rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
          List.mem_flatten] at hcs'
        obtain ⟨l, hl, hcsl⟩ := hcs'
        rw [List.mem_map] at hl
        obtain ⟨g, hg, rfl⟩ := hl
        exact (leafCollapseBlockList_tower_clean w F ρ gs hlist g hg).1 cs' hcsl T hT
      · intro cs' hcs' T hT
        rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
          List.mem_flatten] at hcs'
        obtain ⟨l, hl, hcsl⟩ := hcs'
        rw [List.mem_map] at hl
        obtain ⟨g, hg, rfl⟩ := hl
        exact (leafCollapseBlockList_tower_clean w F ρ gs hlist g hg).2 cs' hcsl T hT
  | gOr gs, hnd => by
      have hlist : ∀ g ∈ gs, BottomPred (fun T => (T.lits.map litVarOf).Nodup) g :=
        fun g' hg' cs hcs T hT => hnd cs (bottomGates_mem_gOr hg' hcs) T hT
      show BottomClean (gOr (leafCollapseBlockList w F ρ gs))
      refine ⟨?_, ?_⟩
      · intro cs' hcs' T hT
        rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
          List.mem_flatten] at hcs'
        obtain ⟨l, hl, hcsl⟩ := hcs'
        rw [List.mem_map] at hl
        obtain ⟨g, hg, rfl⟩ := hl
        exact (leafCollapseBlockList_tower_clean w F ρ gs hlist g hg).1 cs' hcsl T hT
      · intro cs' hcs' T hT
        rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
          List.mem_flatten] at hcs'
        obtain ⟨l, hl, hcsl⟩ := hcs'
        rw [List.mem_map] at hl
        obtain ⟨g, hg, rfl⟩ := hl
        exact (leafCollapseBlockList_tower_clean w F ρ gs hlist g hg).2 cs' hcsl T hT
theorem leafCollapseBlockList_tower_clean (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ (gs : List (Layered n)),
      (∀ g ∈ gs, BottomPred (fun T => (T.lits.map litVarOf).Nodup) g) →
      ∀ g ∈ gs, BottomClean (leafCollapseBlock w F ρ g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapseBlock_tower_clean w F ρ (hall g (by simp))
      · exact leafCollapseBlockList_tower_clean w F ρ gs
          (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

/-- **The block round preserves `BottomClean`** (given the input bottom gates are nodup). -/
theorem collapseRoundBlock_BottomClean (w F : ℕ) (ρ : Fin n → Option Bool) {C : Layered n}
    (hnd : BottomPred (fun T => (T.lits.map litVarOf).Nodup) C) :
    BottomClean (collapseRoundBlock w F ρ C) := by
  have hcl := leafCollapseBlock_tower_clean w F ρ hnd
  show BottomClean (mergePass (leafCollapseBlock w F ρ C))
  exact ⟨mergePass_BottomPred hcl.1, mergePass_BottomPred hcl.2⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRoundBlock_BottomClean
