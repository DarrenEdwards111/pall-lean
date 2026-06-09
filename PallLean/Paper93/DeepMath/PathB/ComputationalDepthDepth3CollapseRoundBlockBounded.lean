import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToDNF

/-!
# Block-DT model, route-2 step [169c]: the block round preserves bottom width

The block twin of `leafCollapse_tower_BottomWidth` + `collapseRound_BottomWidth`.  If `ρ` shallows
every bottom gate of `C` below `s` in the **block** tree (`ShallowsBlock`, both polarities), then the
block round `collapseRoundBlock w F ρ C` is `BottomWidth s`.  The per-gate width-from-depth fact is the
generic `dtreeToCNF_width` / `dtreeToDNF_width` (clause width `≤` tree depth), with `negTree_depth` for
the `cnf` polarity — **no `canonicalDT ↔ canonicalDTree` bridge**.  The merge preserves width
(`mergePass_BottomWidth`, tree-agnostic).

* `ShallowsBlock w F ρ s C` — `ρ` shallows every bottom gate of `C` below `s` (both polarities, block).
* `leafCollapseBlock_tower_BottomWidth` — `ShallowsBlock w F ρ s C ⟹ BottomWidth s (leafCollapseBlock w F ρ C)`.
* `collapseRoundBlock_BottomWidth` — `ShallowsBlock w F ρ s C ⟹ BottomWidth s (collapseRoundBlock w F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- `ρ` shallows every bottom gate of `C` below `s`, both polarities, in the **block** tree. -/
def ShallowsBlock (w F : ℕ) (ρ : Fin n → Option Bool) (s : ℕ) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C,
    (canonicalDTree cs w F ρ).depth < s ∧ (canonicalDTree (negDNF cs) w F ρ).depth < s

-- One survivor shallowing all bottoms (block) sets the whole tower BottomWidth s.
mutual
theorem leafCollapseBlock_tower_BottomWidth (w F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ {C : Layered n}, ShallowsBlock w F ρ s C → BottomWidth s (leafCollapseBlock w F ρ C)
  | dnf cs, hsh => by
      show BottomWidth s (cnf (dtreeToCNF (canonicalDTree cs w F ρ)))
      intro cs' hcs' T hT
      rw [show bottomGates (cnf (dtreeToCNF (canonicalDTree cs w F ρ)))
            = [dtreeToCNF (canonicalDTree cs w F ρ)] from rfl, List.mem_singleton] at hcs'
      subst hcs'
      have hd : (canonicalDTree cs w F ρ).depth < s :=
        (hsh cs (by rw [show bottomGates (dnf cs) = [cs] from rfl]; simp)).1
      have hw := dtreeToCNF_width (canonicalDTree cs w F ρ) T hT
      omega
  | cnf cs, hsh => by
      show BottomWidth s (dnf (dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ))))
      intro cs' hcs' T hT
      rw [show bottomGates (dnf (dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ))))
            = [dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ))] from rfl,
        List.mem_singleton] at hcs'
      subst hcs'
      have hd : (canonicalDTree (negDNF cs) w F ρ).depth < s :=
        (hsh cs (by rw [show bottomGates (cnf cs) = [cs] from rfl]; simp)).2
      have hw := dtreeToDNF_width (DTree.negTree (canonicalDTree (negDNF cs) w F ρ)) T hT
      rw [DTree.negTree_depth] at hw
      omega
  | gAnd gs, hsh => by
      show BottomWidth s (gAnd (leafCollapseBlockList w F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseBlockList_tower_BottomWidth w F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gAnd hg' hcs)) g hg cs' hcsl T hT
  | gOr gs, hsh => by
      show BottomWidth s (gOr (leafCollapseBlockList w F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseBlockList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseBlockList_tower_BottomWidth w F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gOr hg' hcs)) g hg cs' hcsl T hT
theorem leafCollapseBlockList_tower_BottomWidth (w F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ (gs : List (Layered n)),
      (∀ g ∈ gs, ∀ cs ∈ bottomGates g,
        (canonicalDTree cs w F ρ).depth < s ∧ (canonicalDTree (negDNF cs) w F ρ).depth < s) →
      ∀ g ∈ gs, BottomWidth s (leafCollapseBlock w F ρ g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapseBlock_tower_BottomWidth w F ρ (fun cs hcs => hall g (by simp) cs hcs)
      · exact leafCollapseBlockList_tower_BottomWidth w F ρ gs
          (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

/-- **The block round preserves the bottom width.**  `ShallowsBlock w F ρ s C ⟹ BottomWidth s
(collapseRoundBlock w F ρ C)` — switch sets it (block tower width), merge keeps it. -/
theorem collapseRoundBlock_BottomWidth (w F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} {C : Layered n}
    (hsh : ShallowsBlock w F ρ s C) : BottomWidth s (collapseRoundBlock w F ρ C) := by
  show BottomWidth s (mergePass (leafCollapseBlock w F ρ C))
  exact mergePass_BottomWidth (leafCollapseBlock_tower_BottomWidth w F ρ hsh)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRoundBlock_BottomWidth
