import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeBounded

/-!
# Tight switching, step 57: one survivor sets the whole tower's bottom width (branch `razborov-recoverRho-wip`)

The tower version of step 55.  A single survivor restriction `ρ` that shallows *every* bottom gate of `C` —
both as a `DNF` (`canonicalDT cs F ρ`) and as a `CNF` (`canonicalDT (negDNF cs) F ρ`), since `leafCollapse`
switches `dnf`/`cnf` gates by different canonical trees — makes every new bottom gate of `leafCollapse F ρ C`
width `≤ s`.  Proved by the mutual `Layered`/`List` recursion: bottom gates use the per-gate survivor bound
(step 55), internal nodes recurse with the shallowness hypothesis restricted to their children.

* `Shallows F ρ s C` — `ρ` shallows every bottom gate of `C` below `s` (both polarities).
* `leafCollapse_tower_BottomWidth` — `Shallows F ρ s C ⟹ BottomWidth s (leafCollapse F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- `ρ` shallows every bottom gate of `C` below `s`, in both polarities (as a `DNF` and as a `CNF`). -/
def Shallows (F : ℕ) (ρ : Fin n → Option Bool) (s : ℕ) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C,
    (canonicalDT cs F ρ).depth < s ∧ (canonicalDT (negDNF cs) F ρ).depth < s

/-- A bottom gate of a child is a bottom gate of the `gAnd` node. -/
theorem bottomGates_mem_gAnd {gs : List (Layered n)} {g : Layered n} {cs : List (Clause n)}
    (hg : g ∈ gs) (hcs : cs ∈ bottomGates g) : cs ∈ bottomGates (gAnd gs) := by
  rw [bottomGates_gAnd, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

/-- A bottom gate of a child is a bottom gate of the `gOr` node. -/
theorem bottomGates_mem_gOr {gs : List (Layered n)} {g : Layered n} {cs : List (Clause n)}
    (hg : g ∈ gs) (hcs : cs ∈ bottomGates g) : cs ∈ bottomGates (gOr gs) := by
  rw [bottomGates_gOr, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

-- leafCollapse_tower_BottomWidth: one survivor shallowing all bottoms sets the whole tower BottomWidth s.
-- Mutual with the list version.
mutual
theorem leafCollapse_tower_BottomWidth (F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ {C : Layered n}, Shallows F ρ s C → BottomWidth s (leafCollapse F ρ C)
  | dnf cs, hsh =>
      BottomBounded_BottomWidth
        (leafCollapse_dnf_BottomBounded_survivor F ρ cs
          (hsh cs (by rw [show bottomGates (dnf cs) = [cs] from rfl]; simp)).1)
  | cnf cs, hsh =>
      BottomBounded_BottomWidth
        (leafCollapse_cnf_BottomBounded_survivor F ρ cs
          (hsh cs (by rw [show bottomGates (cnf cs) = [cs] from rfl]; simp)).2)
  | gAnd gs, hsh => by
      show BottomWidth s (gAnd (leafCollapseList F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_tower_BottomWidth F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gAnd hg' hcs)) g hg cs' hcsl T hT
  | gOr gs, hsh => by
      show BottomWidth s (gOr (leafCollapseList F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_tower_BottomWidth F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gOr hg' hcs)) g hg cs' hcsl T hT
theorem leafCollapseList_tower_BottomWidth (F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ (gs : List (Layered n)),
      (∀ g ∈ gs, ∀ cs ∈ bottomGates g,
        (canonicalDT cs F ρ).depth < s ∧ (canonicalDT (negDNF cs) F ρ).depth < s) →
      ∀ g ∈ gs, BottomWidth s (leafCollapse F ρ g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapse_tower_BottomWidth F ρ (fun cs hcs => hall g (by simp) cs hcs)
      · exact leafCollapseList_tower_BottomWidth F ρ gs
          (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_tower_BottomWidth
