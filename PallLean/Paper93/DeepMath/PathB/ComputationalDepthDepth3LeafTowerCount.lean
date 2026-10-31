import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerBounded

/-!
# Tight switching, step 93: one survivor sets the whole tower's per-gate clause-count (branch `razborov-recoverRho-wip`)

The per-gate clause-count companion of step 57.  `leafCollapse_dnf_BottomBounded` (step 55) already proved the
*clause-count* half — the switched bottom gate has `≤ 2^depth` clauses — alongside the width half.  So one
survivor `ρ` shallowing every bottom gate below `s` makes every new bottom gate of `leafCollapse F ρ C` have
`≤ 2^s` clauses (`BottomCount (2^s)`), exactly as it makes them `BottomWidth s`.

* `BottomCount` — every bottom gate has `≤ M` clauses (the gate-wise count projection of `BottomBounded`).
* `leafCollapse_tower_BottomCount` — `Shallows F ρ s C ⟹ BottomCount (2^s) (leafCollapse F ρ C)`.

(The merge then *sums* per-gate counts, so a collapse round leaves per-gate count `≤ (gate count)·2^s` — the
remaining bookkeeping for a fully threaded clause-count invariant.)

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The clause-count invariant.**  Every bottom gate of `C` has at most `M` clauses. -/
def BottomCount (M : ℕ) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C, cs.length ≤ M

/-- `BottomBounded` forgets to `BottomCount`. -/
theorem BottomBounded_BottomCount {w M : ℕ} {C : Layered n} (h : BottomBounded w M C) :
    BottomCount M C :=
  fun cs hcs => (h cs hcs).2

-- leafCollapse_tower_BottomCount: one survivor sets every new bottom gate's clause-count ≤ 2^s. Mutual.
mutual
theorem leafCollapse_tower_BottomCount (F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ {C : Layered n}, Shallows F ρ s C → BottomCount (2 ^ s) (leafCollapse F ρ C)
  | dnf cs, hsh =>
      BottomBounded_BottomCount
        (leafCollapse_dnf_BottomBounded_survivor F ρ cs
          (hsh cs (by rw [show bottomGates (dnf cs) = [cs] from rfl]; simp)).1)
  | cnf cs, hsh =>
      BottomBounded_BottomCount
        (leafCollapse_cnf_BottomBounded_survivor F ρ cs
          (hsh cs (by rw [show bottomGates (cnf cs) = [cs] from rfl]; simp)).2)
  | gAnd gs, hsh => by
      show BottomCount (2 ^ s) (gAnd (leafCollapseList F ρ gs))
      intro cs' hcs'
      rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_tower_BottomCount F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gAnd hg' hcs)) g hg cs' hcsl
  | gOr gs, hsh => by
      show BottomCount (2 ^ s) (gOr (leafCollapseList F ρ gs))
      intro cs' hcs'
      rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_tower_BottomCount F ρ gs
        (fun g' hg' cs hcs => hsh cs (bottomGates_mem_gOr hg' hcs)) g hg cs' hcsl
theorem leafCollapseList_tower_BottomCount (F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} :
    ∀ (gs : List (Layered n)),
      (∀ g ∈ gs, ∀ cs ∈ bottomGates g,
        (canonicalDT cs F ρ).depth < s ∧ (canonicalDT (negDNF cs) F ρ).depth < s) →
      ∀ g ∈ gs, BottomCount (2 ^ s) (leafCollapse F ρ g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapse_tower_BottomCount F ρ (fun cs hcs => hall g (by simp) cs hcs)
      · exact leafCollapseList_tower_BottomCount F ρ gs
          (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_tower_BottomCount
