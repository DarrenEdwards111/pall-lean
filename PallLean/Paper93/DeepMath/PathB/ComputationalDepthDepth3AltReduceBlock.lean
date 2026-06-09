import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce

/-!
# Block-DT model, route-2 step [169d]: the block round drops one alternation level

The block twin of `collapseRound_AltO` / `collapseRound_AltA`.  The proof is **purely structural** —
`leafCollapseBlock` has the same polarity behavior as `leafCollapse` (`dnf → cnf`, `cnf → dnf`,
`gOr/gAnd` recurse), and the alternation bookkeeping (`allDnf`/`allCnf`, `AltA_two_cnf`/`AltO_two_dnf`,
`mergePass`) is tree-agnostic — so this is a verbatim mirror with `leafCollapse`/`collapseRound`
replaced by their block versions.

* `collapseRoundBlock_AltO` — `AltO (k+3) C ⟹ AltO (k+2) (collapseRoundBlock w F ρ C)`.
* `collapseRoundBlock_AltA` — `AltA (k+3) C ⟹ AltA (k+2) (collapseRoundBlock w F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem leafCollapseBlock_gOr_eq (w F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapseBlock w F ρ (gOr gs) = gOr (gs.map (leafCollapseBlock w F ρ)) := by
  rw [leafCollapseBlock, leafCollapseBlockList_eq]

private theorem leafCollapseBlock_gAnd_eq (w F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapseBlock w F ρ (gAnd gs) = gAnd (gs.map (leafCollapseBlock w F ρ)) := by
  rw [leafCollapseBlock, leafCollapseBlockList_eq]

mutual
theorem collapseRoundBlock_AltO (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ {k : ℕ} {C : Layered n}, AltO (k + 3) C → AltO (k + 2) (collapseRoundBlock w F ρ C)
  | k, _, AltO.gOr _ gs hne h => by
    cases k with
    | zero =>
      have hdnf : ∀ x ∈ gs.map (leafCollapseBlock w F ρ), ∃ cs, x = Layered.dnf cs := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨g, hg, rfl⟩ := hx
        obtain ⟨cs, rfl⟩ := AltA_two_cnf (h g hg)
        exact ⟨_, rfl⟩
      obtain ⟨dss, hall⟩ := allDnf_some_of_all_dnf hdnf
      have hcr : collapseRoundBlock w F ρ (gOr gs) = Layered.dnf dss.flatten := by
        show mergePass (leafCollapseBlock w F ρ (gOr gs)) = _
        rw [leafCollapseBlock_gOr_eq]
        simp only [mergePass, hall]
      rw [hcr]; exact AltO.dnf _
    | succ j =>
      have hnone : allDnf (gs.map (leafCollapseBlock w F ρ)) = none := by
        obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨gsg₀, rfl⟩ : ∃ gsg, g₀ = gAnd gsg := by
          cases h g₀ (by simp) with
          | gAnd k gsg hne hh => exact ⟨gsg, rfl⟩
        simp only [List.map_cons, leafCollapseBlock_gAnd_eq, allDnf]
      have hcr : collapseRoundBlock w F ρ (gOr gs) = gOr (gs.map (collapseRoundBlock w F ρ)) := by
        show mergePass (leafCollapseBlock w F ρ (gOr gs)) = _
        rw [leafCollapseBlock_gOr_eq]
        simp only [mergePass, hnone]
        rw [mergePassList_eq, List.map_map]
        rfl
      rw [hcr]
      refine AltO.gOr j (gs.map (collapseRoundBlock w F ρ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact collapseRoundBlock_AltA w F ρ (h g hg)
theorem collapseRoundBlock_AltA (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ {k : ℕ} {C : Layered n}, AltA (k + 3) C → AltA (k + 2) (collapseRoundBlock w F ρ C)
  | k, _, AltA.gAnd _ gs hne h => by
    cases k with
    | zero =>
      have hcnf : ∀ x ∈ gs.map (leafCollapseBlock w F ρ), ∃ cs, x = Layered.cnf cs := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨g, hg, rfl⟩ := hx
        obtain ⟨cs, rfl⟩ := AltO_two_dnf (h g hg)
        exact ⟨_, rfl⟩
      obtain ⟨css, hall⟩ := allCnf_some_of_all_cnf hcnf
      have hcr : collapseRoundBlock w F ρ (gAnd gs) = Layered.cnf css.flatten := by
        show mergePass (leafCollapseBlock w F ρ (gAnd gs)) = _
        rw [leafCollapseBlock_gAnd_eq]
        simp only [mergePass, hall]
      rw [hcr]; exact AltA.cnf _
    | succ j =>
      have hnone : allCnf (gs.map (leafCollapseBlock w F ρ)) = none := by
        obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨gsg₀, rfl⟩ : ∃ gsg, g₀ = gOr gsg := by
          cases h g₀ (by simp) with
          | gOr k gsg hne hh => exact ⟨gsg, rfl⟩
        simp only [List.map_cons, leafCollapseBlock_gOr_eq, allCnf]
      have hcr : collapseRoundBlock w F ρ (gAnd gs) = gAnd (gs.map (collapseRoundBlock w F ρ)) := by
        show mergePass (leafCollapseBlock w F ρ (gAnd gs)) = _
        rw [leafCollapseBlock_gAnd_eq]
        simp only [mergePass, hnone]
        rw [mergePassList_eq, List.map_map]
        rfl
      rw [hcr]
      refine AltA.gAnd j (gs.map (collapseRoundBlock w F ρ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact collapseRoundBlock_AltO w F ρ (h g hg)
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRoundBlock_AltO
