import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Alternation

/-!
# Tight switching, step 50: the alternation reduction (depth-counting termination) (branch `razborov-recoverRho-wip`)

The depth-counting termination crux: one collapse round drives an alternating tower down exactly one level,
`AltO (k+3) → AltO (k+2)` (and `AltA` dually).  At the bottom (`k = 0`) the children are `cnf`s, the
leaf-switch turns them to `dnf`s, and the merge flattens the `gOr`-of-`dnf` to a single bottom `dnf` (`AltO 2`).
Higher up (`k = j+1`) the children are `gAnd`s, the switch keeps them, and the merge recurses — each child
collapsing to `AltA (j+2)` by the mutual induction, leaving a `gOr`-of-`AltA (j+2)` = `AltO (j+3)`.

So `depth₀ - 2` rounds reach `AltO 2 = dnf` (the bottom `DNF` the parity capstone needs) — this is the
`Valid`/oracle of the recursive tower at general `d`.

* `allDnf_some_of_all_dnf` / `allCnf_some_of_all_cnf` — uniform-child detection succeeds.
* `collapseRound_AltO` / `collapseRound_AltA` — the per-round one-level reduction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

theorem allDnf_some_of_all_dnf :
    ∀ {L : List (Layered n)}, (∀ x ∈ L, ∃ cs, x = Layered.dnf cs) → ∃ dss, allDnf L = some dss
  | [], _ => ⟨[], rfl⟩
  | x :: rest, h => by
      obtain ⟨cs, rfl⟩ := h x (by simp)
      obtain ⟨dss', hrest⟩ := allDnf_some_of_all_dnf (fun y hy => h y (List.mem_cons_of_mem _ hy))
      exact ⟨cs :: dss', by simp only [allDnf, hrest, Option.map_some]⟩

theorem allCnf_some_of_all_cnf :
    ∀ {L : List (Layered n)}, (∀ x ∈ L, ∃ cs, x = Layered.cnf cs) → ∃ css, allCnf L = some css
  | [], _ => ⟨[], rfl⟩
  | x :: rest, h => by
      obtain ⟨cs, rfl⟩ := h x (by simp)
      obtain ⟨css', hrest⟩ := allCnf_some_of_all_cnf (fun y hy => h y (List.mem_cons_of_mem _ hy))
      exact ⟨cs :: css', by simp only [allCnf, hrest, Option.map_some]⟩

private theorem leafCollapse_gOr_eq (F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapse F ρ (gOr gs) = gOr (gs.map (leafCollapse F ρ)) := by
  rw [leafCollapse, leafCollapseList_eq]

private theorem leafCollapse_gAnd_eq (F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapse F ρ (gAnd gs) = gAnd (gs.map (leafCollapse F ρ)) := by
  rw [leafCollapse, leafCollapseList_eq]

mutual
theorem collapseRound_AltO (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ {k : ℕ} {C : Layered n}, AltO (k + 3) C → AltO (k + 2) (collapseRound F ρ C)
  | k, _, AltO.gOr _ gs hne h => by
    cases k with
    | zero =>
      -- children are cnf; switch to dnf; merge gOr-of-dnf → dnf
      have hdnf : ∀ x ∈ gs.map (leafCollapse F ρ), ∃ cs, x = Layered.dnf cs := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨g, hg, rfl⟩ := hx
        obtain ⟨cs, rfl⟩ := AltA_two_cnf (h g hg)
        exact ⟨_, rfl⟩
      obtain ⟨dss, hall⟩ := allDnf_some_of_all_dnf hdnf
      have hcr : collapseRound F ρ (gOr gs) = Layered.dnf dss.flatten := by
        show mergePass (leafCollapse F ρ (gOr gs)) = _
        rw [leafCollapse_gOr_eq]
        simp only [mergePass, hall]
      rw [hcr]; exact AltO.dnf _
    | succ j =>
      -- children are gAnd; switch keeps gAnd; merge recurses to each child
      have hnone : allDnf (gs.map (leafCollapse F ρ)) = none := by
        obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨gsg₀, rfl⟩ : ∃ gsg, g₀ = gAnd gsg := by
          cases h g₀ (by simp) with
          | gAnd k gsg hne hh => exact ⟨gsg, rfl⟩
        simp only [List.map_cons, leafCollapse_gAnd_eq, allDnf]
      have hcr : collapseRound F ρ (gOr gs) = gOr (gs.map (collapseRound F ρ)) := by
        show mergePass (leafCollapse F ρ (gOr gs)) = _
        rw [leafCollapse_gOr_eq]
        simp only [mergePass, hnone]
        rw [mergePassList_eq, List.map_map]
        rfl
      rw [hcr]
      refine AltO.gOr j (gs.map (collapseRound F ρ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact collapseRound_AltA F ρ (h g hg)
theorem collapseRound_AltA (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ {k : ℕ} {C : Layered n}, AltA (k + 3) C → AltA (k + 2) (collapseRound F ρ C)
  | k, _, AltA.gAnd _ gs hne h => by
    cases k with
    | zero =>
      have hcnf : ∀ x ∈ gs.map (leafCollapse F ρ), ∃ cs, x = Layered.cnf cs := by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨g, hg, rfl⟩ := hx
        obtain ⟨cs, rfl⟩ := AltO_two_dnf (h g hg)
        exact ⟨_, rfl⟩
      obtain ⟨css, hall⟩ := allCnf_some_of_all_cnf hcnf
      have hcr : collapseRound F ρ (gAnd gs) = Layered.cnf css.flatten := by
        show mergePass (leafCollapse F ρ (gAnd gs)) = _
        rw [leafCollapse_gAnd_eq]
        simp only [mergePass, hall]
      rw [hcr]; exact AltA.cnf _
    | succ j =>
      have hnone : allCnf (gs.map (leafCollapse F ρ)) = none := by
        obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨gsg₀, rfl⟩ : ∃ gsg, g₀ = gOr gsg := by
          cases h g₀ (by simp) with
          | gOr k gsg hne hh => exact ⟨gsg, rfl⟩
        simp only [List.map_cons, leafCollapse_gOr_eq, allCnf]
      have hcr : collapseRound F ρ (gAnd gs) = gAnd (gs.map (collapseRound F ρ)) := by
        show mergePass (leafCollapse F ρ (gAnd gs)) = _
        rw [leafCollapse_gAnd_eq]
        simp only [mergePass, hnone]
        rw [mergePassList_eq, List.map_map]
        rfl
      rw [hcr]
      refine AltA.gAnd j (gs.map (collapseRound F ρ)) (by simpa using hne) ?_
      intro g' hg'
      rw [List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      exact collapseRound_AltO F ρ (h g hg)
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_AltO
