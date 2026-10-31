import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GateCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRound

/-!
# Tight switching, step 90: a collapse round does not increase the bottom-gate count (branch `razborov-recoverRho-wip`)

The gate-count invariant.  `leafCollapse` preserves the non-empty-gates shape (it switches bottoms and keeps
the gate lists), so by the merge bound (step 89) and the leaf-switch count-preservation (step 86),
`collapseRound = mergePass ∘ leafCollapse` does not increase the bottom-gate count.  Hence the count is
non-increasing along the rounds, and the uniform gate bound `M := 2·(bottomGates C₀).length` of the union
bound (step 85) holds at every reachable tower.

* `leafCollapse_NonEmptyGates` — the leaf-switch preserves non-empty gates.
* `collapseRound_count_le` — a collapse round does not increase the bottom-gate count.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- The leaf-switch preserves the non-empty-gates shape. -/
theorem leafCollapse_NonEmptyGates (F : ℕ) (ρ : Fin n → Option Bool) {C : Layered n}
    (h : NonEmptyGates C) : NonEmptyGates (leafCollapse F ρ C) := by
  induction h with
  | dnf cs => exact NonEmptyGates.cnf _
  | cnf cs => exact NonEmptyGates.dnf _
  | gAnd gs hne _ ih =>
      show NonEmptyGates (gAnd (leafCollapseList F ρ gs))
      refine NonEmptyGates.gAnd _ ?_ ?_
      · rw [leafCollapseList_eq]; exact mt List.map_eq_nil_iff.mp hne
      · intro g' hg'
        rw [leafCollapseList_eq, List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ih g hg
  | gOr gs hne _ ih =>
      show NonEmptyGates (gOr (leafCollapseList F ρ gs))
      refine NonEmptyGates.gOr _ ?_ ?_
      · rw [leafCollapseList_eq]; exact mt List.map_eq_nil_iff.mp hne
      · intro g' hg'
        rw [leafCollapseList_eq, List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ih g hg

/-- **A collapse round does not increase the bottom-gate count.** -/
theorem collapseRound_count_le (F : ℕ) (ρ : Fin n → Option Bool) {C : Layered n}
    (h : NonEmptyGates C) :
    (bottomGates (collapseRound F ρ C)).length ≤ (bottomGates C).length := by
  show (bottomGates (mergePass (leafCollapse F ρ C))).length ≤ (bottomGates C).length
  calc (bottomGates (mergePass (leafCollapse F ρ C))).length
      ≤ (bottomGates (leafCollapse F ρ C)).length :=
        mergePass_count_le (leafCollapse_NonEmptyGates F ρ h)
    _ = (bottomGates C).length := leafCollapse_bottomGates_length F ρ C

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_count_le
