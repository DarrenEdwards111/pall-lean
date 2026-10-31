import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount

/-!
# Block-DT model, route-2 step [171d]: the block round does not increase the bottom-gate count

The block twin of `collapseRound_count_le`.  `leafCollapseBlock` preserves the bottom-gate *count*
(it switches each bottom gate `dnf↔cnf` and keeps the gate lists), and `mergePass` (tree-agnostic) only
merges — so `collapseRoundBlock = mergePass ∘ leafCollapseBlock` does not increase the bottom-gate
count.  This is the gate-count invariant the m-free union bound `hunion` ([171c]) needs: the uniform
bound `M := (bottomGates C₀).length` holds at every reachable tower.

* `leafCollapseBlock_bottomGates_length` — the block leaf-switch preserves the bottom-gate count.
* `leafCollapseBlock_NonEmptyGates` — it preserves the non-empty-gates shape.
* `collapseRoundBlock_count_le` — a block round does not increase the bottom-gate count.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- The block leaf-switch preserves the bottom-gate count.
mutual
theorem leafCollapseBlock_bottomGates_length (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ C : Layered n, (bottomGates (leafCollapseBlock w F ρ C)).length = (bottomGates C).length
  | dnf _ => rfl
  | cnf _ => rfl
  | gAnd gs => by
      show (bottomGates (gAnd (leafCollapseBlockList w F ρ gs))).length
        = (bottomGates (gAnd gs)).length
      rw [bottomGates_gAnd, bottomGates_gAnd]
      exact leafCollapseBlockList_bottomGates_length w F ρ gs
  | gOr gs => by
      show (bottomGates (gOr (leafCollapseBlockList w F ρ gs))).length
        = (bottomGates (gOr gs)).length
      rw [bottomGates_gOr, bottomGates_gOr]
      exact leafCollapseBlockList_bottomGates_length w F ρ gs
theorem leafCollapseBlockList_bottomGates_length (w F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ gs : List (Layered n),
      (bottomGatesList (leafCollapseBlockList w F ρ gs)).length = (bottomGatesList gs).length
  | [] => rfl
  | g :: gs => by
      rw [leafCollapseBlockList, bottomGatesList, bottomGatesList, List.length_append,
        List.length_append, leafCollapseBlock_bottomGates_length w F ρ g,
        leafCollapseBlockList_bottomGates_length w F ρ gs]
end

/-- The block leaf-switch preserves the non-empty-gates shape. -/
theorem leafCollapseBlock_NonEmptyGates (w F : ℕ) (ρ : Fin n → Option Bool) {C : Layered n}
    (h : NonEmptyGates C) : NonEmptyGates (leafCollapseBlock w F ρ C) := by
  induction h with
  | dnf cs => exact NonEmptyGates.cnf _
  | cnf cs => exact NonEmptyGates.dnf _
  | gAnd gs hne _ ih =>
      show NonEmptyGates (gAnd (leafCollapseBlockList w F ρ gs))
      refine NonEmptyGates.gAnd _ ?_ ?_
      · rw [leafCollapseBlockList_eq]; exact mt List.map_eq_nil_iff.mp hne
      · intro g' hg'
        rw [leafCollapseBlockList_eq, List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ih g hg
  | gOr gs hne _ ih =>
      show NonEmptyGates (gOr (leafCollapseBlockList w F ρ gs))
      refine NonEmptyGates.gOr _ ?_ ?_
      · rw [leafCollapseBlockList_eq]; exact mt List.map_eq_nil_iff.mp hne
      · intro g' hg'
        rw [leafCollapseBlockList_eq, List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ih g hg

/-- **A block collapse round does not increase the bottom-gate count.** -/
theorem collapseRoundBlock_count_le (w F : ℕ) (ρ : Fin n → Option Bool) {C : Layered n}
    (h : NonEmptyGates C) :
    (bottomGates (collapseRoundBlock w F ρ C)).length ≤ (bottomGates C).length := by
  show (bottomGates (mergePass (leafCollapseBlock w F ρ C))).length ≤ (bottomGates C).length
  calc (bottomGates (mergePass (leafCollapseBlock w F ρ C))).length
      ≤ (bottomGates (leafCollapseBlock w F ρ C)).length :=
        mergePass_count_le (leafCollapseBlock_NonEmptyGates w F ρ h)
    _ = (bottomGates C).length := leafCollapseBlock_bottomGates_length w F ρ C

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRoundBlock_count_le
