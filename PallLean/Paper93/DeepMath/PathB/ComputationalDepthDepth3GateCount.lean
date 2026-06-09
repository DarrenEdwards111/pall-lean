import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HsurvDischarge

/-!
# Tight switching, step 86: the gate-count facts (branch `razborov-recoverRho-wip`)

The gate-count `M` for the union bound (step 85) is uniform across the rounds because the leaf-switch keeps the
bottom-gate *count* (each bottom gate maps to one switched gate) and the merge only *reduces* it (uniform
siblings collapse to one).  Here the clean, unconditional half:

* `leafCollapse_bottomGates_length` — the leaf-switch preserves the bottom-gate count exactly.
* `bottomGatesG_card_le` — the survivor gate set is at most twice the bottom-gate count
  (`bottomGates ∪ De Morgan duals`).

So `(bottomGatesG C).card ≤ 2·(bottomGates C).length`, and the count threads through `collapseRound` (the
merge's non-increase, on the non-empty alternating towers, is the remaining half).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- leafCollapse_bottomGates_length: the leaf-switch preserves the bottom-gate count (mutual with the list form).
mutual
theorem leafCollapse_bottomGates_length (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ C : Layered n, (bottomGates (leafCollapse F ρ C)).length = (bottomGates C).length
  | dnf _ => rfl
  | cnf _ => rfl
  | gAnd gs => by
      show (bottomGates (gAnd (leafCollapseList F ρ gs))).length = (bottomGates (gAnd gs)).length
      rw [bottomGates_gAnd, bottomGates_gAnd]
      exact leafCollapseList_bottomGates_length F ρ gs
  | gOr gs => by
      show (bottomGates (gOr (leafCollapseList F ρ gs))).length = (bottomGates (gOr gs)).length
      rw [bottomGates_gOr, bottomGates_gOr]
      exact leafCollapseList_bottomGates_length F ρ gs
theorem leafCollapseList_bottomGates_length (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ gs : List (Layered n),
      (bottomGatesList (leafCollapseList F ρ gs)).length = (bottomGatesList gs).length
  | [] => rfl
  | g :: gs => by
      rw [leafCollapseList, bottomGatesList, bottomGatesList, List.length_append,
        List.length_append, leafCollapse_bottomGates_length F ρ g,
        leafCollapseList_bottomGates_length F ρ gs]
end

/-- **The survivor gate set is at most twice the bottom-gate count.**  `bottomGatesG C` is `bottomGates C`
together with the De Morgan duals, so its cardinality is `≤ 2·(bottomGates C).length`. -/
theorem bottomGatesG_card_le (C : Layered n) :
    (bottomGatesG C).card ≤ 2 * (bottomGates C).length := by
  rw [bottomGatesG]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_append, List.length_map]
  omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_bottomGates_length
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.bottomGatesG_card_le
