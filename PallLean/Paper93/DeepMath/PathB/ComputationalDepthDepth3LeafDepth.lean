import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafCollapse

/-!
# Tight switching, step 48: `leafCollapse` preserves depth (branch `razborov-recoverRho-wip`)

The clean half of the depth-counting termination: the leaf-switch `leafCollapse` (step 45) preserves the
alternation depth (`dnf ↔ cnf` are both depth 2; `gAnd`/`gOr` keep their child lists), so the entire depth
drop in a round comes from the merge pass.  Proved by the mutual `Layered`/`List` recursion.

* `leafCollapse_depth`, `leafCollapseList_depth` — depth/`depthList` invariance under `leafCollapse`.

Together with `mergePass`'s depth behaviour, this drives the termination count — modulo the alternation
invariant needed for the merge's *strict* reduction (a degenerate `gAnd []` would otherwise grow depth `1 → 2`
under the merge, so the invariant must encode non-empty, properly-polarised bottoms).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

mutual
theorem leafCollapse_depth (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ C : Layered n, depth (leafCollapse F ρ C) = depth C
  | dnf cs => rfl
  | cnf cs => rfl
  | gAnd gs => by
      show depth (gAnd (leafCollapseList F ρ gs)) = depth (gAnd gs)
      rw [depth_gAnd, depth_gAnd, leafCollapseList_depth F ρ gs]
  | gOr gs => by
      show depth (gOr (leafCollapseList F ρ gs)) = depth (gOr gs)
      rw [depth_gOr, depth_gOr, leafCollapseList_depth F ρ gs]
theorem leafCollapseList_depth (F : ℕ) (ρ : Fin n → Option Bool) :
    ∀ gs : List (Layered n), depthList (leafCollapseList F ρ gs) = depthList gs
  | [] => rfl
  | g :: gs => by
      show depthList (leafCollapse F ρ g :: leafCollapseList F ρ gs) = depthList (g :: gs)
      rw [depthList, depthList, leafCollapse_depth F ρ g, leafCollapseList_depth F ρ gs]
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_depth
