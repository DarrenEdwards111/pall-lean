import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightCollapseOr

/-!
# Tight switching, step 45: the leaf-recursive collapse over `Layered` gates (branch `razborov-recoverRho-wip`)

The general-depth collapse: under a single restriction `ρ` (with `stars ρ ≤ F`, which the eval-correctness of
`canonicalDT_eval` is all that needs — shallowness is only for widths), every bottom gate of an arbitrarily
deep `Layered` tower is switched (`DNF → CNF` and `CNF → DNF` via the canonical tree), recursing through
`gAnd`/`gOr` nodes.  The whole tower is `EquivOn ρ` to its leaf-collapse — proved by the mutual
`Layered`/`List` recursion (the `toCircuit`/`toCircuitList` pattern), using the per-leaf canonical-tree
eval-correctness at `dnf`/`cnf` and `any`/`all` congruence at `gOr`/`gAnd`.

This is the round operating at the leaves of a deep tree (the existing collapse rounds were depth-4-bottom,
on clause-list gates); composed with merge it is the per-round oracle of the recursive tower.

* `leafCollapse` / `leafCollapseList` — the mutual leaf-collapse over `Layered`.
* `leafCollapse_EquivOn` — `EquivOn ρ C (leafCollapse F ρ C)`, unconditional in shallowness (only
  `stars ρ ≤ F`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_lc {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem all_congr_lc {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.all_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

-- The leaf-recursive collapse: switch each bottom gate (DNF<->CNF via the canonical tree), recurse through gAnd/gOr.
mutual
def leafCollapse (F : ℕ) (ρ : Fin n → Option Bool) : Layered n → Layered n
  | dnf cs => cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ)))
  | cnf cs => dnf (dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ))))
  | gAnd gs => gAnd (leafCollapseList F ρ gs)
  | gOr gs => gOr (leafCollapseList F ρ gs)
def leafCollapseList (F : ℕ) (ρ : Fin n → Option Bool) : List (Layered n) → List (Layered n)
  | [] => []
  | g :: gs => leafCollapse F ρ g :: leafCollapseList F ρ gs
end

/-- `leafCollapseList` is the pointwise `leafCollapse` map. -/
theorem leafCollapseList_eq (F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapseList F ρ gs = gs.map (leafCollapse F ρ) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [leafCollapseList, List.map_cons, ih]

-- leafCollapse_EquivOn: EquivOn ρ C (leafCollapse F ρ C), needing only stars ρ ≤ F (eval-correctness; shallowness unneeded).
mutual
theorem leafCollapse_EquivOn (F : ℕ) {ρ : Fin n → Option Bool} (hstars : SwitchingCounting.stars ρ ≤ F) :
    ∀ C : Layered n, EquivOn ρ C (leafCollapse F ρ C)
  | dnf cs => fun x hx => by
      show eval (dnf cs) x = eval (cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ)))) x
      rw [eval_dnf, eval_cnf, dtreeToCNF_eval, toDTree_eval, canonicalDT_eval F ρ x hstars hx,
        dnfEval_eq_dnfValue]
  | cnf cs => fun x hx => by
      show eval (cnf cs) x
        = eval (dnf (dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ))))) x
      rw [eval_cnf, eval_dnf, dtreeToDNF_eval, DTree.negTree_eval, toDTree_eval,
        canonicalDT_eval F ρ x hstars hx, dnfEval_eq_dnfValue, ← cnfValue_eq_not_dnfValue_negDNF]
  | gAnd gs => fun x hx => by
      show eval (gAnd gs) x = eval (gAnd (leafCollapseList F ρ gs)) x
      rw [leafCollapseList_eq, eval_gAnd, eval_gAnd, List.all_map]
      exact all_congr_lc gs (fun g => eval g x) (fun g => eval (leafCollapse F ρ g) x)
        (fun g hg => leafCollapseList_EquivOn F hstars gs g hg x hx)
  | gOr gs => fun x hx => by
      show eval (gOr gs) x = eval (gOr (leafCollapseList F ρ gs)) x
      rw [leafCollapseList_eq, eval_gOr, eval_gOr, List.any_map]
      exact any_congr_lc gs (fun g => eval g x) (fun g => eval (leafCollapse F ρ g) x)
        (fun g hg => leafCollapseList_EquivOn F hstars gs g hg x hx)
theorem leafCollapseList_EquivOn (F : ℕ) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ ≤ F) :
    ∀ (gs : List (Layered n)), ∀ g ∈ gs, EquivOn ρ g (leafCollapse F ρ g)
  | [] => fun g hg => by simp at hg
  | g :: gs => fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact leafCollapse_EquivOn F hstars g'
      · exact leafCollapseList_EquivOn F hstars gs g' h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_EquivOn
