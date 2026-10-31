import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalComplete
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseCoreTight

/-!
# Block-DT model, route-2 step [169a]: the BLOCK leaf-recursive collapse (option (b) path (ii))

The block-tree twin of `leafCollapse` (the bit-level leaf collapse).  Each bottom gate of an arbitrary
`Layered` tower is switched `DNF → CNF` / `CNF → DNF` via the **block** canonical tree `canonicalDTree`
(no `toDTree` wrapper — `canonicalDTree` already returns a `DTree`), recursing through `gAnd`/`gOr`.
The whole tower is `EquivOn ρ` to its block leaf-collapse, using `canonicalDTree_eval` per leaf (which
needs `stars ρ < F` for enough fuel — strict, vs the bit version's `≤ F`).

Composed with `mergePass` this gives the block per-round oracle whose emitted clauses have width `< s`
directly from `canonicalDTree`-shallowness (no `canonicalDT ↔ canonicalDTree` depth bridge).

* `leafCollapseBlock` / `leafCollapseBlockList` — the mutual block leaf-collapse over `Layered`.
* `leafCollapseBlock_EquivOn` — `EquivOn ρ C (leafCollapseBlock w F ρ C)`, given `stars ρ < F`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_lcb {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem all_congr_lcb {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.all_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

-- The block leaf-recursive collapse: switch each bottom gate via the block canonical tree, recurse through gAnd/gOr.
mutual
def leafCollapseBlock (w F : ℕ) (ρ : Fin n → Option Bool) : Layered n → Layered n
  | dnf cs => cnf (dtreeToCNF (canonicalDTree cs w F ρ))
  | cnf cs => dnf (dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ)))
  | gAnd gs => gAnd (leafCollapseBlockList w F ρ gs)
  | gOr gs => gOr (leafCollapseBlockList w F ρ gs)
def leafCollapseBlockList (w F : ℕ) (ρ : Fin n → Option Bool) : List (Layered n) → List (Layered n)
  | [] => []
  | g :: gs => leafCollapseBlock w F ρ g :: leafCollapseBlockList w F ρ gs
end

/-- `leafCollapseBlockList` is the pointwise `leafCollapseBlock` map. -/
theorem leafCollapseBlockList_eq (w F : ℕ) (ρ : Fin n → Option Bool) (gs : List (Layered n)) :
    leafCollapseBlockList w F ρ gs = gs.map (leafCollapseBlock w F ρ) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [leafCollapseBlockList, List.map_cons, ih]

-- leafCollapseBlock_EquivOn: EquivOn ρ C (leafCollapseBlock w F ρ C), needing stars ρ < F (block fuel).
mutual
theorem leafCollapseBlock_EquivOn (w F : ℕ) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ < F) :
    ∀ C : Layered n, EquivOn ρ C (leafCollapseBlock w F ρ C)
  | dnf cs => fun x hx => by
      show eval (dnf cs) x = eval (cnf (dtreeToCNF (canonicalDTree cs w F ρ))) x
      rw [eval_dnf, eval_cnf, dtreeToCNF_eval, canonicalDTree_eval cs w F ρ x hstars hx]
  | cnf cs => fun x hx => by
      show eval (cnf cs) x
        = eval (dnf (dtreeToDNF (DTree.negTree (canonicalDTree (negDNF cs) w F ρ)))) x
      rw [eval_cnf, eval_dnf, dtreeToDNF_eval, DTree.negTree_eval,
        canonicalDTree_eval (negDNF cs) w F ρ x hstars hx,
        ← cnfValue_eq_not_dnfValue_negDNF]
  | gAnd gs => fun x hx => by
      show eval (gAnd gs) x = eval (gAnd (leafCollapseBlockList w F ρ gs)) x
      rw [leafCollapseBlockList_eq, eval_gAnd, eval_gAnd, List.all_map]
      exact all_congr_lcb gs (fun g => eval g x) (fun g => eval (leafCollapseBlock w F ρ g) x)
        (fun g hg => leafCollapseBlockList_EquivOn w F hstars gs g hg x hx)
  | gOr gs => fun x hx => by
      show eval (gOr gs) x = eval (gOr (leafCollapseBlockList w F ρ gs)) x
      rw [leafCollapseBlockList_eq, eval_gOr, eval_gOr, List.any_map]
      exact any_congr_lcb gs (fun g => eval g x) (fun g => eval (leafCollapseBlock w F ρ g) x)
        (fun g hg => leafCollapseBlockList_EquivOn w F hstars gs g hg x hx)
theorem leafCollapseBlockList_EquivOn (w F : ℕ) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ < F) :
    ∀ (gs : List (Layered n)), ∀ g ∈ gs, EquivOn ρ g (leafCollapseBlock w F ρ g)
  | [] => fun g hg => by simp at hg
  | g :: gs => fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact leafCollapseBlock_EquivOn w F hstars g'
      · exact leafCollapseBlockList_EquivOn w F hstars gs g' h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapseBlock_EquivOn
