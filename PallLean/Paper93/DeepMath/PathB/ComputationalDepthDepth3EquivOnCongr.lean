import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# Tight switching, step 42: `EquivOn` tree congruence (branch `razborov-recoverRho-wip`)

The structural glue for the leaf-recursive oracle: collapsing each child gate of a `gOr`/`gAnd` lifts to an
`EquivOn` of the whole node.  So when the bottom-two-levels of a deep `Layered` tower are collapsed gate by
gate (under one shared restriction), the parent node — and inductively the whole tree — is `EquivOn` to the
collapsed tower.

* `EquivOn_gOr_congr`, `EquivOn_gAnd_congr` — congruence of `EquivOn` under `gOr`/`gAnd` over mapped child
  lists.

This is the per-level congruence the leaf-recursion composes through the tree (with the per-gate collapse
`collapse_core_tight_list` at the leaves and the merge combinators `collapse_then_merge_*` to restore the
alternation).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_eo {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem all_congr_eo {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.all_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- **`gOr` congruence.**  If each child collapses (`EquivOn ρ (f C) (g C)`), the `OR` nodes are `EquivOn`. -/
theorem EquivOn_gOr_congr {ρ : Fin n → Option Bool} {α : Type*} (l : List α)
    (f g : α → Layered n) (h : ∀ C ∈ l, EquivOn ρ (f C) (g C)) :
    EquivOn ρ (gOr (l.map f)) (gOr (l.map g)) := by
  intro x hx
  rw [eval_gOr, eval_gOr, List.any_map, List.any_map]
  exact any_congr_eo l (fun C => eval (f C) x) (fun C => eval (g C) x) (fun C hC => h C hC x hx)

/-- **`gAnd` congruence.**  If each child collapses (`EquivOn ρ (f C) (g C)`), the `AND` nodes are `EquivOn`. -/
theorem EquivOn_gAnd_congr {ρ : Fin n → Option Bool} {α : Type*} (l : List α)
    (f g : α → Layered n) (h : ∀ C ∈ l, EquivOn ρ (f C) (g C)) :
    EquivOn ρ (gAnd (l.map f)) (gAnd (l.map g)) := by
  intro x hx
  rw [eval_gAnd, eval_gAnd, List.all_map, List.all_map]
  exact all_congr_eo l (fun C => eval (f C) x) (fun C => eval (g C) x) (fun C hC => h C hC x hx)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.EquivOn_gOr_congr
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.EquivOn_gAnd_congr
