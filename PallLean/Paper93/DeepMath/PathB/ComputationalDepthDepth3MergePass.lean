import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayeredMerge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# Tight switching, step 46: the merge pass (depth reduction after the leaf-switch) (branch `razborov-recoverRho-wip`)

`leafCollapse` (step 45) switches each bottom gate (`DNF ↔ CNF`) but keeps the tree shape; the depth drop
comes from **merging the same-type siblings created by the switch**: after the switch a bottom `gAnd`-of-`cnf`
becomes a single `cnf` (and `gOr`-of-`dnf` a single `dnf`), one level shorter.  The merge pass detects an
all-`cnf` (all-`dnf`) child list and flattens it (`merge_gAnd_cnf` / `merge_gOr_dnf`), else recurses.

* `allCnf` / `allDnf` — detect a uniform child list and extract its clause-lists.
* `mergePass` / `mergePassList` — the recursive merge pass.
* `mergePass_EquivOn` — `EquivOn ρ C (mergePass C)`, unconditional (merges are eval-preserving).

Composed with `leafCollapse` (step 45) this is the depth-reducing round: `mergePass (leafCollapse F ρ C)`
switches the bottom and collapses the resulting uniform siblings — the per-round oracle of the recursive
tower at any depth.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

private theorem any_congr_mp {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.any_cons, List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem all_congr_mp {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.all_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Extract the clause-lists if every child is a `cnf`. -/
def allCnf : List (Layered n) → Option (List (List (Clause n)))
  | [] => some []
  | cnf c :: gs => (allCnf gs).map (fun css => c :: css)
  | _ :: _ => none

/-- Extract the clause-lists if every child is a `dnf`. -/
def allDnf : List (Layered n) → Option (List (List (Clause n)))
  | [] => some []
  | dnf c :: gs => (allDnf gs).map (fun dss => c :: dss)
  | _ :: _ => none

theorem allCnf_some : ∀ {gs : List (Layered n)} {css}, allCnf gs = some css → gs = css.map cnf
  | [], css, h => by simp only [allCnf, Option.some.injEq] at h; rw [← h]; rfl
  | cnf c :: gs, css, h => by
      simp only [allCnf, Option.map_eq_some_iff] at h
      obtain ⟨css', hgs, rfl⟩ := h
      rw [List.map_cons, ← allCnf_some hgs]
  | dnf _ :: _, _, h => by simp [allCnf] at h
  | gAnd _ :: _, _, h => by simp [allCnf] at h
  | gOr _ :: _, _, h => by simp [allCnf] at h

theorem allDnf_some : ∀ {gs : List (Layered n)} {dss}, allDnf gs = some dss → gs = dss.map dnf
  | [], dss, h => by simp only [allDnf, Option.some.injEq] at h; rw [← h]; rfl
  | dnf c :: gs, dss, h => by
      simp only [allDnf, Option.map_eq_some_iff] at h
      obtain ⟨dss', hgs, rfl⟩ := h
      rw [List.map_cons, ← allDnf_some hgs]
  | cnf _ :: _, _, h => by simp [allDnf] at h
  | gAnd _ :: _, _, h => by simp [allDnf] at h
  | gOr _ :: _, _, h => by simp [allDnf] at h

-- The recursive merge pass: collapse a uniform bottom gAnd-of-cnf / gOr-of-dnf, else recurse.
mutual
def mergePass : Layered n → Layered n
  | dnf cs => dnf cs
  | cnf cs => cnf cs
  | gAnd gs => match allCnf gs with | some css => cnf css.flatten | none => gAnd (mergePassList gs)
  | gOr gs => match allDnf gs with | some dss => dnf dss.flatten | none => gOr (mergePassList gs)
def mergePassList : List (Layered n) → List (Layered n)
  | [] => []
  | g :: gs => mergePass g :: mergePassList gs
end

theorem mergePassList_eq (gs : List (Layered n)) :
    mergePassList gs = gs.map mergePass := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [mergePassList, List.map_cons, ih]

mutual
theorem mergePass_EquivOn (ρ : Fin n → Option Bool) :
    ∀ C : Layered n, EquivOn ρ C (mergePass C)
  | dnf cs => fun _ _ => rfl
  | cnf cs => fun _ _ => rfl
  | gAnd gs => by
      cases h : allCnf gs with
      | some css =>
          have hgs := allCnf_some h
          have : mergePass (gAnd gs) = cnf css.flatten := by simp only [mergePass, h]
          rw [this, hgs]; exact merge_gAnd_cnf_EquivOn ρ css
      | none =>
          have : mergePass (gAnd gs) = gAnd (mergePassList gs) := by simp only [mergePass, h]
          rw [this, mergePassList_eq]
          intro x hx
          rw [eval_gAnd, eval_gAnd, List.all_map]
          exact all_congr_mp gs (fun g => eval g x) (fun g => eval (mergePass g) x)
            (fun g hg => mergePassList_EquivOn ρ gs g hg x hx)
  | gOr gs => by
      cases h : allDnf gs with
      | some dss =>
          have hgs := allDnf_some h
          have : mergePass (gOr gs) = dnf dss.flatten := by simp only [mergePass, h]
          rw [this, hgs]; exact merge_gOr_dnf_EquivOn ρ dss
      | none =>
          have : mergePass (gOr gs) = gOr (mergePassList gs) := by simp only [mergePass, h]
          rw [this, mergePassList_eq]
          intro x hx
          rw [eval_gOr, eval_gOr, List.any_map]
          exact any_congr_mp gs (fun g => eval g x) (fun g => eval (mergePass g) x)
            (fun g hg => mergePassList_EquivOn ρ gs g hg x hx)
theorem mergePassList_EquivOn (ρ : Fin n → Option Bool) :
    ∀ (gs : List (Layered n)), ∀ g ∈ gs, EquivOn ρ g (mergePass g)
  | [] => fun g hg => by simp at hg
  | g :: gs => fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact mergePass_EquivOn ρ g'
      · exact mergePassList_EquivOn ρ gs g' h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_EquivOn
