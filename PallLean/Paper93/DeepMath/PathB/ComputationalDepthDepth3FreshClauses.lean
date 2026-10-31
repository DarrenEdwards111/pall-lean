import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToCNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# AC⁰ reduction, foundation 14: clause well-formedness from a fresh tree (branch only)

The intermediate-hypothesis preservation the multi-round recursion needs: converting a decision tree to a
CNF (bricks 66–67) yields clauses that are **distinct-variable** and **consistent** — provided the tree
never re-queries a variable along a path (`fresh`).  Those are exactly the switching hypotheses
(`Nodup`, `Consistent`) the *next* round requires of the gates it acts on.

* `DTree.queriedVars` / `DTree.fresh` — the variables a tree queries, and "no variable queried twice".
* `dtreeToCNF_litVars_subset` — a clause's variables are among the tree's queried variables.
* `dtreeToCNF_nodup` / `dtreeToCNF_consistent` — for a fresh tree, every clause has distinct variables and
  no variable with both signs.

This reduces the round-to-round preservation to the concrete claim "`canonicalDTree` is `fresh`" — the
next target.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace DTree

variable {n : ℕ}

/-- The set of variables a decision tree queries. -/
def queriedVars : DTree n → Finset (Fin n)
  | leaf _ => ∅
  | node v lo hi => insert v (queriedVars lo ∪ queriedVars hi)

/-- A decision tree is fresh if no variable is queried twice along any path. -/
def fresh : DTree n → Prop
  | leaf _ => True
  | node v lo hi => v ∉ queriedVars lo ∧ v ∉ queriedVars hi ∧ fresh lo ∧ fresh hi

end DTree

variable {n : ℕ}

private theorem litVarOf_pos (v : Fin n) : litVarOf (Rung4Literal.pos v) = v := rfl
private theorem litVarOf_neg (v : Fin n) : litVarOf (Rung4Literal.neg v) = v := rfl

/-- A clause's variables are among the tree's queried variables. -/
theorem dtreeToCNF_litVars_subset :
    ∀ (t : DTree n), ∀ C ∈ dtreeToCNF t, ∀ w ∈ C.lits.map litVarOf, w ∈ DTree.queriedVars t := by
  intro t
  induction t with
  | leaf b => cases b <;> simp [dtreeToCNF, DTree.queriedVars]
  | node v lo hi ihlo ihhi =>
    intro C hC w hw
    rw [dtreeToCNF, List.mem_append] at hC
    rw [DTree.queriedVars, Finset.mem_insert, Finset.mem_union]
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.mem_cons, litVarOf_neg] at hw
      cases hw with
      | inl hwv => exact Or.inl hwv
      | inr hw' => exact Or.inr (Or.inr (ihhi C' hC' w hw'))
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.mem_cons, litVarOf_pos] at hw
      cases hw with
      | inl hwv => exact Or.inl hwv
      | inr hw' => exact Or.inr (Or.inl (ihlo C' hC' w hw'))

/-- **Distinct variables.**  Every clause of a fresh tree's CNF has distinct literal-variables. -/
theorem dtreeToCNF_nodup :
    ∀ (t : DTree n), t.fresh → ∀ C ∈ dtreeToCNF t, (C.lits.map litVarOf).Nodup := by
  intro t
  induction t with
  | leaf b => intro _ C hC; cases b <;> simp_all [dtreeToCNF]
  | node v lo hi ihlo ihhi =>
    intro ht C hC
    simp only [DTree.fresh] at ht
    obtain ⟨hvlo, hvhi, hflo, hfhi⟩ := ht
    rw [dtreeToCNF, List.mem_append] at hC
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.nodup_cons, litVarOf_neg]
      exact ⟨fun hmem => hvhi (dtreeToCNF_litVars_subset hi C' hC' v hmem), ihhi hfhi C' hC'⟩
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.nodup_cons, litVarOf_pos]
      exact ⟨fun hmem => hvlo (dtreeToCNF_litVars_subset lo C' hC' v hmem), ihlo hflo C' hC'⟩

/-- **Consistency.**  Every clause of a fresh tree's CNF has no variable with both signs. -/
theorem dtreeToCNF_consistent :
    ∀ (t : DTree n), t.fresh → ∀ C ∈ dtreeToCNF t, Consistent C := by
  intro t
  induction t with
  | leaf b => intro _ C hC; cases b <;> simp_all [dtreeToCNF, Consistent]
  | node v lo hi ihlo ihhi =>
    intro ht C hC
    simp only [DTree.fresh] at ht
    obtain ⟨hvlo, hvhi, hflo, hfhi⟩ := ht
    rw [dtreeToCNF, List.mem_append] at hC
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      intro u ⟨hp, hn⟩
      simp only [List.mem_cons] at hp hn
      rcases hp with hpv | hpc
      · exact absurd hpv (by simp)
      · rcases hn with hnv | hnc
        · injection hnv with huv
          have hu : u ∈ DTree.queriedVars hi :=
            dtreeToCNF_litVars_subset hi C' hC' u (List.mem_map_of_mem hpc)
          rw [huv] at hu
          exact hvhi hu
        · exact ihhi hfhi C' hC' u ⟨hpc, hnc⟩
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      intro u ⟨hp, hn⟩
      simp only [List.mem_cons] at hp hn
      rcases hn with hnv | hnc
      · exact absurd hnv (by simp)
      · rcases hp with hpv | hpc
        · injection hpv with huv
          have hu : u ∈ DTree.queriedVars lo :=
            dtreeToCNF_litVars_subset lo C' hC' u (List.mem_map_of_mem hnc)
          rw [huv] at hu
          exact hvlo hu
        · exact ihlo hflo C' hC' u ⟨hpc, hnc⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToCNF_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToCNF_consistent
