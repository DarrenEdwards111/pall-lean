import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreshClauses
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToDNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NegTree

/-!
# AC⁰ reduction, foundation 18: DNF-side clause well-formedness (branch only)

The dual of brick 14 (`dtreeToCNF_nodup`/`_consistent`).  The *dual* collapse round converts a fresh tree
to a DNF (`dtreeToDNF`, brick 66) — via the De Morgan / `negTree` route — so for that round's output to
re-enter the next round we need the same well-formedness on the *DNF* side: a fresh tree's accepting-path
DNF has distinct-variable, consistent terms.  We also record that leaf-negation (`negTree`) preserves
freshness, which is what carries the fresh canonical tree of the negated gate through the dual round.

* `DTree.negTree_fresh` — negating a tree's leaves preserves freshness (it leaves `queriedVars` unchanged).
* `dtreeToDNF_litVars_subset` / `dtreeToDNF_nodup` / `dtreeToDNF_consistent` — the DNF-side analogues of
  brick 14.

Composed with bricks 14/15 this closes the round-to-round preservation for *both* alternation parities.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace DTree

variable {n : ℕ}

/-- Leaf-negation leaves the queried variables unchanged. -/
theorem negTree_queriedVars (t : DTree n) : (negTree t).queriedVars = t.queriedVars := by
  induction t with
  | leaf b => rfl
  | node v lo hi ihlo ihhi => rw [negTree, queriedVars, queriedVars, ihlo, ihhi]

/-- **Leaf-negation preserves freshness.** -/
theorem negTree_fresh : ∀ (t : DTree n), t.fresh → (negTree t).fresh := by
  intro t
  induction t with
  | leaf b => intro _; trivial
  | node v lo hi ihlo ihhi =>
    intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [negTree]
    refine ⟨?_, ?_, ihlo h3, ihhi h4⟩
    · rw [negTree_queriedVars]; exact h1
    · rw [negTree_queriedVars]; exact h2

end DTree

variable {n : ℕ}

private theorem litVarOf_pos' (v : Fin n) : litVarOf (Rung4Literal.pos v) = v := rfl
private theorem litVarOf_neg' (v : Fin n) : litVarOf (Rung4Literal.neg v) = v := rfl

/-- A DNF term's variables are among the tree's queried variables. -/
theorem dtreeToDNF_litVars_subset :
    ∀ (t : DTree n), ∀ C ∈ dtreeToDNF t, ∀ w ∈ C.lits.map litVarOf, w ∈ DTree.queriedVars t := by
  intro t
  induction t with
  | leaf b => cases b <;> simp [dtreeToDNF, DTree.queriedVars]
  | node v lo hi ihlo ihhi =>
    intro C hC w hw
    rw [dtreeToDNF, List.mem_append] at hC
    rw [DTree.queriedVars, Finset.mem_insert, Finset.mem_union]
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.mem_cons, litVarOf_pos'] at hw
      rcases hw with hwv | hwc
      · left; exact hwv
      · right; right; exact ihhi C' hC' w hwc
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.mem_cons, litVarOf_neg'] at hw
      rcases hw with hwv | hwc
      · left; exact hwv
      · right; left; exact ihlo C' hC' w hwc

/-- **Distinct variables.**  Every term of a fresh tree's DNF has distinct literal-variables. -/
theorem dtreeToDNF_nodup :
    ∀ (t : DTree n), t.fresh → ∀ C ∈ dtreeToDNF t, (C.lits.map litVarOf).Nodup := by
  intro t
  induction t with
  | leaf b => intro _ C hC; cases b <;> simp_all [dtreeToDNF]
  | node v lo hi ihlo ihhi =>
    intro ht C hC
    simp only [DTree.fresh] at ht
    obtain ⟨hvlo, hvhi, hflo, hfhi⟩ := ht
    rw [dtreeToDNF, List.mem_append] at hC
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.nodup_cons, litVarOf_pos']
      exact ⟨fun hmem => hvhi (dtreeToDNF_litVars_subset hi C' hC' v hmem), ihhi hfhi C' hC'⟩
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      simp only [List.map_cons, List.nodup_cons, litVarOf_neg']
      exact ⟨fun hmem => hvlo (dtreeToDNF_litVars_subset lo C' hC' v hmem), ihlo hflo C' hC'⟩

/-- **Consistency.**  Every term of a fresh tree's DNF has no variable with both signs. -/
theorem dtreeToDNF_consistent :
    ∀ (t : DTree n), t.fresh → ∀ C ∈ dtreeToDNF t, Consistent C := by
  intro t
  induction t with
  | leaf b => intro _ C hC; cases b <;> simp_all [dtreeToDNF, Consistent]
  | node v lo hi ihlo ihhi =>
    intro ht C hC
    simp only [DTree.fresh] at ht
    obtain ⟨hvlo, hvhi, hflo, hfhi⟩ := ht
    rw [dtreeToDNF, List.mem_append] at hC
    cases hC with
    | inl h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      intro u ⟨hp, hn⟩
      simp only [List.mem_cons] at hp hn
      rcases hn with hnv | hnc
      · exact absurd hnv (by simp)
      · rcases hp with hpv | hpc
        · injection hpv with huv
          have hu : u ∈ DTree.queriedVars hi :=
            dtreeToDNF_litVars_subset hi C' hC' u (List.mem_map_of_mem hnc)
          rw [huv] at hu
          exact hvhi hu
        · exact ihhi hfhi C' hC' u ⟨hpc, hnc⟩
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨C', hC', rfl⟩ := h
      intro u ⟨hp, hn⟩
      simp only [List.mem_cons] at hp hn
      rcases hp with hpv | hpc
      · exact absurd hpv (by simp)
      · rcases hn with hnv | hnc
        · injection hnv with huv
          have hu : u ∈ DTree.queriedVars lo :=
            dtreeToDNF_litVars_subset lo C' hC' u (List.mem_map_of_mem hpc)
          rw [huv] at hu
          exact hvlo hu
        · exact ihlo hflo C' hC' u ⟨hpc, hnc⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.negTree_fresh
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToDNF_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToDNF_consistent
