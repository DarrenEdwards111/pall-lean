import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingConfirm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathClause

/-!
# The forward-decoder collection fold: `decode_encode_id` on the σ* layer

**STATUS: REAL.  THE MULTI-CLAUSE DECODER CLOSES.**

The capstone: the forward decoder walks `cs`, runs the free-and-confirm test per clause,
and collects the confirmed clauses' path variables.  With the per-clause variable sets
`pathClauseVars` (the label), this recovers exactly the path-variable set, and freeing it
from `σ*` returns `ρ`.

* `completionVars`: union over confirmed clauses of their labelled variable sets;
* `completionVars_eq`: it equals the path-variable set — ⟸ every path variable's clause
  confirms (`pathLits_clause_facts` + processed ⇒ satisfied/flips), ⟹ collected sets are
  path variables;
* `freeOn_completionVars_eq`: `freeOn σ* (completionVars …) = ρ` — `decode_encode_id` for
  the faithful multi-clause decoder.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Membership in a `foldr` of `Finset` unions. -/
theorem mem_foldr_union {l : List (Clause n)} {sel : Clause n → Finset (Fin n)} {v : Fin n} :
    v ∈ l.foldr (fun C acc => sel C ∪ acc) ∅ ↔ ∃ C ∈ l, v ∈ sel C := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨C, hC, hv⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨C, Or.inr hC, hv⟩
    · rintro ⟨C, (rfl | hC), hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨C, hC, hv⟩

/-- The decoder's collected variable set: union over confirmed clauses of their labelled
variable sets. -/
def completionVars (cs : List (Clause n)) (σstar : Restriction n)
    (sel : Clause n → Finset (Fin n)) : Finset (Fin n) :=
  (cs.filter (fun C => confirm σstar (sel C) C)).foldr (fun C acc => sel C ∪ acc) ∅

theorem completionVars_mem {cs : List (Clause n)} {σstar : Restriction n}
    {sel : Clause n → Finset (Fin n)} {v : Fin n} :
    v ∈ completionVars cs σstar sel ↔ ∃ C ∈ cs, confirm σstar (sel C) C = true ∧ v ∈ sel C := by
  unfold completionVars
  rw [mem_foldr_union]
  constructor
  · rintro ⟨C, hC, hv⟩
    rw [List.mem_filter] at hC
    exact ⟨C, hC.1, hC.2, hv⟩
  · rintro ⟨C, hCcs, hconf, hv⟩
    exact ⟨C, List.mem_filter.mpr ⟨hCcs, hconf⟩, hv⟩

/-- The label: the path variables lying in each clause. -/
def pathClauseVars (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) (C : Clause n) :
    Finset (Fin n) :=
  (C.lits.map litVar).toFinset ∩ ((pathLits cs ρ s).map litVar).toFinset

/-- `ρ` is free on every path variable. -/
theorem pathLits_free' (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    ∀ v ∈ (pathLits cs ρ s).map litVar, ρ v = none := by
  intro v hv
  rw [List.mem_map] at hv
  obtain ⟨ℓ, hℓ, hv⟩ := hv
  rw [← hv]; exact pathLits_free cs ρ s hℓ

/-- **The decoder collects exactly the path variables.** -/
theorem completionVars_eq (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    completionVars cs (complete ρ (pathLits cs ρ s)) (pathClauseVars cs ρ s)
      = ((pathLits cs ρ s).map litVar).toFinset := by
  classical
  ext v
  rw [completionVars_mem, List.mem_toFinset]
  constructor
  · rintro ⟨C, _, _, hvsel⟩
    rw [pathClauseVars, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hvsel
    exact hvsel.2
  · intro hv
    rw [List.mem_map] at hv
    obtain ⟨ℓ, hℓpath, hℓv⟩ := hv
    obtain ⟨C, hCcs, hℓC, hρ⟩ := pathLits_clause_facts cs ρ s ℓ hℓpath
    have hS : ∀ ℓ' ∈ C.lits,
        (litVar ℓ' ∈ pathClauseVars cs ρ s C ↔ litVar ℓ' ∈ (pathLits cs ρ s).map litVar) := by
      intro ℓ' hℓ'
      rw [pathClauseVars, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_map.mpr ⟨ℓ', hℓ', rfl⟩, h⟩⟩
    refine ⟨C, hCcs, ?_, ?_⟩
    · rw [confirm_complete_eq (pathLits_free' cs ρ s) hS,
        clauseSatisfied_complete_of_mem hℓpath hℓC (pathLits_nodup_litVar cs ρ s), hρ]
      simp
    · rw [pathClauseVars, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset]
      exact ⟨List.mem_map.mpr ⟨ℓ, hℓC, hℓv⟩, List.mem_map.mpr ⟨ℓ, hℓpath, hℓv⟩⟩

/-- **`decode_encode_id` (faithful multi-clause decoder).**  The decoder recovers `ρ` from
the satisfying completion and the per-clause labels — no path history, no `ρ`. -/
theorem freeOn_completionVars_eq (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    freeOn (complete ρ (pathLits cs ρ s))
      (completionVars cs (complete ρ (pathLits cs ρ s)) (pathClauseVars cs ρ s)) = ρ := by
  apply freeOn_complete_recover (pathLits_free' cs ρ s)
  intro j
  rw [completionVars_eq]
  exact List.mem_toFinset

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.completionVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_completionVars_eq
