import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# The encoder canonical block path (satisfying-completion tracked)

**STATUS: REAL.  THE ENCODER PRODUCING THE PATH-LITERAL LIST.**

The canonical path processes terms left to right against the *accumulating satisfying
completion* `σ` (so the global completion is `complete ρ (encLits ρ cs)`).  At each term:

* if the term is already **falsified** under `σ`, it is **skipped** (its literals must not
  enter the path — a falsified term is not satisfied under the completion, so including its
  literals would break the `hterm` cover);
* otherwise it contributes its **current** free literals `freeLits σ T`, and the state
  advances by satisfying them (`complete σ (freeLits σ T)`).

This produces the path-literal list `encLits` — with distinct variables across terms (later
terms' current-free literals are on still-free variables, disjoint from already-fixed ones).
This file builds the path and proves it lies in the starting `ρ`'s free variables and has
distinct variables (the foundations for the `hterm` cover).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A variable touched by the satisfying completion is fixed (never `none`). -/
theorem complete_ne_none_of_mem (l : List (Rung4Literal n)) :
    ∀ (ρ : Restriction n) {v : Fin n}, v ∈ l.map litVar → complete ρ l v ≠ none := by
  induction l with
  | nil => intro ρ v h; simp at h
  | cons a t ih =>
    intro ρ v h
    rw [List.map_cons, List.mem_cons] at h
    rw [complete_cons]
    rcases h with rfl | h
    · by_cases hvt : litVar a ∈ t.map litVar
      · exact ih (satFix ρ a) hvt
      · rw [complete_apply_eq_of_not_mem (satFix ρ a) t (litVar a) hvt, satFix,
          Function.update_self]; simp
    · exact ih (satFix ρ a) h

/-- Satisfying-completing a literal list only shrinks the free set. -/
theorem freeVars_complete_subset (ρ : Restriction n) (l : List (Rung4Literal n)) :
    freeVars (complete ρ l) ⊆ freeVars ρ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases h : j ∈ l.map litVar
  · exact absurd hj (complete_ne_none_of_mem l ρ h)
  · rw [complete_apply_eq_of_not_mem ρ l j h] at hj; exact hj

/-- The encoder path: process terms left to right against the accumulating satisfying
completion, skipping terms already falsified, contributing each live term's current free
literals. -/
def encLits (ρ : Restriction n) : List (Clause n) → List (Rung4Literal n)
  | [] => []
  | T :: ts =>
      if termFalsified ρ T then encLits ρ ts
      else freeLits ρ T ++ encLits (complete ρ (freeLits ρ T)) ts

/-- **Encoder literals are `ρ`-free.**  Every variable of the encoder path was free in the
starting restriction. -/
theorem encLits_subset_freeVars (ρ : Restriction n) (cs : List (Clause n)) :
    ((encLits ρ cs).map litVar).toFinset ⊆ freeVars ρ := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    simp only [encLits]
    split
    · exact ih ρ
    · intro v hv
      simp only [List.map_append, List.toFinset_append, Finset.mem_union] at hv
      rcases hv with h | h
      · rw [List.mem_toFinset, List.mem_map] at h
        obtain ⟨ℓ, hℓ, hℓv⟩ := h
        rw [mem_freeVars, ← hℓv]
        have := (List.mem_filter.mp hℓ).2
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this
      · exact freeVars_complete_subset ρ _ (ih (complete ρ (freeLits ρ T)) h)

/-- The current-free literals of a single term have distinct variables (a sublist of the
term's literals). -/
theorem freeLits_map_litVar_nodup (ρ : Restriction n) (T : Clause n)
    (hT : (T.lits.map litVar).Nodup) : ((freeLits ρ T).map litVar).Nodup := by
  have hsub : (freeLits ρ T).Sublist T.lits := List.filter_sublist
  exact hT.sublist (List.Sublist.map litVar hsub)

/-- **Distinct variables across the whole encoder path.**  Each live term contributes only
its *current* free literals, on still-free variables disjoint from already-fixed ones, so the
full path-literal list has no repeated variable.  (Requires each term to have distinct-variable
literals.) -/
theorem encLits_nodup (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ((encLits ρ cs).map litVar).Nodup := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    simp only [encLits]
    split
    · exact ih ρ (fun T' hT' => hcs T' (List.mem_cons.mpr (Or.inr hT')))
    · simp only [List.map_append]
      rw [List.nodup_append]
      refine ⟨freeLits_map_litVar_nodup ρ T (hcs T (List.mem_cons.mpr (Or.inl rfl))),
              ih (complete ρ (freeLits ρ T))
                (fun T' hT' => hcs T' (List.mem_cons.mpr (Or.inr hT'))), ?_⟩
      intro v hv1 b hb hvb
      subst hvb
      have hfree : complete ρ (freeLits ρ T) v = none :=
        mem_freeVars.mp (encLits_subset_freeVars (complete ρ (freeLits ρ T)) ts
          (List.mem_toFinset.mpr hb))
      exact complete_ne_none_of_mem (freeLits ρ T) ρ hv1 hfree

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_nodup
