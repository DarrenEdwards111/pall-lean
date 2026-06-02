import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# The encoder canonical block path (current-freeness)

**STATUS: REAL.  THE ENCODER PRODUCING THE PATH-LITERAL LIST.**

The canonical path processes terms in order, fixing each term's *current* free literals
(those still free under the partially-fixed restriction).  This produces the path-literal
list `encLits` — with distinct variables across terms (later terms' current-free literals
exclude already-fixed ones).  This file builds the path and proves its literals lie in the
starting `ρ`'s free variables (the foundation for distinctness and the `hterm` cover).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Fix all variables of a literal block (to `false`). -/
def fixBlock (ρ : Restriction n) (blk : List (Rung4Literal n)) : Restriction n :=
  fixOn ρ ((blk.map litVar).toFinset) (fun _ => false)

/-- The encoder path: process terms, fixing each term's current free literals. -/
def encLits (ρ : Restriction n) : List (Clause n) → List (Rung4Literal n)
  | [] => []
  | T :: ts => freeLits ρ T ++ encLits (fixBlock ρ (freeLits ρ T)) ts

/-- Fixing variables only shrinks the free set. -/
theorem freeVars_fixBlock_subset (ρ : Restriction n) (blk : List (Rung4Literal n)) :
    freeVars (fixBlock ρ blk) ⊆ freeVars ρ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases h : j ∈ (blk.map litVar).toFinset
  · simp [fixBlock, fixOn, h] at hj
  · simpa [fixBlock, fixOn, h] using hj

/-- **Encoder literals are `ρ`-free.**  Every variable of the encoder path was free in the
starting restriction. -/
theorem encLits_subset_freeVars (ρ : Restriction n) (cs : List (Clause n)) :
    ((encLits ρ cs).map litVar).toFinset ⊆ freeVars ρ := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    intro v hv
    simp only [encLits, List.map_append, List.toFinset_append, Finset.mem_union] at hv
    rcases hv with h | h
    · -- v in T's current-free block ⊆ freeVars ρ
      rw [List.mem_toFinset, List.mem_map] at h
      obtain ⟨ℓ, hℓ, hℓv⟩ := h
      rw [mem_freeVars, ← hℓv]
      have := (List.mem_filter.mp hℓ).2
      rw [litFree_var] at this
      exact Option.isNone_iff_eq_none.mp this
    · -- v in the recursive part ⊆ freeVars (fixBlock …) ⊆ freeVars ρ
      exact freeVars_fixBlock_subset ρ _ (ih (fixBlock ρ (freeLits ρ T)) h)

/-- A fixed-block variable is no longer free. -/
theorem fixBlock_fixed (ρ : Restriction n) (blk : List (Rung4Literal n)) {v : Fin n}
    (hv : v ∈ (blk.map litVar).toFinset) : (fixBlock ρ blk) v ≠ none := by
  simp [fixBlock, fixOn, hv]

/-- The current-free literals of a single term have distinct variables (a sublist of the
term's literals). -/
theorem freeLits_map_litVar_nodup (ρ : Restriction n) (T : Clause n)
    (hT : (T.lits.map litVar).Nodup) : ((freeLits ρ T).map litVar).Nodup := by
  have hsub : (freeLits ρ T).Sublist T.lits := List.filter_sublist
  exact hT.sublist (List.Sublist.map litVar hsub)

/-- **Distinct variables across the whole encoder path.**  Each term contributes only its
*current* free literals; later terms' blocks exclude already-fixed variables, so the full
path-literal list has no repeated variable.  (Requires each term to have distinct-variable
literals.) -/
theorem encLits_nodup (ρ : Restriction n) (cs : List (Clause n))
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup) :
    ((encLits ρ cs).map litVar).Nodup := by
  induction cs generalizing ρ with
  | nil => simp [encLits]
  | cons T ts ih =>
    simp only [encLits, List.map_append]
    rw [List.nodup_append]
    refine ⟨freeLits_map_litVar_nodup ρ T (hcs T (List.mem_cons.mpr (Or.inl rfl))),
            ih (fixBlock ρ (freeLits ρ T))
              (fun T' hT' => hcs T' (List.mem_cons.mpr (Or.inr hT'))), ?_⟩
    intro v hv1 b hb hvb
    subst hvb
    have hfree : (fixBlock ρ (freeLits ρ T)) v = none :=
      mem_freeVars.mp (encLits_subset_freeVars (fixBlock ρ (freeLits ρ T)) ts
        (List.mem_toFinset.mpr hb))
    exact fixBlock_fixed ρ (freeLits ρ T) (List.mem_toFinset.mpr hv1) hfree

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_subset_freeVars
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_nodup
