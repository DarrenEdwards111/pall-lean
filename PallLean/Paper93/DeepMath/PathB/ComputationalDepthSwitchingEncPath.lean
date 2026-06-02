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

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.encLits_subset_freeVars
