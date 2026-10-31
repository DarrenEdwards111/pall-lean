import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepInput

/-!
# Block-DT model, foundation 40: branching holography, step 3a — per-block restriction decoder (branch only)

The first ingredient of the switching-lemma encoding injection.  The encoding records the deep path as a
"smaller" restriction (one that fixes the path's variables) plus a per-block *label* recording which of
the term's variables were freed.  The decoder must un-fix one block — recover the previous restriction
`σ` from the extended `extendσ σ T a` given the freed-variable set.

* `resetVars σ' vs` — set the listed variables back to `none` in `σ'`.
* `resetVars_extendσ` — un-fixing the freed variables inverts `extendσ`: `resetVars (extendσ σ T a)
  (freeVarsOf σ T) = σ`.  So the freed-variable set is exactly the label needed to decode one block.
* `freeVarsOf_subset_litVars` / `freeVarsOf_length_le` — the freed set is a subset of the term's
  variables, of size `≤ #literals`; hence the per-block label lives in a space of size `≤ 2^w`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Reset the listed variables to `none` in a restriction. -/
def resetVars (σ' : Fin n → Option Bool) (vs : List (Fin n)) : Fin n → Option Bool :=
  fun i => if i ∈ vs then none else σ' i

/-- **One-block decoder.**  Un-fixing the freed variables inverts the block extension: given the freed
set `freeVarsOf σ T`, resetting them in `extendσ σ T a` recovers `σ`. -/
theorem resetVars_extendσ (σ : Fin n → Option Bool) (T : Clause n) (a : Fin n → Bool) :
    resetVars (extendσ σ T a) (freeVarsOf σ T) = σ := by
  funext i
  rw [resetVars, extendσ]
  by_cases hi : i ∈ freeVarsOf σ T
  · rw [if_pos hi]; exact (mem_freeVarsOf_none hi).symm
  · rw [if_neg hi, if_neg hi]

/-- The freed variables of a term are among the term's literal-variables. -/
theorem freeVarsOf_subset_litVars (σ : Fin n → Option Bool) (T : Clause n) :
    ∀ v ∈ freeVarsOf σ T, v ∈ T.lits.map litVarOf := by
  intro v hv
  rw [freeVarsOf, List.mem_filterMap] at hv
  obtain ⟨ℓ, hℓ, he⟩ := hv
  rw [List.mem_map]
  refine ⟨ℓ, hℓ, ?_⟩
  by_cases hc : σ (litVarOf ℓ) = none
  · rw [if_pos hc] at he
    exact Option.some.inj he
  · rw [if_neg hc] at he
    exact absurd he (by simp)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.resetVars_extendσ
