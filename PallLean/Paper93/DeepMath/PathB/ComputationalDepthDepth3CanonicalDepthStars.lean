import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalParity

/-!
# Block-DT model, foundation 31: the tight `w`-free depth bound (branch only)

The tight deterministic depth bound for the adaptive canonical tree: `depth ≤ stars σ` (no `w` factor),
for clauses with distinct variables.  Each block queries fresh free variables, so the total queried
along any path is at most the number of survivors.

* `canonicalDTree_depth_le_stars` — `depth ≤ stars σ` for distinct-variable clauses.

## Honest scope

This removes the spurious `w` factor from `depth ≤ F · w`.  But it **matches** the parity depth lower
bound `depth ≥ stars σ` (brick 30): so deterministically `depth = stars σ` for parity, and there is no
single-restriction contradiction (parity is genuinely depth-`stars σ`-computable).  The AC⁰ lower bound
still requires the probabilistic counting bridge.  No `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A guarded-`some` `filterMap` is a sublist of the corresponding `map`. -/
theorem filterMap_ite_sublist {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (g : α → β) :
    List.Sublist (l.filterMap (fun a => if p a then some (g a) else none)) (l.map g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · simp only [List.filterMap_cons, hp, if_true, List.map_cons]; exact ih.cons₂ _
    · simp only [List.filterMap_cons, hp, if_false, List.map_cons]; exact ih.cons _

/-- `freeVarsOf` is nodup when the clause's variables are distinct. -/
theorem freeVarsOf_nodup {σ : Fin n → Option Bool} {T : Clause n}
    (hnd : (T.lits.map litVarOf).Nodup) : (freeVarsOf σ T).Nodup := by
  have hsub : List.Sublist (freeVarsOf σ T) (T.lits.map litVarOf) := by
    rw [freeVarsOf]
    exact filterMap_ite_sublist T.lits (fun ℓ => σ (litVarOf ℓ) = none) litVarOf
  exact hnd.sublist hsub

/-- The free variables after extension: `freeVars σ` minus the queried variables. -/
theorem freeVars_extendσ {σ : Fin n → Option Bool} {T : Clause n} {a : Fin n → Bool} :
    freeVars (extendσ σ T a) = freeVars σ \ (freeVarsOf σ T).toFinset := by
  ext i
  simp only [mem_freeVars, Finset.mem_sdiff, List.mem_toFinset]
  rw [extendσ]
  by_cases hi : i ∈ freeVarsOf σ T
  · rw [if_pos hi]; simp [hi]
  · rw [if_neg hi]; simp [hi]

/-- The queried-variable finset lies in the free variables. -/
theorem freeVarsOf_toFinset_subset {σ : Fin n → Option Bool} {T : Clause n} :
    (freeVarsOf σ T).toFinset ⊆ freeVars σ := by
  intro v hv
  rw [List.mem_toFinset] at hv
  exact mem_freeVars.mpr (mem_freeVarsOf_none hv)

/-- Extension drops `stars` by exactly the queried-variable count. -/
theorem stars_extendσ_eq {σ : Fin n → Option Bool} {T : Clause n} {a : Fin n → Bool} :
    stars (extendσ σ T a) = stars σ - (freeVarsOf σ T).toFinset.card := by
  rw [stars, freeVars_extendσ, Finset.card_sdiff_of_subset freeVarsOf_toFinset_subset, stars]

/-- **The tight `w`-free depth bound.**  For clauses with distinct variables, the adaptive canonical
tree has depth `≤ stars σ`. -/
theorem canonicalDTree_depth_le_stars (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), (canonicalDTree cs w F σ).depth ≤ stars σ := by
  intro F
  induction F with
  | zero => intro σ; simp [canonicalDTree, DTree.depth]
  | succ F ih =>
    intro σ
    rw [canonicalDTree]
    split
    · simp [DTree.depth]
    · next hany =>
      cases hact : activeTerm cs σ with
      | none => simp [DTree.depth]
      | some T =>
        have hnodup : (freeVarsOf σ T).Nodup := freeVarsOf_nodup (hnd T (activeTerm_mem hact))
        have hcard : (freeVarsOf σ T).toFinset.card = (freeVarsOf σ T).length :=
          List.toFinset_card_of_nodup hnodup
        have hsub : (freeVarsOf σ T).toFinset.card ≤ stars σ :=
          Finset.card_le_card freeVarsOf_toFinset_subset
        refine le_trans (DTree.queryAll_depth (freeVarsOf σ T) _ _
          (stars σ - (freeVarsOf σ T).toFinset.card) ?_) ?_
        · intro a
          split
          · simp [DTree.depth]
          · rw [← stars_extendσ_eq]; exact ih (extendσ σ T a)
        · rw [← hcard]; omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_depth_le_stars
