import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreshClauses

/-!
# AC⁰ reduction, foundation 15: the canonical tree is fresh (branch only)

The concrete input that brick 79 (`dtreeToCNF_nodup`/`dtreeToCNF_consistent`) reduces the round-to-round
preservation to: the adaptive canonical decision tree never queries a variable twice on any path.

The argument is two intertwined facts:

* `canonicalDTree_queriedVars_unset` — every variable the tree queries is **unset** (`= none`) in the
  restriction `σ` at the root.  This is the heart: at each block we query the active term's *free*
  variables (unset by definition), then recurse on `extendσ`, which **sets** exactly those variables, so
  no deeper query can revisit them.
* `canonicalDTree_fresh` — hence, provided each clause has distinct variables (`Nodup` of its
  `litVarOf` list — the same hypothesis the switching gates carry), the tree is `fresh`.

Composed with brick 79 this gives: the per-round `canonicalDTree` collapses to clauses that are `Nodup`
and `Consistent`, exactly the hypotheses the *next* collapse round requires.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A free variable of a term under `σ` is unset in `σ`. -/
theorem mem_freeVarsOf {σ : Fin n → Option Bool} {T : Clause n} {v : Fin n}
    (h : v ∈ freeVarsOf σ T) : σ v = none := by
  rw [freeVarsOf, List.mem_filterMap] at h
  obtain ⟨ℓ, _, hℓ⟩ := h
  by_cases hc : σ (litVarOf ℓ) = none
  · rw [if_pos hc] at hℓ
    injection hℓ with hv
    rw [← hv]; exact hc
  · rw [if_neg hc] at hℓ
    exact absurd hℓ (by simp)

/-- `freeVarsOf` is a sublist of the term's full variable list. -/
theorem freeVarsOf_sublist (σ : Fin n → Option Bool) (T : Clause n) :
    List.Sublist (freeVarsOf σ T) (T.lits.map litVarOf) := by
  rw [freeVarsOf]
  generalize T.lits = ls
  induction ls with
  | nil => simp
  | cons ℓ ls ih =>
    rw [List.map_cons]
    by_cases hc : σ (litVarOf ℓ) = none
    · have hstep : (ℓ :: ls).filterMap
            (fun ℓ => if σ (litVarOf ℓ) = none then some (litVarOf ℓ) else none)
          = litVarOf ℓ :: ls.filterMap
            (fun ℓ => if σ (litVarOf ℓ) = none then some (litVarOf ℓ) else none) := by
        simp [hc]
      rw [hstep]; exact ih.cons₂ _
    · have hstep : (ℓ :: ls).filterMap
            (fun ℓ => if σ (litVarOf ℓ) = none then some (litVarOf ℓ) else none)
          = ls.filterMap
            (fun ℓ => if σ (litVarOf ℓ) = none then some (litVarOf ℓ) else none) := by
        simp [hc]
      rw [hstep]; exact ih.cons _

/-- If a term's variables are distinct, so are its free variables under any `σ`. -/
theorem freeVarsOf_nodup {σ : Fin n → Option Bool} {T : Clause n}
    (h : (T.lits.map litVarOf).Nodup) : (freeVarsOf σ T).Nodup :=
  List.Nodup.sublist (freeVarsOf_sublist σ T) h

/-- A variable queried by `queryAll` is either one of the queried `vars` or queried by some
continuation leaf. -/
theorem queryAll_queriedVars_mem (vars : List (Fin n)) (k : (Fin n → Bool) → DTree n) {v : Fin n} :
    ∀ acc, v ∈ DTree.queriedVars (DTree.queryAll vars acc k) →
      v ∈ vars ∨ ∃ a, v ∈ DTree.queriedVars (k a) := by
  induction vars with
  | nil => intro acc h; right; exact ⟨acc, h⟩
  | cons u us ih =>
    intro acc h
    rw [DTree.queryAll, DTree.queriedVars, Finset.mem_insert, Finset.mem_union] at h
    rcases h with hv | hlo | hhi
    · left; simp [hv]
    · rcases ih (Function.update acc u false) hlo with hin | hex
      · left; exact List.mem_cons_of_mem _ hin
      · right; exact hex
    · rcases ih (Function.update acc u true) hhi with hin | hex
      · left; exact List.mem_cons_of_mem _ hin
      · right; exact hex

/-- `queryAll` is fresh when its variable list is `Nodup`, every continuation is fresh, and no
continuation queries any of the listed variables. -/
theorem queryAll_fresh (k : (Fin n → Bool) → DTree n) (hkfresh : ∀ a, (k a).fresh) :
    ∀ (vars : List (Fin n)), vars.Nodup →
      (∀ v ∈ vars, ∀ a, v ∉ DTree.queriedVars (k a)) →
      ∀ acc, (DTree.queryAll vars acc k).fresh := by
  intro vars
  induction vars with
  | nil => intro _ _ acc; exact hkfresh acc
  | cons u us ih =>
    intro hnd hkavoid acc
    rw [DTree.queryAll]
    have hunotin : u ∉ us := (List.nodup_cons.mp hnd).1
    have hndus : us.Nodup := (List.nodup_cons.mp hnd).2
    have hkavoidus : ∀ v ∈ us, ∀ a, v ∉ DTree.queriedVars (k a) :=
      fun v hv => hkavoid v (List.mem_cons_of_mem _ hv)
    refine ⟨?_, ?_, ih hndus hkavoidus _, ih hndus hkavoidus _⟩
    · intro hmem
      rcases queryAll_queriedVars_mem us k (Function.update acc u false) hmem with hin | ⟨a, ha⟩
      · exact hunotin hin
      · exact hkavoid u (List.mem_cons_self ..) a ha
    · intro hmem
      rcases queryAll_queriedVars_mem us k (Function.update acc u true) hmem with hin | ⟨a, ha⟩
      · exact hunotin hin
      · exact hkavoid u (List.mem_cons_self ..) a ha

/-- **Every queried variable is unset in the root restriction.**  Free variables of the active term are
unset by definition; each recursion sets exactly those, so no deeper query revisits them. -/
theorem canonicalDTree_queriedVars_unset (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (v : Fin n),
      v ∈ DTree.queriedVars (canonicalDTree cs w F σ) → σ v = none := by
  intro F
  induction F with
  | zero => intro σ v h; simp [canonicalDTree, DTree.queriedVars] at h
  | succ F ih =>
    intro σ v h
    rw [canonicalDTree] at h
    split at h
    · simp [DTree.queriedVars] at h
    · split at h
      · simp [DTree.queriedVars] at h
      · next T hact =>
        rcases queryAll_queriedVars_mem _ _ _ h with hin | ⟨a, ha⟩
        · exact mem_freeVarsOf hin
        · split at ha
          · simp [DTree.queriedVars] at ha
          · have hext := ih (extendσ σ T a) v ha
            simp only [extendσ] at hext
            split at hext
            · exact absurd hext (by simp)
            · exact hext

/-- **The adaptive canonical decision tree is fresh** for distinct-variable clauses. -/
theorem canonicalDTree_fresh (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), (canonicalDTree cs w F σ).fresh := by
  intro F
  induction F with
  | zero => intro σ; rw [canonicalDTree]; trivial
  | succ F ih =>
    intro σ
    rw [canonicalDTree]
    split
    · trivial
    · next hns =>
      cases hact : activeTerm cs σ with
      | none => trivial
      | some T =>
        apply queryAll_fresh
        · intro a
          split
          · trivial
          · exact ih (extendσ σ T a)
        · exact freeVarsOf_nodup (hnd T (activeTerm_mem hact))
        · intro v hv a
          split
          · simp [DTree.queriedVars]
          · intro hmem
            have hext := canonicalDTree_queriedVars_unset cs w F (extendσ σ T a) v hmem
            simp only [extendσ] at hext
            rw [if_pos hv] at hext
            exact absurd hext (by simp)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_queriedVars_unset
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_fresh
