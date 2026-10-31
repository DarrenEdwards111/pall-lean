import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BridgeNoGo

/-!
# Block-DT model, foundation 36: branching holography, step 1 — per-input path length (branch only)

The pivot the obstruction (brick 33) demands: keep the branching `canonicalDTree` as the holographic
object, and re-found the count on *it* instead of on the single `killTerm` path.  Step 1 is the
per-input descent and its relation to the (branching) tree depth.

* `pathLen cs w F σ x` — the length of input `x`'s root-to-leaf path in the canonical tree (the per-input
  descent: query the active term's free vars, stop if `x` satisfies it, else recurse with `x`'s
  restriction).
* `pathLen_le_depth` — every input's path is at most the tree depth (`pathLen ≤ canonicalDTree.depth`).

So `{ρ : canonicalDTree.depth ≥ s}` is exactly `{ρ : ∃ x, pathLen ≥ s}` on the `≥` side — the per-input
descents are what a *branching* holographic count must encode (replacing the all-false `blockStream`
path).  The encoding + the probability bound `Pr_ρ[depth ≥ s] ≤ small` are the remaining Razborov-style
steps; this brick fixes the object they act on.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The length of input `x`'s root-to-leaf path in the canonical decision tree. -/
def pathLen (cs : List (Clause n)) (w : ℕ) : ℕ → (Fin n → Option Bool) → (Fin n → Bool) → ℕ
  | 0, _, _ => 0
  | F + 1, σ, x =>
    if anyTermSat cs σ then 0
    else match activeTerm cs σ with
      | none => 0
      | some T =>
        (freeVarsOf σ T).length +
          (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then 0
           else pathLen cs w F (extendσ σ T x) x)

/-- The leaf assignment selected by `x` agrees with `x` on the queried (free) variables. -/
theorem leaf_eq_on_free (σ : Fin n → Option Bool) (T : Clause n) (x : Fin n → Bool)
    {v : Fin n} (hv : v ∈ freeVarsOf σ T) :
    (freeVarsOf σ T).foldl (fun a v => Function.update a v (x v)) (fun _ => false) v = x v :=
  foldl_update_mem (freeVarsOf σ T) x _ _ hv

/-- `extendσ` at `x`'s leaf assignment equals `extendσ` at `x` (they agree on the free variables). -/
theorem extendσ_leaf_eq (σ : Fin n → Option Bool) (T : Clause n) (x : Fin n → Bool) :
    extendσ σ T ((freeVarsOf σ T).foldl (fun a v => Function.update a v (x v)) (fun _ => false))
      = extendσ σ T x := by
  funext i
  rw [extendσ, extendσ]
  by_cases hi : i ∈ freeVarsOf σ T
  · rw [if_pos hi, if_pos hi, leaf_eq_on_free σ T x hi]
  · rw [if_neg hi, if_neg hi]

/-- `List.all` over pointwise-equal predicates agree. -/
theorem all_eq_of_pointwise {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The satisfying condition at `x`'s leaf equals the condition at `x`. -/
theorem cond_leaf_eq (σ : Fin n → Option Bool) (T : Clause n) (x : Fin n → Bool) :
    (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ
        ((freeVarsOf σ T).foldl (fun a v => Function.update a v (x v)) (fun _ => false)))
      = (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) := by
  apply all_eq_of_pointwise
  intro ℓ hℓ
  rw [List.mem_filter] at hℓ
  have hva : (freeVarsOf σ T).foldl (fun a v => Function.update a v (x v)) (fun _ => false)
      (litVarOf ℓ) = x (litVarOf ℓ) :=
    leaf_eq_on_free σ T x (litVar_mem_freeVarsOf hℓ.1 hℓ.2)
  exact eval_eq_of_var _ x ℓ hva

/-- **Per-input path length is at most the tree depth.** -/
theorem pathLen_le_depth (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      pathLen cs w F σ x ≤ (canonicalDTree cs w F σ).depth := by
  intro F
  induction F with
  | zero => intro σ x; simp [pathLen, canonicalDTree, DTree.depth]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => rw [pathLen, canonicalDTree]; simp [hany, DTree.depth]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [pathLen, canonicalDTree]; simp [hany, hact, DTree.depth]
      | some T =>
        have hpl : pathLen cs w (F + 1) σ x
            = (freeVarsOf σ T).length
              + (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then 0
                 else pathLen cs w F (extendσ σ T x) x) := by
          rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hcd : canonicalDTree cs w (F + 1) σ
            = DTree.queryAll (freeVarsOf σ T) (fun _ => false)
                (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                          then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a)) := by
          rw [canonicalDTree]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hpl, hcd]
        have hge := queryAll_depth_ge (freeVarsOf σ T)
          (fun a => if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ a)
                    then DTree.leaf true else canonicalDTree cs w F (extendσ σ T a))
          x (fun _ => false)
        -- the continuation at x's leaf bounds the per-input block contribution
        have hcont : (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x)
              then 0 else pathLen cs w F (extendσ σ T x) x)
            ≤ (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ
                  ((freeVarsOf σ T).foldl (fun a v => Function.update a v (x v)) (fun _ => false)))
                then DTree.leaf true
                else canonicalDTree cs w F
                  (extendσ σ T ((freeVarsOf σ T).foldl
                    (fun a v => Function.update a v (x v)) (fun _ => false)))).depth := by
          rw [cond_leaf_eq, extendσ_leaf_eq]
          split
          · simp [DTree.depth]
          · exact ih (extendσ σ T x) x
        omega
end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pathLen_le_depth
