import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TreePathLen

/-!
# Block-DT model, foundation 38: branching holography, step 2 — descent locality (branch only)

The well-formedness of the canonical tree, in usable form: the per-input descent `pathLen` depends only
on the input's values at the **free** variables of `σ`.  (Equivalently: the canonical tree never queries
a variable `σ` has already fixed — each block fixes its free vars via `extendσ`, so they leave the
free set and are not re-queried.)

* `pathLen_eq_of_agree_on_free` — if `x` and `y` agree on all `σ`-free coordinates, then
  `pathLen cs w F σ x = pathLen cs w F σ y`.

This is the locality the branching count needs: the descent (hence the deep path / encoding) lives
entirely on the free variables.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Descent locality.**  `pathLen` depends only on the input's values at `σ`'s free coordinates. -/
theorem pathLen_eq_of_agree_on_free (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x y : Fin n → Bool),
      (∀ i, σ i = none → x i = y i) → pathLen cs w F σ x = pathLen cs w F σ y := by
  intro F
  induction F with
  | zero => intro σ x y _; rfl
  | succ F ih =>
    intro σ x y hag
    cases hany : anyTermSat cs σ with
    | true => rw [pathLen, pathLen]; simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [pathLen, pathLen]; simp [hany, hact]
      | some T =>
        have hpl : ∀ z : Fin n → Bool, pathLen cs w (F + 1) σ z
            = (freeVarsOf σ T).length
              + (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ z) then 0
                 else pathLen cs w F (extendσ σ T z) z) := by
          intro z; rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact]
        -- the satisfying condition agrees (free literals live on free variables)
        have hcond : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x)
            = (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ y) := by
          apply all_eq_of_pointwise
          intro ℓ hℓ
          rw [List.mem_filter] at hℓ
          exact eval_eq_of_var x y ℓ
            (hag (litVarOf ℓ) (mem_freeVarsOf_none (litVar_mem_freeVarsOf hℓ.1 hℓ.2)))
        -- the extended restriction agrees (free vars get equal values)
        have hext : extendσ σ T x = extendσ σ T y := by
          funext i
          rw [extendσ, extendσ]
          by_cases hi : i ∈ freeVarsOf σ T
          · rw [if_pos hi, if_pos hi, hag i (mem_freeVarsOf_none hi)]
          · rw [if_neg hi, if_neg hi]
        rw [hpl x, hpl y, hcond, hext]
        congr 1
        split
        · rfl
        · apply ih
          intro i hi
          rw [extendσ] at hi
          by_cases hiv : i ∈ freeVarsOf σ T
          · rw [if_pos hiv] at hi; simp at hi
          · rw [if_neg hiv] at hi; exact hag i hi

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pathLen_eq_of_agree_on_free
