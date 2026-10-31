import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LabelNodup

/-!
# Block-DT model, foundation 46: branching holography, step 4d — set-form decoder (branch only)

`resetVars` only ever sets variables to `none`, so folding it over the labels just blanks the *set* of
freed variables — their order and block structure are irrelevant to recovering `σ`.  Hence `σ` is
determined by the pair `(descentFinal, freed-variable set)`:

* `descent_decode_set` — `(fun v => if v ∈ (descentLabels …).flatten then none else descentFinal … v) = σ`.

This is the form that lands in a genuine `Fintype` codomain (`(Fin n → Option Bool) × Finset (Fin n)`),
the prerequisite for a `Finset.card` bound on the restrictions with deep paths.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Set-form decoder.**  The final restriction together with the *set* of freed variables determines the
original restriction: blank the freed variables in the final restriction and recover `σ`. -/
theorem descent_decode_set (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (fun v => if v ∈ (descentLabels cs w F σ x).flatten then none else descentFinal cs w F σ x v) = σ := by
  intro F
  induction F with
  | zero => intro σ x; funext v; simp [descentLabels, descentFinal]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true =>
      funext v
      rw [descentLabels, descentFinal]
      simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none =>
        funext v
        rw [descentLabels, descentFinal]
        simp [hany, hact]
      | some T =>
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          have hf : descentFinal cs w (F + 1) σ x = extendσ σ T x := by
            rw [descentFinal]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          rw [hl, hf]; funext v
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
          by_cases hv : v ∈ freeVarsOf σ T
          · rw [if_pos hv]; exact (mem_freeVarsOf_none hv).symm
          · rw [if_neg hv, extendσ, if_neg hv]
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          have hf : descentFinal cs w (F + 1) σ x = descentFinal cs w F (extendσ σ T x) x := by
            rw [descentFinal]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, hf]; funext v
          rw [List.flatten_cons]
          have ihv := congrFun (ih (extendσ σ T x) x) v
          by_cases hv : v ∈ freeVarsOf σ T
          · rw [if_pos (List.mem_append.mpr (Or.inl hv))]; exact (mem_freeVarsOf_none hv).symm
          · rw [extendσ, if_neg hv] at ihv
            by_cases hv2 : v ∈ (descentLabels cs w F (extendσ σ T x) x).flatten
            · rw [if_pos (List.mem_append.mpr (Or.inr hv2))]; rw [if_pos hv2] at ihv; exact ihv
            · rw [if_neg (fun h => Or.elim (List.mem_append.mp h) hv hv2)]
              rw [if_neg hv2] at ihv; exact ihv

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_decode_set
