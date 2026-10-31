import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockDecode

/-!
# Block-DT model, foundation 41: branching holography, step 3b — the sequential decoder (branch only)

The switching-lemma encoding records a deep path as its *final* restriction together with the list of
per-block freed-variable sets (the labels).  This brick chains brick 40's one-block inversion across the
whole path: folding `resetVars` over the reversed label list recovers the *original* restriction `σ` from
the final one.

* `descentFinal` — the restriction reached at the end of input `x`'s descent (all path blocks fixed).
* `descentLabels` — the list of per-block freed-variable sets along that descent.
* `descent_decode` — `(descentLabels …).reverse.foldl resetVars (descentFinal …) = σ`: the labels +
  final restriction determine the original restriction.  This is the decode side of the injection
  `{ρ : depth ≥ s} ↪ {final restriction} × {label list}`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The restriction reached at the end of input `x`'s descent (every block on the path fixed). -/
def descentFinal (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → (Fin n → Option Bool)
  | 0, σ, _ => σ
  | F + 1, σ, x =>
    if anyTermSat cs σ then σ
    else match activeTerm cs σ with
      | none => σ
      | some T =>
        if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then extendσ σ T x
        else descentFinal cs w F (extendσ σ T x) x

/-- The list of per-block freed-variable sets (labels) along input `x`'s descent. -/
def descentLabels (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (List (Fin n))
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T =>
        if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then [freeVarsOf σ T]
        else freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x

/-- **The sequential decoder.**  The label list and the final restriction recover the original
restriction: folding `resetVars` over the reversed labels inverts the whole descent. -/
theorem descent_decode (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (descentLabels cs w F σ x).reverse.foldl resetVars (descentFinal cs w F σ x) = σ := by
  intro F
  induction F with
  | zero => intro σ x; simp [descentLabels, descentFinal]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => simp [descentLabels, descentFinal, hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [descentLabels, descentFinal, hany, hact]
      | some T =>
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          have hf : descentFinal cs w (F + 1) σ x = extendσ σ T x := by
            rw [descentFinal]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          rw [hl, hf, List.reverse_singleton, List.foldl_cons, List.foldl_nil, resetVars_extendσ]
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          have hf : descentFinal cs w (F + 1) σ x = descentFinal cs w F (extendσ σ T x) x := by
            rw [descentFinal]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, hf, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
            ih (extendσ σ T x) x, resetVars_extendσ]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_decode
