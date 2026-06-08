import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentDecode

/-!
# Block-DT model, foundation 42: branching holography, step 3c — label-space quantitative bridges (branch only)

The decode side (brick 41) makes `ρ ↦ (descentFinal, descentLabels)` injective.  To turn injectivity into
a cardinality bound we must bound the label space.  This brick proves the two quantitative facts the count
consumes:

* `descentLabels_flatten_length` — the labels carry exactly `pathLen` variables in total
  (`(descentLabels …).flatten.length = pathLen …`).  So on the bad event `pathLen ≥ s` the labels hold
  `≥ s` variable-slots.
* `descentLabels_label_le_w` — every individual label has length `≤ w` (each block frees at most the
  active term's `≤ w` variables).  So the labels partition the `pathLen` slots into blocks of width `≤ w`.

Together: the label list is a partition of a length-`pathLen` variable sequence into `≤ w`-sized blocks —
the object whose count gives the `(cw)^s` factor.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Total label content equals the path length.**  The freed-variable sets along the descent carry
exactly `pathLen` variables in total. -/
theorem descentLabels_flatten_length (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (descentLabels cs w F σ x).flatten.length = pathLen cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; simp [descentLabels, pathLen]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => simp [descentLabels, pathLen, hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [descentLabels, pathLen, hany, hact]
      | some T =>
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          have hp : pathLen cs w (F + 1) σ x = (freeVarsOf σ T).length := by
            rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true, Nat.add_zero]
          rw [hl, hp]; simp [List.flatten_cons]
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          have hp : pathLen cs w (F + 1) σ x
              = (freeVarsOf σ T).length + pathLen cs w F (extendσ σ T x) x := by
            rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, hp, List.flatten_cons, List.length_append, ih (extendσ σ T x) x]

/-- **Each label is a `≤ w`-sized block.**  For width-`≤ w` clauses, every freed-variable set along the
descent has at most `w` variables. -/
theorem descentLabels_label_le_w (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ L ∈ descentLabels cs w F σ x, L.length ≤ w := by
  intro F
  induction F with
  | zero => intro σ x L hL; simp [descentLabels] at hL
  | succ F ih =>
    intro σ x L hL
    cases hany : anyTermSat cs σ with
    | true => rw [descentLabels] at hL; simp only [hany] at hL; simp at hL
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [descentLabels] at hL; simp only [hany, Bool.false_eq_true, if_false, hact] at hL; simp at hL
      | some T =>
        have hTle : (freeVarsOf σ T).length ≤ w :=
          le_trans (freeVarsOf_length_le σ T) (hw T (activeTerm_mem hact))
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          rw [hl, List.mem_singleton] at hL
          rw [hL]; exact hTle
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, List.mem_cons] at hL
          cases hL with
          | inl h => rw [h]; exact hTle
          | inr h => exact ih (extendσ σ T x) x L h

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentLabels_flatten_length
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentLabels_label_le_w
