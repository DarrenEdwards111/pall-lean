import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BadLabels

/-!
# Block-DT model, foundation 45: branching holography, step 4c — labels are globally distinct (branch only)

The fact that makes the label space *finite*: the descent never frees a variable twice.  The labels
flatten to a `Nodup` list of variables, each of which `σ` leaves free — so the total label content is a
list of distinct elements of `Fin n`, of length `≤ n`.  This is the global counterpart of brick 38's
descent locality (each block fixes its freed variables via `extendσ`, so later blocks cannot free them
again).

* `descentLabels_flatten_mem_free` — every variable appearing in the labels is `σ`-free (`σ v = none`).
* `descentLabels_flatten_nodup` — the flattened labels are `Nodup` (no variable freed twice).

With brick 44 this pins the codomain of the switching injection to a finite space: label-lists whose
flatten is a `Nodup` subset of `Fin n` (size `≤ n`), partitioned into `≤ w`-sized blocks — the finite
container whose cardinality yields the `(c·w)^s` factor.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Every variable appearing in the descent labels is left free by `σ`. -/
theorem descentLabels_flatten_mem_free (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      ∀ v ∈ (descentLabels cs w F σ x).flatten, σ v = none := by
  intro F
  induction F with
  | zero => intro σ x v hv; simp [descentLabels] at hv
  | succ F ih =>
    intro σ x v hv
    cases hany : anyTermSat cs σ with
    | true => rw [descentLabels] at hv; simp only [hany] at hv; simp at hv
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [descentLabels] at hv; simp only [hany, Bool.false_eq_true, if_false, hact] at hv; simp at hv
      | some T =>
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          rw [hl] at hv
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hv
          exact mem_freeVarsOf_none hv
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, List.flatten_cons, List.mem_append] at hv
          cases hv with
          | inl h => exact mem_freeVarsOf_none h
          | inr h =>
            have hf := ih (extendσ σ T x) x v h
            rw [extendσ] at hf
            by_cases hv' : v ∈ freeVarsOf σ T
            · rw [if_pos hv'] at hf; exact absurd hf (by simp)
            · rw [if_neg hv'] at hf; exact hf

/-- **The descent labels are globally distinct.**  No variable is freed by two different blocks. -/
theorem descentLabels_flatten_nodup (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (descentLabels cs w F σ x).flatten.Nodup := by
  intro F
  induction F with
  | zero => intro σ x; simp [descentLabels]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => simp [descentLabels, hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => simp [descentLabels, hany, hact]
      | some T =>
        by_cases hcx : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · have hl : descentLabels cs w (F + 1) σ x = [freeVarsOf σ T] := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx, if_true]
          rw [hl]
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
          exact freeVarsOf_nodup (hnd T (activeTerm_mem hact))
        · rw [Bool.not_eq_true] at hcx
          have hl : descentLabels cs w (F + 1) σ x
              = freeVarsOf σ T :: descentLabels cs w F (extendσ σ T x) x := by
            rw [descentLabels]; simp only [hany, Bool.false_eq_true, if_false, hact, hcx]
          rw [hl, List.flatten_cons, List.nodup_append]
          refine ⟨freeVarsOf_nodup (hnd T (activeTerm_mem hact)), ih (extendσ σ T x) x, ?_⟩
          intro a ha b hb hab
          have hbfree := descentLabels_flatten_mem_free cs w F (extendσ σ T x) x b hb
          rw [hab] at ha
          rw [extendσ, if_pos ha] at hbfree
          exact absurd hbfree (by simp)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentLabels_flatten_nodup
