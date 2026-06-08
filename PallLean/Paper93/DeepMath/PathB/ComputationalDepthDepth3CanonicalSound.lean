import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# Block-DT model, foundation 27: canonical tree soundness (increment 3, step 2a) (branch only)

Eval-correctness of the adaptive canonical tree, **soundness direction**: if `canonicalDTree` accepts a
`σ`-consistent input, the DNF is true on it.  (No false positives — proved without any fuel-sufficiency
hypothesis, since `leaf true` is reached only at `anyTermSat` or a genuine satisfying leaf.)

* `canonicalDTree_sound` — `agreeRestriction σ x → eval (canonicalDTree cs w F σ) x = true → dnfValue cs x = true`.

## Honest scope

This is the soundness half of eval-correctness.  The completeness half (`dnfValue → eval`, needs the
descent to terminate within fuel — `F ≥ stars σ`) and the tighter `≤ blockStream.length · w` depth bound
are the remaining steps of increment 3.  Built incrementally and honestly; no `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `DTree.freeLit` agrees with the block-arc `litFree`. -/
theorem freeLit_eq_litFree (σ : Fin n → Option Bool) (ℓ : Rung4Literal n) :
    DTree.freeLit σ ℓ = Depth3.litFree σ ℓ := by
  cases ℓ with
  | pos i => cases hv : σ i <;> simp [DTree.freeLit, Depth3.litFree, Depth3.litFixedVal, hv]
  | neg i => cases hv : σ i <;> simp [DTree.freeLit, Depth3.litFree, Depth3.litFixedVal, hv]

/-- A `σ`-forced-true literal is true on `σ`-consistent inputs. -/
theorem litTrue_eval {σ : Fin n → Option Bool} {x : Fin n → Bool} {ℓ : Rung4Literal n}
    (hx : DTree.agreeRestriction σ x) (h : Depth3.litTrue σ ℓ = true) :
    Rung4Literal.eval ℓ x = true := by
  cases ℓ with
  | pos i =>
    cases hv : σ i with
    | none => simp [Depth3.litTrue, Depth3.litFixedVal, hv] at h
    | some b =>
      cases b with
      | false => simp [Depth3.litTrue, Depth3.litFixedVal, hv] at h
      | true => simp only [Rung4Literal.eval]; exact hx i true hv
  | neg i =>
    cases hv : σ i with
    | none => simp [Depth3.litTrue, Depth3.litFixedVal, hv] at h
    | some b =>
      cases b with
      | true => simp [Depth3.litTrue, Depth3.litFixedVal, hv] at h
      | false => simp [Rung4Literal.eval, hx i false hv]

/-- The literal value depends only on its variable. -/
theorem eval_eq_of_var (a x : Fin n → Bool) (ℓ : Rung4Literal n)
    (h : a (litVarOf ℓ) = x (litVarOf ℓ)) : Rung4Literal.eval ℓ a = Rung4Literal.eval ℓ x := by
  cases ℓ <;> simp only [Rung4Literal.eval, litVarOf] at h ⊢ <;> rw [h]

/-- Off the queried variables the leaf assignment keeps `init`. -/
theorem foldl_update_not_mem (vars : List (Fin n)) (x : Fin n → Bool) :
    ∀ (init : Fin n → Bool) (i : Fin n), i ∉ vars →
      (vars.foldl (fun acc v => Function.update acc v (x v)) init) i = init i := by
  induction vars with
  | nil => intro init i _; rfl
  | cons v vars ih =>
    intro init i hi
    rw [List.mem_cons, not_or] at hi
    rw [List.foldl_cons, ih (Function.update init v (x v)) i hi.2,
      Function.update_of_ne hi.1]

/-- The leaf assignment built by `queryAll` agrees with `x` on the queried variables. -/
theorem foldl_update_mem (vars : List (Fin n)) (x : Fin n → Bool) :
    ∀ (init : Fin n → Bool) (i : Fin n), i ∈ vars →
      (vars.foldl (fun acc v => Function.update acc v (x v)) init) i = x i := by
  induction vars with
  | nil => intro init i hi; simp at hi
  | cons v vars ih =>
    intro init i hi
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · by_cases hiv : i ∈ vars
      · exact ih (Function.update init i (x i)) i hiv
      · rw [foldl_update_not_mem vars x (Function.update init i (x i)) i hiv,
          Function.update_self]
    · exact ih (Function.update init v (x v)) i hi'

/-- A free literal's variable is one of the queried variables. -/
theorem litVar_mem_freeVarsOf {σ : Fin n → Option Bool} {T : Clause n} {ℓ : Rung4Literal n}
    (hℓ : ℓ ∈ T.lits) (hfree : DTree.freeLit σ ℓ = true) :
    litVarOf ℓ ∈ freeVarsOf σ T := by
  rw [freeVarsOf, List.mem_filterMap]
  refine ⟨ℓ, hℓ, ?_⟩
  have hnone : σ (litVarOf ℓ) = none := by
    cases ℓ with
    | pos i => simpa [DTree.freeLit, litVarOf] using hfree
    | neg i => simpa [DTree.freeLit, litVarOf] using hfree
  rw [if_pos hnone]

/-- **`anyTermSat` soundness.**  If some term is `σ`-satisfied, the DNF is true on consistent inputs. -/
theorem anyTermSat_sound {cs : List (Clause n)} {σ : Fin n → Option Bool} {x : Fin n → Bool}
    (hany : anyTermSat cs σ = true) (hx : DTree.agreeRestriction σ x) :
    DTree.dnfValue cs x = true := by
  rw [anyTermSat, List.any_eq_true] at hany
  obtain ⟨T, hT, hsat⟩ := hany
  rw [DTree.dnfValue, List.any_eq_true]
  refine ⟨T, hT, ?_⟩
  rw [termSat, List.all_eq_true] at hsat
  rw [List.all_eq_true]
  intro ℓ hℓ
  exact litTrue_eval hx (hsat ℓ hℓ)

/-- Consistency is preserved by extending `σ` with values agreeing with `x` on the free variables. -/
theorem agreeRestriction_extendσ {σ : Fin n → Option Bool} {T : Clause n} {x a : Fin n → Bool}
    (hx : DTree.agreeRestriction σ x) (ha : ∀ i ∈ freeVarsOf σ T, a i = x i) :
    DTree.agreeRestriction (extendσ σ T a) x := by
  intro i b hb
  rw [extendσ] at hb
  by_cases hi : i ∈ freeVarsOf σ T
  · rw [if_pos hi] at hb
    injection hb with hb'
    rw [← hb']; exact (ha i hi).symm
  · rw [if_neg hi] at hb
    exact hx i b hb

/-- **Active-term satisfying soundness.**  If the active term's free literals are all true under `x`,
the DNF is true (the term's fixed literals are forced true on consistent inputs). -/
theorem activeTerm_sat_sound {cs : List (Clause n)} {σ : Fin n → Option Bool} {x : Fin n → Bool}
    {T : Clause n} (hact : activeTerm cs σ = some T) (hx : DTree.agreeRestriction σ x)
    (hcond : ∀ ℓ ∈ T.lits, DTree.freeLit σ ℓ = true → Rung4Literal.eval ℓ x = true) :
    DTree.dnfValue cs x = true := by
  have hTmem : T ∈ cs := activeTerm_mem hact
  have hnotfals : termFalsified σ T = false := by
    have hns := activeTerm_anyTermSat_false hact
    have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))
        = some T := activeTerm_eq_find hns ▸ hact
    have hp := List.find?_some hfind
    rw [Bool.and_eq_true] at hp
    have := hp.1
    rwa [Bool.not_eq_true'] at this
  rw [DTree.dnfValue, List.any_eq_true]
  refine ⟨T, hTmem, ?_⟩
  rw [List.all_eq_true]
  intro ℓ hℓ
  by_cases hf : DTree.freeLit σ ℓ = true
  · exact hcond ℓ hℓ hf
  · rw [Bool.not_eq_true] at hf
    rw [freeLit_eq_litFree] at hf
    have hlitfalse : litFalse σ ℓ = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have : termFalsified σ T = true := by
        rw [termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓ, hc⟩
      rw [this] at hnotfals; simp at hnotfals
    exact litTrue_eval hx (litTrue_of_not_free_not_false hf hlitfalse)

/-- **Canonical tree soundness.**  If `canonicalDTree` accepts a `σ`-consistent input, the DNF is true. -/
theorem canonicalDTree_sound (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      DTree.agreeRestriction σ x →
      (canonicalDTree cs w F σ).eval x = true → DTree.dnfValue cs x = true := by
  intro F
  induction F with
  | zero => intro σ x _ h; simp [canonicalDTree, DTree.eval] at h
  | succ F ih =>
    intro σ x hx h
    rw [canonicalDTree] at h
    split at h
    · next hany => exact anyTermSat_sound hany hx
    · next hany =>
      cases hact : activeTerm cs σ with
      | none => rw [hact] at h; simp [DTree.eval] at h
      | some T =>
        rw [hact, DTree.queryAll_eval] at h
        set a := (freeVarsOf σ T).foldl (fun acc v => Function.update acc v (x v)) (fun _ => false)
          with ha
        have ha_mem : ∀ i ∈ freeVarsOf σ T, a i = x i := by
          intro i hi; rw [ha]; exact foldl_update_mem (freeVarsOf σ T) x _ i hi
        split at h
        · next hcond =>
          refine activeTerm_sat_sound hact hx ?_
          intro ℓ hℓ hfree
          have hℓfilter : ℓ ∈ T.lits.filter (DTree.freeLit σ) := List.mem_filter.mpr ⟨hℓ, hfree⟩
          have hva : a (litVarOf ℓ) = x (litVarOf ℓ) :=
            ha_mem _ (litVar_mem_freeVarsOf hℓ hfree)
          rw [← eval_eq_of_var a x ℓ hva]
          exact List.all_eq_true.mp hcond ℓ hℓfilter
        · next hcond =>
          exact ih (extendσ σ T a) x (agreeRestriction_extendσ hx ha_mem) h

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_sound
