import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalSound

/-!
# Block-DT model, foundation 28: canonical tree completeness (increment 3, step 2b) (branch only)

Eval-correctness of the adaptive canonical tree, **completeness direction**: if the DNF is true on a
`σ`-consistent input and the fuel suffices (`stars σ < F`), the tree accepts.  Together with soundness
this is full eval-correctness on the subcube (for sufficient fuel).

The fuel hypothesis `stars σ < F` is what makes the induction clean: `F = 0` is vacuous, and each block
strictly decreases `stars` (the active term has a free variable, fixed in every branch via `extendσ`).

* `canonicalDTree_complete` — `stars σ < F → agreeRestriction σ x → dnfValue cs x = true → eval = true`.
* `canonicalDTree_eval` — full eval-correctness: `eval = dnfValue` on the subcube, for `stars σ < F`.

## Honest scope

This completes eval-correctness (both directions, for sufficient fuel).  Remaining for increment 3: the
tighter `≤ blockStream.length · w` depth bound, then the parity-bridge connection.  No `sorry`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A `σ`-forced-false literal is false on `σ`-consistent inputs. -/
theorem litFalse_eval {σ : Fin n → Option Bool} {x : Fin n → Bool} {ℓ : Rung4Literal n}
    (hx : DTree.agreeRestriction σ x) (h : litFalse σ ℓ = true) :
    Rung4Literal.eval ℓ x = false := by
  cases ℓ with
  | pos i =>
    cases hv : σ i with
    | none => simp [litFalse, Depth3.litFixedVal, hv] at h
    | some b => cases b with
      | true => simp [litFalse, Depth3.litFixedVal, hv] at h
      | false => simp [Rung4Literal.eval, hx i false hv]
  | neg i =>
    cases hv : σ i with
    | none => simp [litFalse, Depth3.litFixedVal, hv] at h
    | some b => cases b with
      | false => simp [litFalse, Depth3.litFixedVal, hv] at h
      | true => simp [Rung4Literal.eval, hx i true hv]

/-- A falsified term is false on consistent inputs. -/
theorem termFalsified_eval {σ : Fin n → Option Bool} {x : Fin n → Bool} {T : Clause n}
    (hx : DTree.agreeRestriction σ x) (h : termFalsified σ T = true) :
    T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) = false := by
  rw [termFalsified, List.any_eq_true] at h
  obtain ⟨ℓ, hℓ, hf⟩ := h
  cases hres : T.lits.all (fun ℓ => Rung4Literal.eval ℓ x) with
  | false => rfl
  | true =>
    rw [List.all_eq_true] at hres
    have := hres ℓ hℓ
    rw [litFalse_eval hx hf] at this
    simp at this

/-- A free variable's `σ`-value is `none`. -/
theorem mem_freeVarsOf_none {σ : Fin n → Option Bool} {T : Clause n} {v : Fin n}
    (h : v ∈ freeVarsOf σ T) : σ v = none := by
  rw [freeVarsOf, List.mem_filterMap] at h
  obtain ⟨ℓ, _, he⟩ := h
  split at he
  · next hcond => injection he with he'; rw [← he']; exact hcond
  · next => simp at he

/-- The active term has a free variable (with `σ`-value `none`). -/
theorem activeTerm_exists_free {cs : List (Clause n)} {σ : Fin n → Option Bool} {T : Clause n}
    (hact : activeTerm cs σ = some T) :
    ∃ v ∈ freeVarsOf σ T, σ v = none := by
  have hns := activeTerm_anyTermSat_false hact
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length))
      = some T := activeTerm_eq_find hns ▸ hact
  have hp := List.find?_some hfind
  rw [Bool.and_eq_true] at hp
  have h0 : 0 < (freeLits σ T).length := of_decide_eq_true hp.2
  obtain ⟨ℓ, hℓ⟩ := List.exists_mem_of_length_pos h0
  rw [freeLits, List.mem_filter] at hℓ
  have hℓDfree : DTree.freeLit σ ℓ = true := by rw [freeLit_eq_litFree]; exact hℓ.2
  exact ⟨litVarOf ℓ, litVar_mem_freeVarsOf hℓ.1 hℓDfree,
    mem_freeVarsOf_none (litVar_mem_freeVarsOf hℓ.1 hℓDfree)⟩

/-- **Each block strictly decreases `stars`.** -/
theorem stars_extendσ_lt {cs : List (Clause n)} {σ : Fin n → Option Bool} {T : Clause n}
    (a : Fin n → Bool) (hact : activeTerm cs σ = some T) :
    stars (extendσ σ T a) < stars σ := by
  obtain ⟨v, hvfree, hvnone⟩ := activeTerm_exists_free hact
  have hsub : freeVars (extendσ σ T a) ⊆ freeVars σ := by
    intro i hi
    rw [mem_freeVars] at hi ⊢
    rw [extendσ] at hi
    by_cases hiv : i ∈ freeVarsOf σ T
    · rw [if_pos hiv] at hi; simp at hi
    · rwa [if_neg hiv] at hi
  have hvσ : v ∈ freeVars σ := mem_freeVars.mpr hvnone
  have hvnot : v ∉ freeVars (extendσ σ T a) := by
    rw [mem_freeVars, extendσ, if_pos hvfree]; simp
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨v, hvσ, hvnot⟩)

/-- **When no active term remains, the DNF is false on consistent inputs.** -/
theorem activeTerm_none_dnf_false {cs : List (Clause n)} {σ : Fin n → Option Bool} {x : Fin n → Bool}
    (hx : DTree.agreeRestriction σ x) (hany : anyTermSat cs σ = false)
    (hact : activeTerm cs σ = none) : DTree.dnfValue cs x = false := by
  have hfind : cs.find? (fun T => !termFalsified σ T && decide (0 < (freeLits σ T).length)) = none := by
    rw [← activeTerm_eq_find hany]; exact hact
  rw [List.find?_eq_none] at hfind
  have hsatfalse : ∀ T ∈ cs, termSat σ T = false := by
    intro T hT
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hcontra : anyTermSat cs σ = true := by
      rw [anyTermSat, List.any_eq_true]; exact ⟨T, hT, hc⟩
    rw [hcontra] at hany; simp at hany
  cases hres : DTree.dnfValue cs x with
  | false => rfl
  | true =>
    rw [DTree.dnfValue, List.any_eq_true] at hres
    obtain ⟨T, hT, hTsat⟩ := hres
    have hTfals : termFalsified σ T = true := by
      have hp := hfind T hT
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_and, not_lt,
        Nat.le_zero] at hp
      by_cases hf : termFalsified σ T = true
      · exact hf
      · rw [Bool.not_eq_true] at hf
        have hempty : freeLits σ T = [] := List.length_eq_zero_iff.mp (hp hf)
        exact term_falsified_of_not_sat_no_free (hsatfalse T hT) hempty
    rw [termFalsified_eval hx hTfals] at hTsat
    simp at hTsat

/-- **Canonical tree completeness.**  If the DNF is true on a `σ`-consistent input and the fuel
suffices (`stars σ < F`), the adaptive tree accepts. -/
theorem canonicalDTree_complete (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      stars σ < F → DTree.agreeRestriction σ x → DTree.dnfValue cs x = true →
      (canonicalDTree cs w F σ).eval x = true := by
  intro F
  induction F with
  | zero => intro σ x hsf _ _; exact absurd hsf (Nat.not_lt_zero _)
  | succ F ih =>
    intro σ x hsf hx hdnf
    rw [canonicalDTree]
    split
    · simp [DTree.eval]
    · next hany =>
      rw [Bool.not_eq_true] at hany
      cases hact : activeTerm cs σ with
      | none =>
        rw [activeTerm_none_dnf_false hx hany hact] at hdnf
        simp at hdnf
      | some T =>
        rw [DTree.queryAll_eval]
        set a := (freeVarsOf σ T).foldl (fun acc v => Function.update acc v (x v)) (fun _ => false)
          with ha
        have ha_mem : ∀ i ∈ freeVarsOf σ T, a i = x i := by
          intro i hi; rw [ha]; exact foldl_update_mem (freeVarsOf σ T) x _ i hi
        split
        · simp [DTree.eval]
        · refine ih (extendσ σ T a) x ?_ (agreeRestriction_extendσ hx ha_mem) hdnf
          have hlt := stars_extendσ_lt a hact
          omega

/-- **Full eval-correctness on the subcube.**  For sufficient fuel (`stars σ < F`), the adaptive tree
computes the DNF on `σ`-consistent inputs. -/
theorem canonicalDTree_eval (cs : List (Clause n)) (w F : ℕ) (σ : Fin n → Option Bool)
    (x : Fin n → Bool) (hsf : stars σ < F) (hx : DTree.agreeRestriction σ x) :
    (canonicalDTree cs w F σ).eval x = DTree.dnfValue cs x := by
  cases hd : DTree.dnfValue cs x with
  | true => exact canonicalDTree_complete cs w F σ x hsf hx hd
  | false =>
    cases he : (canonicalDTree cs w F σ).eval x with
    | false => rfl
    | true =>
      rw [canonicalDTree_sound cs w F σ x hx he] at hd
      simp at hd

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_complete
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDTree_eval
