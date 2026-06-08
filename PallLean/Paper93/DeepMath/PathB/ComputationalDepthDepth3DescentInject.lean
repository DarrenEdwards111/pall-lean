import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentPeel

/-!
# Block-DT model, foundation 50: branching holography, step 4h — the injection (branch only)

`σ` is recovered from the boundary `(descentSat cs w F σ x, descentSatMasks cs w F σ x)` by **freeing the
masked (block) variables** — the masks carry `some` exactly on the freed variables, so "masked" is
`(m v).isSome`.  Hence `σ ↦ (descentSat …, descentSatMasks …)` is **injective**, the branching analog of
`block_injective`.

* `extendσ_outside` — `extendσ` leaves non-block coordinates equal to `σ`.
* `recoverσ` — free the masked coordinates of the boundary.
* `descentSat_recover` — `recoverσ (descentSatMasks …) (descentSat …) = σ`.
* `descentSat_injective` — `σ ↦ (descentSat …, descentSatMasks …)` is injective.

This completes the branching replay injection (`descentSat` + peel recovery + injectivity), mirroring the
single-path `blockEncode`/`block_recovery`/`block_injective` chain.  Remaining for the tight count: bound
the per-block label space (positions+signs within the peel-recovered term, `≤ 3^w`), giving `(3^w)^s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `extendσ` leaves a non-block coordinate equal to `σ`. -/
theorem extendσ_outside {σ : Fin n → Option Bool} {T : Clause n} {x : Fin n → Bool} {v : Fin n}
    (hv : v ∉ freeVarsOf σ T) : extendσ σ T x v = σ v := by
  rw [extendσ, if_neg hv]

/-- Free the masked coordinates of the boundary (a coordinate is masked iff some block fixes it). -/
def recoverσ (masks : List (Fin n → Option Bool)) (enc : Fin n → Option Bool) : Fin n → Option Bool :=
  fun v => if masks.any (fun m => (m v).isSome) then none else enc v

/-- **The recovery identity.**  Freeing the masked (block) variables of the boundary recovers `σ`. -/
theorem descentSat_recover (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      recoverσ (descentSatMasks cs w F σ x) (descentSat cs w F σ x) = σ := by
  intro F
  induction F with
  | zero => intro σ x; funext v; simp [recoverσ, descentSatMasks, descentSat]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => funext v; simp [recoverσ, descentSatMasks, descentSat, hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => funext v; simp [recoverσ, descentSatMasks, descentSat, hany, hact]
      | some T =>
        funext v
        have hmask : descentSatMasks cs w (F + 1) σ x
            = (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
              :: descentSatMasks cs w F (extendσ σ T x) x := by
          rw [descentSatMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hihv := congrFun (ih (extendσ σ T x) x) v
        have hisSome : (if v ∈ freeVarsOf σ T then some (x v) else none).isSome
            = decide (v ∈ freeVarsOf σ T) := by
          by_cases hv : v ∈ freeVarsOf σ T <;> simp [hv]
        simp only [recoverσ] at hihv ⊢
        rw [hmask]
        simp only [List.any_cons, hisSome]
        by_cases hv : v ∈ freeVarsOf σ T
        · simp only [decide_eq_true_eq.mpr hv, Bool.true_or, if_true]
          exact (mem_freeVarsOf_none hv).symm
        · simp only [decide_eq_false_iff_not.mpr hv, Bool.false_or]
          by_cases hrest : (descentSatMasks cs w F (extendσ σ T x) x).any (fun m => (m v).isSome) = true
          · rw [if_pos hrest]
            rw [if_pos hrest] at hihv
            rw [extendσ_outside hv] at hihv
            exact hihv
          · rw [if_neg hrest]
            rw [if_neg hrest] at hihv
            rw [descentSat_succ_apply x hany hact, if_neg (not_cond_of_not_mem_free hv), hihv,
              extendσ_outside hv]

/-- **The injection.**  `σ ↦ (descentSat cs w F σ x, descentSatMasks cs w F σ x)` is injective (even with
the descent input varying per `σ`: the recovery uses only the boundary and masks). -/
theorem descentSat_injective (cs : List (Clause n)) (w F : ℕ)
    {σ₁ σ₂ : Fin n → Option Bool} {x₁ x₂ : Fin n → Bool}
    (henc : descentSat cs w F σ₁ x₁ = descentSat cs w F σ₂ x₂)
    (hmask : descentSatMasks cs w F σ₁ x₁ = descentSatMasks cs w F σ₂ x₂) : σ₁ = σ₂ := by
  rw [← descentSat_recover cs w F σ₁ x₁, ← descentSat_recover cs w F σ₂ x₂, henc, hmask]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentSat_injective
