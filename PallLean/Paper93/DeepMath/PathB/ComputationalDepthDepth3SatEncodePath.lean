import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatEncode

/-!
# The global satisfying encoding `satEncode` (branch only)

For the `s`-step holographic count we need a single encoded restriction whose first satisfied term is the
first active term, and which — after re-falsifying processed blocks — reveals each subsequent active
term.  `satEncode cs F σ` follows the canonical deepest descent (same deeper-child choices, hence the
same queried-variable sequence `deepestSel`), but sets **each queried variable to its satisfying value**
instead of the descent value.

This file builds it and proves the first structural property:

* `satEncode` — the global satisfying encoding (mirrors `deepestEnd`, overriding each pivot to `satValue`).
* `satEncode_extends` — it **extends** `σ` (it only fills coordinates free in `σ`).

The remaining properties (it satisfies the first active term; the per-step peel invariant
`RecoverableBy`) build on this; this is the load-bearing definition + the extension property.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The value of a literal's variable that makes the literal **true**. -/
def satValue : Rung4Literal n → Bool
  | .pos _ => true
  | .neg _ => false

/-- **The global satisfying encoding.**  Follow the canonical deepest descent (to fix the queried
variable sequence), but set each pivot variable to its satisfying value. -/
def satEncode (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → (Fin n → Option Bool)
  | 0, σ => σ
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then σ
    else match SwitchingCounting.activeTerm cs σ with
      | none => σ
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => σ
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then fixVar (satEncode cs fuel (fixVar σ (litVar ℓ) false)) (litVar ℓ) (satValue ℓ)
          else fixVar (satEncode cs fuel (fixVar σ (litVar ℓ) true)) (litVar ℓ) (satValue ℓ)

/-- The active literal's variable is free at the descent state. -/
private theorem head_free_enc {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) : σ (litVar ℓ) = none := by
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  rw [litFree_var] at hfree
  cases hx : σ (litVar ℓ) with
  | none => rfl
  | some _ => rw [hx] at hfree; simp at hfree

/-- **The global satisfying encoding extends `σ`.** -/
theorem satEncode_extends (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), Extends σ (satEncode cs F σ) := by
  intro F
  induction F with
  | zero => intro σ v c h; rw [satEncode]; exact h
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => intro v c h; rw [satEncode]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        intro v c h; rw [satEncode]
        simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          intro v c h; rw [satEncode]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact h
        | some ℓ =>
          have hℓfree : σ (litVar ℓ) = none := head_free_enc hh
          intro v c hvc
          rw [satEncode]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split <;>
          · by_cases hvl : v = litVar ℓ
            · exact absurd (hvl ▸ hvc) (by rw [hℓfree]; simp)
            · rw [fixVar, Function.update_of_ne hvl]
              exact ih _ v c (by rw [fixVar, Function.update_of_ne hvl]; exact hvc)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.satEncode_extends
