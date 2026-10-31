import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PBiased

/-!
# AC⁰ reduction, foundation 9: restriction composition (branch only)

The bookkeeping the multi-round collapse threads: each round fixes more variables, so the per-round
restrictions *compose*.  `composeR ρ₁ ρ₂` keeps `ρ₁`'s fixings and applies `ρ₂` on `ρ₁`'s free
coordinates.  An input agreeing with the composition agrees with `ρ₁` (always) and with `ρ₂` (when `ρ₂`
only touches `ρ₁`-free coordinates, as in the iteration), and the composition has at most `ρ₁`'s stars.

* `composeR` — compose two restrictions (`ρ₁` overrides).
* `composeR_extends` — the composition extends `ρ₁`.
* `agreeRestriction_composeR_left` / `_right` — agreement transfers to each factor.
* `stars_composeR_le` — the composition fixes at least as much as `ρ₁`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Compose two restrictions: keep `ρ₁`'s fixings, apply `ρ₂` on `ρ₁`'s free coordinates. -/
def composeR (ρ₁ ρ₂ : Fin n → Option Bool) : Fin n → Option Bool :=
  fun v => match ρ₁ v with
    | some b => some b
    | none => ρ₂ v

/-- The composition extends `ρ₁`. -/
theorem composeR_extends (ρ₁ ρ₂ : Fin n → Option Bool) : Extends ρ₁ (composeR ρ₁ ρ₂) := by
  intro v b h
  rw [composeR, h]

/-- An input agreeing with the composition agrees with `ρ₁`. -/
theorem agreeRestriction_composeR_left (ρ₁ ρ₂ : Fin n → Option Bool) (x : Fin n → Bool)
    (h : DTree.agreeRestriction (composeR ρ₁ ρ₂) x) : DTree.agreeRestriction ρ₁ x := by
  intro i b hi
  exact h i b (by rw [composeR, hi])

/-- If `ρ₂` only touches `ρ₁`-free coordinates, an input agreeing with the composition agrees with `ρ₂`. -/
theorem agreeRestriction_composeR_right (ρ₁ ρ₂ : Fin n → Option Bool) (x : Fin n → Bool)
    (hdis : ∀ i b, ρ₂ i = some b → ρ₁ i = none)
    (h : DTree.agreeRestriction (composeR ρ₁ ρ₂) x) : DTree.agreeRestriction ρ₂ x := by
  intro i b hi
  refine h i b ?_
  rw [composeR, hdis i b hi]; exact hi

/-- The composition fixes at least as much as `ρ₁` (no more stars). -/
theorem stars_composeR_le (ρ₁ ρ₂ : Fin n → Option Bool) : stars (composeR ρ₁ ρ₂) ≤ stars ρ₁ :=
  stars_le_of_extends (composeR_extends ρ₁ ρ₂)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.composeR_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_composeR_le
