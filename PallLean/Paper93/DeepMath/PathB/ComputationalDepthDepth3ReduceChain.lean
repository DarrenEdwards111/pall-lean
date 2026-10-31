import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TowerParity

/-!
# AC⁰ reduction, foundation 31: chaining nested rounds (branch only)

The connective that turns a sequence of switching rounds into the single `Reduces` that
`tower_not_parity` (brick 21) consumes.  Each round produces its own restriction `ρ_i`, but the multi-round
loop runs them *nested* — each `ρ_{i+1}` **extends** the previous, so the finest restriction `σ = ρ_m`
extends every `ρ_i`.  Agreement with `σ` therefore implies agreement with every `ρ_i`, so each round's
subcube-equivalence is valid on `σ`'s subcube: every round can be re-expressed at the *common* `σ`, and the
chain composes by `Reduces` with no further nesting bookkeeping.

* `agreeRestriction_of_extends` — agreeing with the finer `σ` implies agreeing with the coarser `ρ`.
* `EquivOn_of_extends` — a round's `EquivOn ρ` lifts to `EquivOn σ` whenever `σ` extends `ρ`.
* `Reduces.round` — prepend one extended round to a reduction on `σ`'s subcube.

With these, a `d`-round nested reduction is a fold of `Reduces.round` ending in `tower_not_parity` — the
logical spine of the `d`-fold loop is closed; only the per-instance parameter bookkeeping (the budget
inequalities chaining over the rounds) remains.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- Agreeing with the finer restriction `σ` implies agreeing with any `ρ` that `σ` extends. -/
theorem agreeRestriction_of_extends {ρ σ : Fin n → Option Bool} {x : Fin n → Bool}
    (hext : Extends ρ σ) (hag : DTree.agreeRestriction σ x) : DTree.agreeRestriction ρ x :=
  fun i b hρ => hag i b (hext i b hρ)

/-- A round's subcube-equivalence lifts from `ρ` to any finer `σ` extending it. -/
theorem EquivOn_of_extends {ρ σ : Fin n → Option Bool} {C C' : Layered n}
    (hext : Extends ρ σ) (h : EquivOn ρ C C') : EquivOn σ C C' :=
  fun x hag => h x (agreeRestriction_of_extends hext hag)

/-- Prepend one round (an `EquivOn ρ` step, with `σ` extending `ρ`) to a reduction on `σ`'s subcube. -/
theorem Reduces.round {x : Fin n → Bool} {σ ρ : Fin n → Option Bool} {C C' Cm : Layered n}
    (hext : Extends ρ σ) (hag : DTree.agreeRestriction σ x)
    (heq : EquivOn ρ C C') (h : Reduces x C' Cm) : Reduces x C Cm :=
  Reduces.cons (EquivOn_of_extends hext heq) hag h

/-- **Two nested rounds compose.**  With `σ` extending both `ρ₁` and `ρ₂`, two subcube-equivalences chain
into a reduction on `σ`'s subcube. -/
theorem Reduces.two_rounds {x : Fin n → Bool} {σ ρ₁ ρ₂ : Fin n → Option Bool}
    {C₀ C₁ C₂ : Layered n}
    (hext1 : Extends ρ₁ σ) (hext2 : Extends ρ₂ σ) (hag : DTree.agreeRestriction σ x)
    (heq1 : EquivOn ρ₁ C₀ C₁) (heq2 : EquivOn ρ₂ C₁ C₂) : Reduces x C₀ C₂ :=
  Reduces.round hext1 hag heq1 (Reduces.round hext2 hag heq2 (Reduces.refl C₂))

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.EquivOn_of_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.Reduces.two_rounds
