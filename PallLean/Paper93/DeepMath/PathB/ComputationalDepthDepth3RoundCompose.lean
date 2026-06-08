import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RestrCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ACircuit

/-!
# AC⁰ reduction, foundation 13: round composition (branch only)

The chaining backbone of the multi-round collapse.  One round replaces a circuit by an equivalent shallower
one *on a subcube* (`single_round_collapse` / `single_round_collapse_or`, bricks 73/77); to iterate, the
per-round equivalences chain through the composed restriction (brick 74).

* `round_compose` — if `C = C'` on the `ρ₁`-subcube and `C' = C''` on the `ρ₂`-subcube (with `ρ₂` touching
  only `ρ₁`-free coordinates), then `C = C''` on the `composeR ρ₁ ρ₂`-subcube.

Iterating this is exactly the `d`-fold recursion's eval-chaining: each round shrinks depth by one and
refines the restriction, and the equivalences compose down to the final shallow circuit.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

variable {n : ℕ}

/-- **Round composition.**  Two per-round subcube-equivalences chain through the composed restriction. -/
theorem round_compose {C C' C'' : ACircuit n} {ρ₁ ρ₂ : Fin n → Option Bool}
    (h1 : ∀ x, DTree.agreeRestriction ρ₁ x → C.eval x = C'.eval x)
    (h2 : ∀ x, DTree.agreeRestriction ρ₂ x → C'.eval x = C''.eval x)
    (hdis : ∀ i b, ρ₂ i = some b → ρ₁ i = none) :
    ∀ x, DTree.agreeRestriction (composeR ρ₁ ρ₂) x → C.eval x = C''.eval x := by
  intro x hx
  rw [h1 x (agreeRestriction_composeR_left ρ₁ ρ₂ x hx),
    h2 x (agreeRestriction_composeR_right ρ₁ ρ₂ x hdis hx)]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.round_compose
