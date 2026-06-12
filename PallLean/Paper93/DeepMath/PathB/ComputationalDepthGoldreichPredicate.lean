import Mathlib

/-!
# A high‑algebraic‑immunity predicate — the decision‑hard‑family direction, fixed and verified

The naive 4‑variable AND gadget `x_u ⊕ x_v ⊕ (x_w ∧ x_z)` failed the gadget battery because it has **algebraic
immunity 1**: the degree‑1 annihilator `(1 ⊕ x_w)` kills the AND term, which is exactly the linearization the
AC⁰[p] filter exploited.  The genuine candidate for a *decision‑hard* family — Goldreich's local PRG — applies a
predicate of **high algebraic immunity** to expander‑hypergraph neighborhoods.

This file pins down the smallest real instance: the standard Goldreich **TSA** ("tri‑sum‑and") predicate on
five variables, `P(x) = x₀ ⊕ x₁ ⊕ x₂ ⊕ (x₃ ∧ x₄)`, and **verifies `AI(P) ≥ 2`** — no nonzero affine function
annihilates `P` or `¬P`.  The linear prefix `x₀ ⊕ x₁ ⊕ x₂` is what defeats the degree‑1 annihilator that broke
the bare AND.

## Proved (clean axioms, no `sorry`)

* `tsa_algebraic_immunity_ge_two` — for every nonzero affine `a`, the affine function `aff a` fails to
  annihilate both `P` and `¬P`: `∃ x, aff a x ∧ P x` and `∃ x, aff a x ∧ ¬P x`.  Hence `AI(P) ≥ 2`: `P` resists
  the linear/degree‑1 annihilator attack that the AND gadget succumbed to.  (By `decide`.)

## Honest status — the right direction, conjectural hardness

This is a genuine improvement over the gadget lab: the TSA predicate clears the degree‑1 (affine) algebraic
attack the AND gadget failed, and it is the standard primitive of Goldreich/Applebaum local one‑way functions
and pseudorandom generators — the canonical *nonlinear expander‑CSP* family.  A SAT/CSP instance built from `P`
over an expander hypergraph is the right shape for a decision‑hard compressing family.

But two honest caveats keep it short of a proof:

1. **`AI ≥ 2` is only the smallest case.**  Real local‑PRG hardness needs algebraic immunity (and rational‑
   degree, resiliency) growing with the arity; `AI = 2` resists degree‑1 attacks but not the full algebraic /
   Gröbner machinery.  This file proves the *direction*, not asymptotic immunity.
2. **Decision‑hardness is conjectural.**  The security of Goldreich's PRG (that inverting / deciding the family
   is hard) is a *cryptographic assumption*, not a theorem.  A *provably* decision‑hard explicit family is
   `P ≠ NP`.  So this predicate supplies the right object for the Williams cash‑out's `separatorSpeedup`
   ingredient *conditionally* (if local PRGs are secure), not unconditionally.

So: the decision‑hard‑family direction is now concrete and verified at its base case — the right predicate, with
the degree‑1 collapse provably removed — and the residual is the same wall: turning conjectural local‑PRG
hardness into a proof is `P ≠ NP`.  Not a separation; the honest next object, made precise.
-/

namespace PallLean.Paper93.DeepMath.PathB.GoldreichPredicate

/-- The Goldreich **TSA** predicate on five bits: `x₀ ⊕ x₁ ⊕ x₂ ⊕ (x₃ ∧ x₄)`. -/
def P (x : Fin 5 → Bool) : Bool :=
  xor (xor (xor (x 0) (x 1)) (x 2)) (x 3 && x 4)

/-- A general affine (degree‑`≤ 1`) function with coefficient vector `a : Fin 6 → Bool` (constant `a 0` plus the
five linear coefficients). -/
def aff (a : Fin 6 → Bool) (x : Fin 5 → Bool) : Bool :=
  xor (xor (xor (xor (xor (a 0) (a 1 && x 0)) (a 2 && x 1)) (a 3 && x 2)) (a 4 && x 3)) (a 5 && x 4)

/-- **`AI(P) ≥ 2` (proved).**  Every nonzero affine function fails to annihilate both `P` and `¬P`: it agrees
with `P = 1` somewhere and with `P = 0` somewhere (weighted by the affine function being `1`).  So `P` has no
degree‑1 annihilator — it resists the linear attack that collapsed the bare AND gadget. -/
theorem tsa_algebraic_immunity_ge_two :
    ∀ a : Fin 6 → Bool, a ≠ (fun _ => false) →
      (∃ x, (aff a x && P x) = true) ∧ (∃ x, (aff a x && ! (P x)) = true) := by
  decide

end PallLean.Paper93.DeepMath.PathB.GoldreichPredicate

#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichPredicate.tsa_algebraic_immunity_ge_two
