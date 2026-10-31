import Mathlib

/-!
# Nonlinear CSP pilot, step 5: ACC⁰ / mixed-moduli stress — EXPLORATORY (the modular shortcut detector)

The AC⁰[p] calibration (step 4) showed the AND gadget is degree-2 and *linearizes*.  Now the ACC⁰ test: does
the gadget carry genuine **modular** (MOD_q / CRT) content that resists mixed-moduli views, or is it
modular-trivial?  ACC⁰'s power over AC⁰[p] is exactly its MOD_q gates, which are **modulus-specific** (MOD₃
differs from MOD₂ — that asymmetry is what `mod_q_indicators_false` / Razborov–Smolensky exploit).

This file proves the gadget's AND term is the opposite: **modulus-agnostic.**  For bit inputs, `AND(a,b) = a·b`
holds as the *same* product over **every** modulus.  So a CRT / mixed-moduli view gains nothing on the gadget —
it carries no MOD_q content to resist with.

## Proved (clean axioms, no `sorry`)

* `andBit_eq_prod_any_modulus` — for all `m` and bits `a, b`: `((a ∧ b : Bool) : ZMod m) = (a : ZMod m)·(b :
  ZMod m)`.  The AND gadget is the integer bit-product over *every* modulus — modulus-agnostic.
* `andBit_mod2_eq_mod3` — concrete corollary: the gadget's AND value over `ZMod 2` and over `ZMod 3` carry the
  same truth table (no modulus distinguishes it), unlike a genuine MOD_q gate.

## Diagnostic conclusion — the AND gadget fails the calibration battery (abandon it)

Cumulative lab verdict on the simple AND gadget:

| test | result |
|---|---|
| affine / Gaussian (step 1) | **escapes** (non-affine) — the one good sign |
| shared-variable richness (step 3) | **fails** (restricted by AND transitivity) |
| AC⁰[p] / low-degree (step 4) | **fails** (degree-2, linearizes with poly lift) |
| ACC⁰ / mixed-moduli (this step) | **fails** (AND is modulus-agnostic — no MOD_q content) |

The gadget resists *only* the degree-1 shortcut; it is low-degree, linearizable, and modulus-trivial.  So it
has **no algebraic-shortcut-resistance** beyond escaping pure linearity — exactly the profile of a family that
is *not* decision-hard.  **Honest conclusion: abandon the simple AND gadget as a P-vs-NP candidate.**  The
calibration battery did its job — it filtered out a bad candidate cheaply, before any P-vs-NP claim.  A real
decision-hard-holonomy family would need a predicate resisting *all* of: affine, low-degree-lift, *and*
modular shortcuts; this one resists only the first.  No `P ≠ NP` step — a successful negative filter.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

/-- **The AND gadget is modulus-agnostic (proved).**  For bit inputs, `AND(a,b)` equals the integer bit-product
`a·b` as the *same* value over **every** modulus `m`.  Unlike a MOD_q gate (modulus-specific), the AND carries
no modular content — a CRT / mixed-moduli view gains nothing. -/
theorem andBit_eq_prod_any_modulus (m : ℕ) (a b : Bool) :
    (((a && b).toNat : ℕ) : ZMod m) = ((a.toNat : ℕ) : ZMod m) * ((b.toNat : ℕ) : ZMod m) := by
  cases a <;> cases b <;> simp

/-- **Concrete: the gadget's AND is the same over `ZMod 2` and `ZMod 3` (proved).**  Both equal the bit-product;
no modulus distinguishes the AND gadget — in contrast to a genuine `MOD_q` gate. -/
theorem andBit_mod2_eq_mod3 (a b : Bool) :
    (((a && b).toNat : ℕ) : ZMod 2) = ((a.toNat : ℕ) : ZMod 2) * ((b.toNat : ℕ) : ZMod 2)
    ∧ (((a && b).toNat : ℕ) : ZMod 3) = ((a.toNat : ℕ) : ZMod 3) * ((b.toNat : ℕ) : ZMod 3) :=
  ⟨andBit_eq_prod_any_modulus 2 a b, andBit_eq_prod_any_modulus 3 a b⟩

end PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.andBit_eq_prod_any_modulus
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.andBit_mod2_eq_mod3
