import Mathlib

/-!
# Nonlinear CSP pilot, step 3: AND-only richness over shared variables — EXPLORATORY (the diagnostic test)

Step 2 showed the gadget family keeps `2^m` residual richness — but the richness was sourced by the **private
linear variables** `u_i`, with the AND terms along for the ride.  The diagnostic question: do the **AND terms
alone**, over **shared** variables (no private linear bits), generate richness, or does the multiplicative
structure restrict it?

This file runs the sharp test on a *triangle* of gadgets on three shared variables `x₀, x₁, x₂`:

```
AND triangle:  (x₀·x₁, x₁·x₂, x₀·x₂)        linear triangle:  (x₀⊕x₁, x₁⊕x₂, x₀⊕x₂)
```

**Result (proved): the AND triangle is strictly more restricted than the linear one.**  The outcome `(1,1,0)`
is **achievable by the linear gadgets but impossible for the AND gadgets** — `x₀x₁ = x₁x₂ = 1` forces
`x₀ = x₁ = x₂ = 1`, hence `x₀x₂ = 1 ≠ 0` (multiplicative transitivity).  So over shared variables the AND terms
**remove** achievable outcomes; they do not create new richness.

## Proved (clean axioms, no `sorry`)

* `linTriangle_hits_110` — the linear gadgets achieve `(1,1,0)` (witness `x = (0,1,0)`).
* `andTriangle_misses_110` — the AND gadgets can **never** achieve `(1,1,0)` (multiplicative transitivity).
* `andTriangle_not_surjective` — hence the AND-only outcome map is not surjective over shared variables.

## Honest finding — a cautionary (mildly negative) diagnostic

The result says: **AND-only richness over shared variables is *restricted*, not enhanced.**  The product
structure imposes dependencies (`x_ix_j = x_jx_k = 1 ⇒ x_ix_k = 1`) that the linear structure does not, so the
AND terms shrink the achievable-outcome set.  This means step 2's `2^m` richness was genuinely **linear-sourced**
(the private variables), and stripping the linear part *reduces* richness rather than producing a new,
nonlinear, decision-relevant kind.

Diagnostic conclusion for option B: on this evidence the AND-gadget is **not obviously a good route** to a
decision-hard family — its nonlinearity restricts residual richness rather than adding shortcut-resistant
richness, so it plausibly inherits linear-style tractability.  A genuinely decision-hard family would need a
predicate that *both* resists the linear/affine shortcut *and* keeps full residual richness over shared
variables; the simple AND gadget achieves the first (step 1) but loses the second (here).  This is an honest
negative signal from the laboratory, not a `P ≠ NP` step.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

/-- Three AND gadgets on three shared variables: `(x₀·x₁, x₁·x₂, x₀·x₂)`. -/
def andTriangle (x : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![x 0 * x 1, x 1 * x 2, x 0 * x 2]

/-- Three linear (XOR) gadgets on three shared variables: `(x₀⊕x₁, x₁⊕x₂, x₀⊕x₂)`. -/
def linTriangle (x : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![x 0 + x 1, x 1 + x 2, x 0 + x 2]

/-- **Linear gadgets hit `(1,1,0)` (proved).**  Witness `x = (0,1,0)`: `(0⊕1, 1⊕0, 0⊕0) = (1,1,0)`. -/
theorem linTriangle_hits_110 : ∃ x : Fin 3 → ZMod 2, linTriangle x = ![1, 1, 0] :=
  ⟨![0, 1, 0], by decide⟩

/-- **AND gadgets can never hit `(1,1,0)` (proved).**  `x₀x₁ = x₁x₂ = 1` forces `x₀ = x₁ = x₂ = 1`, so
`x₀x₂ = 1 ≠ 0`: multiplicative transitivity forbids the outcome the linear gadgets achieve. -/
theorem andTriangle_misses_110 : ∀ x : Fin 3 → ZMod 2, andTriangle x ≠ ![1, 1, 0] := by decide

/-- **The AND-only outcome map is not surjective over shared variables (proved).** -/
theorem andTriangle_not_surjective : ¬ Function.Surjective andTriangle := by
  intro h
  obtain ⟨x, hx⟩ := h ![1, 1, 0]
  exact andTriangle_misses_110 x hx

end PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.linTriangle_hits_110
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.andTriangle_misses_110
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.andTriangle_not_surjective
