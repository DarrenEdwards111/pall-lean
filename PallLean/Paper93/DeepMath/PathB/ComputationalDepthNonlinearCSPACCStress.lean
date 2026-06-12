import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonlinearCSPRichness

/-!
# Nonlinear CSP pilot, step 4: AC⁰[p] / low-degree calibration — EXPLORATORY (shortcut detector)

Steps 1–3 showed the AND gadget `x_u ⊕ x_v ⊕ (x_w ∧ x_z) = b` (a) destroys the *affine* (degree-1, Gaussian)
shortcut, but (b) has restricted richness over shared variables.  Before treating it as a decision-hard
candidate, calibrate against **AC⁰[p] / low-degree** representations — where algebraic shortcuts live.

The AND `x_w ∧ x_z = x_w · x_z` is a **degree-2** monomial over `F₂`.  So the gadget *linearizes*: introduce a
fresh variable `q := x_w · x_z`, and in `(x_u, x_v, q)` the gadget is **linear**.  This file proves that
linearisation and the resulting affineness — the AC⁰[p] shortcut detector firing.

## Proved (clean axioms, no `sorry`)

* `gadget_eq_lifted` — `gadgetVal x_u x_v x_w x_z = liftedGadgetVal x_u x_v (x_w · x_z)`: the AND gadget *is*
  its linearisation composed with the quadratic lift `(x_w, x_z) ↦ x_w · x_z`.
* `liftedGadget_solution_affine` — the lifted gadget's solution set **is affine** (closed under `a+b+c`): in
  the lifted variables the Gaussian / AC⁰[p] shortcut applies again — in direct contrast to the original
  gadget's non-affine solution set (step 1).

## What the calibration says (honest, nuanced)

* The gadget is **degree-2** — AC⁰[p] / low-degree *representable*.  It does not escape the algebraic régime; it
  is "one degree up" from linear.  Lifting one fresh variable per AND term (poly overhead: `n + m` lifted
  variables for `m` gadgets) makes the constraint system **linear** — except for the side-relations
  `q_i = x_{w_i} · x_{z_i}`, which carry *all* the remaining nonlinearity.
* **This locates any hardness precisely:** the linear core is Gaussian-trivial; the gadget's entire potential
  for decision-hardness lives in the consistency of the quadratic side-relations.
* **Crucial nuance, both ways.**  Low-degree *representation* (cheap function) is **not** decision-easiness:
  degree-1 (linear) systems are decision-easy by Gaussian elimination, but degree-2 `F₂` systems (the `MQ`
  problem) are **NP-hard in general** (classical, cited — not formalized).  So the calibration is *not* a death
  certificate: the gadget escaped degree-1's decision-easiness and sits exactly at the degree-2 threshold where
  low representation and decision-hardness can coexist.
* But it is *not* an endorsement either: whether the *specific expander* AND-gadget family realises that
  NP-hardness — rather than collapsing via its restricted shared-variable richness (step 3) — is unresolved.

**Diagnostic conclusion:** the AC⁰[p] lens shows the gadget is low-degree (degree 2), so it is firmly in the
algebraic régime; its decision status reduces to the quadratic side-relations and is genuinely open (degree-2
`F₂`-SAT is NP-hard in general, but this family's instance is not pinned down).  This is honest calibration —
the gadget is neither cleanly killed nor validated; it is *located* at the degree-1→2 boundary.  No `P ≠ NP`
claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

/-- The **linearised** gadget: with a fresh variable `q` standing for the quadratic monomial `x_w · x_z`, the
gadget `x_u ⊕ x_v ⊕ (x_w ∧ x_z)` becomes the linear `x_u ⊕ x_v ⊕ q`. -/
def liftedGadgetVal (xu xv q : ZMod 2) : ZMod 2 := xu + xv + q

/-- **The AND gadget is its own linearisation under the quadratic lift (proved).**  `gadgetVal` equals
`liftedGadgetVal` with `q := x_w · x_z` — the degree-2 monomial lifted to a fresh variable. -/
theorem gadget_eq_lifted (xu xv xw xz : ZMod 2) :
    gadgetVal xu xv xw xz = liftedGadgetVal xu xv (xw * xz) := rfl

/-- **The lifted gadget's solution set is affine (proved).**  In the lifted variables `(x_u, x_v, q)` the
gadget is linear, so its solutions are closed under the affine combination `a + b + c` — the Gaussian / AC⁰[p]
shortcut applies, in contrast to the original gadget's non-affine solution set (`nonlinear_solution_set_not_affine`). -/
theorem liftedGadget_solution_affine (a b c : Fin 3 → ZMod 2)
    (ha : liftedGadgetVal (a 0) (a 1) (a 2) = 0)
    (hb : liftedGadgetVal (b 0) (b 1) (b 2) = 0)
    (hc : liftedGadgetVal (c 0) (c 1) (c 2) = 0) :
    liftedGadgetVal ((a + b + c) 0) ((a + b + c) 1) ((a + b + c) 2) = 0 := by
  simp only [liftedGadgetVal, Pi.add_apply] at ha hb hc ⊢
  linear_combination ha + hb + hc

end PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.gadget_eq_lifted
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.liftedGadget_solution_affine
