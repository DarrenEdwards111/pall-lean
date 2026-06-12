import Mathlib

/-!
# Nonlinear expander-CSP pilot — EXPLORATORY SCAFFOLDING (not a P≠NP step)

**Status: a laboratory, explicitly labelled.** The arc proved expander Tseitin is *proof-hard* but
*decision-easy* (`tseitin_unsat_of_odd_charge`): its satisfiability falls to the parity functional
`∑ charge`, because Tseitin's constraints are `F₂`-**linear** (XOR), so each constraint's solution set is an
**affine** subspace and Gaussian elimination / the parity shortcut applies.

Option B (decision-hard family) asks: keep the expander residual/holonomy debt but **destroy the linear
shortcut**.  HAL's pilot constraint is the AND-gadgetised parity

```
x_u ⊕ x_v ⊕ (x_w ∧ x_z) = b          (over F₂, AND = product)
```

This file does the honest *local* pilot: it proves the gadget's solution set is **not affine** — so the
Gaussian/parity structure that decides Tseitin does **not** apply to it — in direct contrast to the pure-XOR
constraint, whose solution set **is** affine.

## Proved (clean axioms, no `sorry`)

* `xor_solution_set_affine` — the pure-XOR constraint's solutions are closed under the affine combination
  `a + b + c` (an affine subspace): the linear shortcut applies.
* `nonlinear_solution_set_not_affine` — the AND-gadget constraint's solutions are **not** closed under
  `a + b + c`: explicit `a, b, c` solutions whose sum violates the constraint.  No affine/Gaussian structure.

## Honest scope — what this is and is NOT

* It **is** a clean witness that the AND-gadget removes the affine structure underlying Tseitin's decision
  shortcut — the right *local* property for a decision-hard family.
* It is **not** a proof of decision hardness, residual richness for the nonlinear family, the expander
  hypergraph lift, or anything approaching `P ≠ NP`.  "No *affine* shortcut" is far weaker than "no shortcut":
  a nonlinear CSP could still be decision-easy by some other means.  Proving *no shortcut exists* for an
  NP-complete family is exactly `DecisionHolonomyHyp` — the open breakthrough.
* This is the **laboratory**, per the recommendation: a place to test whether residual richness survives while
  the linear shortcut dies.  The next pilot steps (residual-explosion of the gadget, expander lift) are future
  exploratory work, not claimed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

/-- The pure-XOR (Tseitin-style) constraint on four variables: `x₀ ⊕ x₁ ⊕ x₂ ⊕ x₃ = b`. -/
def xorPred (x : Fin 4 → ZMod 2) (b : ZMod 2) : Prop := x 0 + x 1 + x 2 + x 3 = b

/-- The AND-gadgetised constraint: `x₀ ⊕ x₁ ⊕ (x₂ ∧ x₃) = b` (over `F₂`, `∧ = ·`). -/
def nonlinPred (x : Fin 4 → ZMod 2) (b : ZMod 2) : Prop := x 0 + x 1 + x 2 * x 3 = b

/-- **The XOR constraint's solution set is affine (proved).**  Closed under `a + b + c`: a linear (Tseitin)
constraint's solutions form an affine subspace, exactly the structure Gaussian elimination / the parity
shortcut exploit. -/
theorem xor_solution_set_affine (a b c : Fin 4 → ZMod 2)
    (ha : xorPred a 0) (hb : xorPred b 0) (hc : xorPred c 0) :
    xorPred (a + b + c) 0 := by
  simp only [xorPred, Pi.add_apply] at ha hb hc ⊢
  linear_combination ha + hb + hc

/-- **The AND-gadget's solution set is NOT affine (proved).**  Explicit solutions `a, b, c` whose affine
combination `a + b + c` violates the constraint.  So the gadget has no affine/Gaussian structure — the linear
shortcut that decides Tseitin does not apply. -/
theorem nonlinear_solution_set_not_affine :
    ∃ a b c : Fin 4 → ZMod 2,
      nonlinPred a 0 ∧ nonlinPred b 0 ∧ nonlinPred c 0 ∧ ¬ nonlinPred (a + b + c) 0 :=
  ⟨![0, 0, 0, 1], ![0, 1, 1, 1], ![1, 1, 1, 0],
    by unfold nonlinPred; decide, by unfold nonlinPred; decide, by unfold nonlinPred; decide,
    by unfold nonlinPred; decide⟩

end PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.xor_solution_set_affine
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.nonlinear_solution_set_not_affine
