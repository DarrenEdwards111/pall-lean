import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding

/-!
# Nonlinear CSP pilot, step 2: residual richness survives gadgetisation — EXPLORATORY (not a P≠NP step)

`ComputationalDepthNonlinearCSPPilot.lean` showed the AND-gadget `x_u ⊕ x_v ⊕ (x_w ∧ x_z) = b` **destroys the
affine structure** that gives Tseitin its linear (Gaussian/parity) decision shortcut.  The next lab question:
does the **residual / distinguishability debt survive** the gadgetisation, or does the AND term collapse it?

This file answers the provable half: **richness survives.**  For an AND-gadget family of `m` constraints, each
with its own *private* variable `u_i`, the constraint-value (outcome) vector is a **surjection onto `2^m`
outcomes** — so any low-boundary observer still carries residual debt `≥ 2^m − 2^B`, exactly as for the linear
Tseitin family.  The nonlinear AND terms do not collapse the distinguishability debt.

## Proved (clean axioms, no `sorry`)

* `gadgetOutcomes_surjective` — the map `u ↦ (gadget value at each constraint)` is surjective: varying the
  private linear bit `u_i` flips constraint `i`'s value freely, hitting all `2^m` outcome vectors.
* `gadget_residual_forces_debt` — consequently (via `surjective_residual_forces_debt`) every boundary-`B`
  observer of the gadget family carries residual debt `≥ 2^m − 2^B`.  Distinguishability debt survives.

## Honest scope — where the lab now stands

Two pilot facts are now proved about the AND-gadget family:

1. **No affine/Gaussian shortcut** (`nonlinear_solution_set_not_affine`): the linear structure that decides
   Tseitin is gone.
2. **Residual debt survives** (this file): the family still has `2^{Ω(n)}` distinguishable residuals.

That is the *desired* profile for a decision-hard family — but it is **not** decision hardness.  Two honest
caveats: (a) the richness here is sourced by the **private linear variables**, so it is "debt preserved despite
the AND terms," not debt *created* by them; (b) "no affine shortcut + rich residuals" does **not** imply "no
shortcut" — a nonlinear CSP can still be decision-easy by other means.  Proving no shortcut exists for an
NP-complete family is `DecisionHolonomyHyp` = the open breakthrough.  This remains the laboratory, labelled as
such; the expander hypergraph lift and any decision-hardness claim are future work, not provided here.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

/-- The AND-gadget constraint value over `F₂`: `x_u ⊕ x_v ⊕ (x_w ∧ x_z) = x_u + x_v + x_w · x_z`. -/
def gadgetVal (xu xv xw xz : ZMod 2) : ZMod 2 := xu + xv + xw * xz

/-- For `m` gadget constraints, each with its own private variable `u_i` and fixed `(v_i, w_i, z_i)`, the
constraint-value vector as a function of the private bits `u`. -/
def gadgetOutcomes {m : ℕ} (vfix wfix zfix : Fin m → ZMod 2) (u : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun i => gadgetVal (u i) (vfix i) (wfix i) (zfix i)

/-- **The gadget outcome map is surjective (proved).**  Varying each private bit `u_i` flips constraint `i`'s
value freely, so the outcome vector ranges over all `2^m` patterns. -/
theorem gadgetOutcomes_surjective {m : ℕ} (vfix wfix zfix : Fin m → ZMod 2) :
    Function.Surjective (gadgetOutcomes vfix wfix zfix) := by
  intro t
  refine ⟨fun i => t i + (vfix i + wfix i * zfix i), ?_⟩
  funext i
  simp only [gadgetOutcomes, gadgetVal]
  generalize t i = T
  generalize vfix i = V
  generalize wfix i = W
  generalize zfix i = Z
  revert T V W Z
  decide

/-- **Residual richness survives gadgetisation (proved, exploratory).**  For an AND-gadget family of `m`
constraints with private variables, there is a residual map onto `2^m` outcomes under which **every**
boundary-`B` observer carries residual debt `≥ 2^m − 2^B`.  The nonlinear AND terms do not collapse the
distinguishability debt. -/
theorem gadget_residual_forces_debt {m B : ℕ} (vfix wfix zfix : Fin m → ZMod 2)
    (view : (Fin m → ZMod 2) → Fin (2 ^ B)) :
    ∃ residual : (Fin m → ZMod 2) → Fin (2 ^ m),
      2 ^ m - 2 ^ B ≤ debtCount (residualFooling residual) view := by
  have hcard : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun x => e (gadgetOutcomes vfix wfix zfix x), ?_⟩
  exact surjective_residual_forces_debt _
    (e.surjective.comp (gadgetOutcomes_surjective vfix wfix zfix)) view

end PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.gadgetOutcomes_surjective
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearCSPPilot.gadget_residual_forces_debt
