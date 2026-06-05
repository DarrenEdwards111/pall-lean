import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestActiveId
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFreeConfirm

/-!
# Satisfy-step recovery: the active literal's value is read off the end-state

The deepest-branch decoder's wall (`deepestPathLabel`'s `hdec`) is the **satisfy-step active-clause
identification**: a *falsify*-step's variable carries a false literal, so it is visible in the
end-state; a *satisfy*-step's variable need not be — or so the difficulty was stated.  This file
attacks exactly that gap and resolves its *value-recovery* half: a satisfy-step's literal **is**
recoverable from the deepest end-state.

The mechanism is monotonicity (`deepestEnd_eq_of_fixed`): the deepest branch only ever fixes *free*
variables, so once a step fixes the active literal's variable, that value persists unchanged to the
leaf.  Hence:

* `deepestStep_active_fixes` — a genuine step fixes `litVar ℓ` to some bit.
* `deepestEnd_active_var_eq` — **the active literal's variable holds the same value at the full
  end-state as right after its step**.
* `litTrue_deepestEnd_active_eq` / `litFalse_deepestEnd_active_eq` — so its forced truth/falsity is
  preserved step → leaf.
* `litTrue_deepestEnd_of_satisfy_step` — **a satisfy step's literal is true at the deepest leaf**
  (the satisfy-step counterpart of falsify-step monotonicity): its value *is* visible in the
  end-state, dissolving the "satisfy-step variables are invisible" half of the wall.

## What remains (honest)

This recovers each step's literal *value* from the end-state.  The genuinely irreducible remainder is
*which clause* that literal belongs to at *which step* — the canonical-ordering active-clause
identification across falsify boundaries (the same Håstad forward-reconstruction core isolated as
`hdec`), which shared variables make non-local.  The *value* half is now proved on both polarities;
the *ordering* half is **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A genuine deepest step fixes the active literal's variable.**  At a non-stuck state (no term
satisfied, active clause `T`, head free literal `ℓ`), `deepestStep` sets `litVar ℓ` to some bit. -/
theorem deepestStep_active_fixes (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (ℓ : Rung4Literal n) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) :
    ∃ b, deepestStep cs F σ (litVar ℓ) = some b := by
  rw [deepestStep_active cs F σ T hany hact hh]
  split
  · exact ⟨false, by simp [fixVar, Function.update_self]⟩
  · exact ⟨true, by simp [fixVar, Function.update_self]⟩

/-- **The active literal's variable is preserved to the leaf.**  Its value at the full deepest
end-state equals its value right after the step that fixed it — by `deepestEnd_eq_of_fixed` (the
branch only fixes free variables, so a fixed value persists). -/
theorem deepestEnd_active_var_eq (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (ℓ : Rung4Literal n) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) :
    deepestEnd cs (F + 1) σ (litVar ℓ) = deepestStep cs F σ (litVar ℓ) := by
  obtain ⟨b, hb⟩ := deepestStep_active_fixes cs F σ T ℓ hany hact hh
  rw [deepestEnd_succ, deepestEnd_eq_of_fixed cs F _ (litVar ℓ) b hb, hb]

/-- **Forced truth of the active literal is preserved step → leaf.** -/
theorem litTrue_deepestEnd_active_eq (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (ℓ : Rung4Literal n) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) :
    Depth3.litTrue (deepestEnd cs (F + 1) σ) ℓ = Depth3.litTrue (deepestStep cs F σ) ℓ :=
  SwitchingCounting.litTrue_eq_of_agree (deepestEnd_active_var_eq cs F σ T ℓ hany hact hh)

/-- **Forced falsity of the active literal is preserved step → leaf.** -/
theorem litFalse_deepestEnd_active_eq (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (ℓ : Rung4Literal n) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) :
    SwitchingCounting.litFalse (deepestEnd cs (F + 1) σ) ℓ
      = SwitchingCounting.litFalse (deepestStep cs F σ) ℓ :=
  SwitchingCounting.litFalse_eq_of_litVar_val (deepestEnd_active_var_eq cs F σ T ℓ hany hact hh)

/-- **A satisfy step's literal is true at the deepest leaf.**  If the deepest step makes its active
literal `ℓ` true (a *satisfy* step), then `ℓ` is still forced true at the full end-state — so the
satisfy-step's value is visible in the leaf, the satisfy-step counterpart of falsify-step
monotonicity. -/
theorem litTrue_deepestEnd_of_satisfy_step (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (ℓ : Rung4Literal n) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ)
    (hsat : Depth3.litTrue (deepestStep cs F σ) ℓ = true) :
    Depth3.litTrue (deepestEnd cs (F + 1) σ) ℓ = true := by
  rw [litTrue_deepestEnd_active_eq cs F σ T ℓ hany hact hh, hsat]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_active_var_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.litTrue_deepestEnd_of_satisfy_step
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.litFalse_deepestEnd_active_eq
