import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatStep

/-!
# Polarity: falsify, not satisfy (the decoder-direction finding)

**STATUS: REAL.  ANALYSIS REALIZED — CORRECT POLARITY + FORWARD-STABILITY.**

Decoder analysis:

* **Backward replay is stuck** with the *satisfy* polarity: at step `k` the active
  clause is `firstUnsat σ_{k-1}`, but after a satisfying `satFix` that clause is
  *satisfied* in `σ_k`, so `firstUnsat σ_k` points past it — the active clause is
  not recoverable from `σ_k` without already knowing `σ_{k-1}`.  Circular.
* **Forward replay works with the *falsify* polarity.**  The long canonical-DT
  path falsifies each active clause's literals (the satisfying branch is a leaf),
  so the encoded `σ` leaves every processed clause *unsatisfied*; then
  `firstUnsat σ` = the first active clause, recomputable from `σ` alone.

So the step must fix each chosen literal to **false** (`falFix`).  This file builds
that polarity and proves the key forward-stability fact: falsifying one literal of
an unsatisfied clause keeps it unsatisfied (for clauses with distinct variables —
true for Tseitin), so `firstUnsat` does not skip the active clause forward.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The value that makes a literal **false**: `x ↦ false`, `¬x ↦ true`. -/
def falValue : Rung4Literal n → Bool
  | .pos _ => false
  | .neg _ => true

/-- Fix a literal's variable so the literal becomes false (Håstad convention). -/
def falFix (ρ : Restriction n) (ℓ : Rung4Literal n) : Restriction n :=
  Function.update ρ (litVar ℓ) (some (falValue ℓ))

/-- `falFix` changes only the literal's own variable. -/
theorem falFix_eq_outside (ρ : Restriction n) (ℓ : Rung4Literal n) {j : Fin n}
    (hj : j ≠ litVar ℓ) : falFix ρ ℓ j = ρ j :=
  Function.update_of_ne hj _ _

/-- **The step forces its literal false.** -/
theorem falFix_forces_false (ρ : Restriction n) (ℓ : Rung4Literal n) :
    Depth3.litFixedVal (falFix ρ ℓ) ℓ = some false := by
  cases ℓ with
  | pos i => simp [Depth3.litFixedVal, falFix, falValue, litVar, Function.update_self]
  | neg i => simp [Depth3.litFixedVal, falFix, falValue, litVar, Function.update_self]

/-- The falsified literal is not forced true. -/
theorem litTrue_falFix_self (ρ : Restriction n) (ℓ : Rung4Literal n) :
    Depth3.litTrue (falFix ρ ℓ) ℓ = false := by
  simp [Depth3.litTrue, falFix_forces_false]

/-- `falFix` leaves the forced value of literals on *other* variables unchanged. -/
theorem litFixedVal_falFix_ne (ρ : Restriction n) {ℓ ℓ' : Rung4Literal n}
    (h : litVar ℓ' ≠ litVar ℓ) :
    Depth3.litFixedVal (falFix ρ ℓ) ℓ' = Depth3.litFixedVal ρ ℓ' := by
  cases ℓ' with
  | pos i =>
    show (falFix ρ ℓ) i = ρ i
    exact falFix_eq_outside ρ ℓ (by simpa [litVar] using h)
  | neg i =>
    show ((falFix ρ ℓ) i).map (fun b => !b) = (ρ i).map (fun b => !b)
    rw [falFix_eq_outside ρ ℓ (by simpa [litVar] using h)]

/-- `litTrue` is unchanged on literals over other variables. -/
theorem litTrue_falFix_ne (ρ : Restriction n) {ℓ ℓ' : Rung4Literal n}
    (h : litVar ℓ' ≠ litVar ℓ) :
    Depth3.litTrue (falFix ρ ℓ) ℓ' = Depth3.litTrue ρ ℓ' := by
  unfold Depth3.litTrue
  rw [litFixedVal_falFix_ne ρ h]

/-- **Forward-stability.**  Falsifying a literal of an unsatisfied clause (with
distinct variables) keeps the clause unsatisfied — so `firstUnsat` does not skip
the active clause on the next step. -/
theorem clauseSatisfied_falFix (ρ : Restriction n) (C : Clause n) {ℓ : Rung4Literal n}
    (hℓ : ℓ ∈ C.lits)
    (hdist : ∀ ℓ₁ ∈ C.lits, ∀ ℓ₂ ∈ C.lits, litVar ℓ₁ = litVar ℓ₂ → ℓ₁ = ℓ₂)
    (hunsat : clauseSatisfied ρ C = false) :
    clauseSatisfied (falFix ρ ℓ) C = false := by
  rw [clauseSatisfied, Bool.eq_false_iff, Ne, List.any_eq_true]
  rintro ⟨ℓ', hℓ', htrue⟩
  by_cases hv : litVar ℓ' = litVar ℓ
  · have : ℓ' = ℓ := hdist ℓ' hℓ' ℓ hℓ hv
    subst this
    rw [litTrue_falFix_self] at htrue
    exact absurd htrue (by simp)
  · rw [litTrue_falFix_ne ρ hv] at htrue
    have : clauseSatisfied ρ C = true := by
      rw [clauseSatisfied, List.any_eq_true]; exact ⟨ℓ', hℓ', htrue⟩
    rw [hunsat] at this; exact absurd this (by simp)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.falFix_forces_false
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_falFix
