import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatRecovery

/-!
# The satisfying encoding: making the active term recoverable (branch only)

The recovery principle (`firstSat_eq_active`) says: if the encoded state extends `ρ` and *satisfies*
the active term `T`, then `T` is recovered as the first satisfied term — for **any** `ρ`.  This file
builds an encoded state with exactly those two properties.

`satExtendTerm σ T` sets each free coordinate of `T` to its **satisfying** value (`x_i ↦ true` if
`x_i ∈ T`, `x_i ↦ false` if `¬x_i ∈ T`), keeping `σ`'s fixed coordinates.  Then:

* `satExtendTerm_extends` — it extends `σ` (only fills free coordinates).
* `satExtendTerm_sat` — for a **consistent** term `T` (no variable occurs with both signs) that `σ` does
  not falsify, `satExtendTerm σ T` satisfies `T`.
* `firstSat_satExtend` — combining with `firstSat_eq_active`: the active term of `ρ` is recovered as the
  first satisfied term of `satExtendTerm ρ T`, with **no clause identity recorded**.  This is the
  holographic boundary: the encoded restriction (a boundary object with fewer stars) determines the
  active term, recovered by `find? termSat` — no bulk clause-history is transmitted.

Consistency is the standard hypothesis on DNF terms (`x ∧ ¬x` is unsatisfiable); real terms satisfy it.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A term is **consistent** if no variable occurs in it with both signs. -/
def Consistent (T : Clause n) : Prop :=
  ∀ v : Fin n, ¬ ((Rung4Literal.pos v) ∈ T.lits ∧ (Rung4Literal.neg v) ∈ T.lits)

/-- **The satisfying encoding of a term.**  Keep `σ`'s fixed coordinates; fill each free coordinate of
`T` with the value that makes its literal true. -/
def satExtendTerm (σ : Restriction n) (T : Clause n) : Restriction n :=
  fun v =>
    if σ v = none then
      (if (Rung4Literal.pos v) ∈ T.lits then some true
       else if (Rung4Literal.neg v) ∈ T.lits then some false else none)
    else σ v

/-- The satisfying encoding extends `σ` (it only fills free coordinates). -/
theorem satExtendTerm_extends (σ : Restriction n) (T : Clause n) :
    Extends σ (satExtendTerm σ T) := by
  intro v b h
  simp only [satExtendTerm, h, reduceCtorEq, if_false]

/-- Value at a positive-literal variable: the encoding sets it `true`. -/
theorem satExtend_eq_true {σ : Restriction n} {T : Clause n} {v : Fin n}
    (hpos : (Rung4Literal.pos v) ∈ T.lits) (hnf : SwitchingCounting.termFalsified σ T = false) :
    satExtendTerm σ T v = some true := by
  simp only [satExtendTerm]
  by_cases hv : σ v = none
  · simp [hv, if_pos hpos]
  · rw [if_neg hv]
    cases hb : σ v with
    | none => exact absurd hb hv
    | some b =>
      cases b with
      | true => rfl
      | false =>
        exfalso
        have hbad : SwitchingCounting.termFalsified σ T = true := by
          rw [SwitchingCounting.termFalsified, List.any_eq_true]
          exact ⟨Rung4Literal.pos v, hpos, by
            simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hb]⟩
        rw [hnf] at hbad; exact absurd hbad (by simp)

/-- Value at a negative-literal variable (consistent term): the encoding sets it `false`. -/
theorem satExtend_eq_false {σ : Restriction n} {T : Clause n} {v : Fin n}
    (hneg : (Rung4Literal.neg v) ∈ T.lits) (hcons : Consistent T)
    (hnf : SwitchingCounting.termFalsified σ T = false) :
    satExtendTerm σ T v = some false := by
  simp only [satExtendTerm]
  by_cases hv : σ v = none
  · have hpos : (Rung4Literal.pos v) ∉ T.lits := fun hp => hcons v ⟨hp, hneg⟩
    simp [hv, if_neg hpos, if_pos hneg]
  · rw [if_neg hv]
    cases hb : σ v with
    | none => exact absurd hb hv
    | some b =>
      cases b with
      | false => rfl
      | true =>
        exfalso
        have hbad : SwitchingCounting.termFalsified σ T = true := by
          rw [SwitchingCounting.termFalsified, List.any_eq_true]
          exact ⟨Rung4Literal.neg v, hneg, by
            simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hb]⟩
        rw [hnf] at hbad; exact absurd hbad (by simp)

/-- **The satisfying encoding satisfies a consistent, non-falsified term.** -/
theorem satExtendTerm_sat {σ : Restriction n} {T : Clause n}
    (hcons : Consistent T) (hnf : SwitchingCounting.termFalsified σ T = false) :
    SwitchingCounting.termSat (satExtendTerm σ T) T = true := by
  rw [SwitchingCounting.termSat, List.all_eq_true]
  intro ℓ hℓ
  cases ℓ with
  | pos v => simp [Depth3.litTrue, Depth3.litFixedVal, satExtend_eq_true hℓ hnf]
  | neg v => simp [Depth3.litTrue, Depth3.litFixedVal, satExtend_eq_false hℓ hcons hnf]

/-- **The active term is recovered as the first satisfied term of its satisfying encoding.**  For any
`ρ` (falsifying or not), with `T` consistent: `cs.find? (termSat (satExtendTerm ρ T)) = T`. -/
theorem firstSat_satExtend {cs : List (Clause n)} {ρ : Restriction n} {T : Clause n}
    (hcons : Consistent T)
    (hact : SwitchingCounting.activeTerm cs ρ = some T) :
    cs.find? (SwitchingCounting.termSat (satExtendTerm ρ T)) = some T := by
  have hns := SwitchingCounting.activeTerm_anyTermSat_false hact
  have hfind : cs.find?
      (fun U => !SwitchingCounting.termFalsified ρ U
        && decide (0 < (SwitchingCounting.freeLits ρ U).length)) = some T := by
    rw [← SwitchingCounting.activeTerm_eq_find hns]; exact hact
  have hp := List.find?_some hfind
  have hnf : SwitchingCounting.termFalsified ρ T = false := by
    cases hx : SwitchingCounting.termFalsified ρ T with
    | false => rfl
    | true => rw [hx] at hp; simp at hp
  exact firstSat_eq_active (satExtendTerm_extends ρ T) hact (satExtendTerm_sat hcons hnf)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.satExtendTerm_sat
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.firstSat_satExtend
