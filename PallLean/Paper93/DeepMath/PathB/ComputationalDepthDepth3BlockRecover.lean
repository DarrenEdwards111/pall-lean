import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockEncode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatRecovery

/-!
# Block-DT model, foundation 4: the encoding satisfies each block's term (branch only)

The load-bearing recovery enabler: the satisfying global encoding `blockEncode cs (F+1) σ` **satisfies**
the active term of `σ` — so, by the proven `firstSat_eq_active`, that term is recovered as the first
satisfied term of the boundary.  This is the head link of the peel chain `RecoverableBy`.

* `blockEncode_succ_apply` — the value of `blockEncode` at the active step (the per-coordinate override).
* `blockEncode_sat_term` — `blockEncode cs (F+1) σ` satisfies the (consistent) active term of `σ`.
* `blockEncode_firstSat` — hence `cs.find? (termSat (blockEncode cs (F+1) σ)) = some T`: the active term
  is recovered from the boundary, *for any `σ`* (no clause identity, no falsified-set knowledge).

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The value of `blockEncode` at the active step. -/
theorem blockEncode_succ_apply {cs : List (Clause n)} {F : ℕ} {σ : Restriction n} {T : Clause n}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) (v : Fin n) :
    blockEncode cs (F + 1) σ v =
      if σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) then
        (if (Rung4Literal.pos v) ∈ T.lits then some true else some false)
      else blockEncode cs F (killTerm σ T) v := by
  rw [blockEncode]; simp only [hany, Bool.false_eq_true, if_false, hact]

/-- **The encoding satisfies the active term.** -/
theorem blockEncode_sat_term {cs : List (Clause n)} {F : ℕ} {σ : Restriction n} {T : Clause n}
    (hcons : Consistent T) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) :
    SwitchingCounting.termSat (blockEncode cs (F + 1) σ) T = true := by
  have hnf : SwitchingCounting.termFalsified σ T = false := by
    have hfind : cs.find?
        (fun U => !SwitchingCounting.termFalsified σ U
          && decide (0 < (SwitchingCounting.freeLits σ U).length)) = some T := by
      rw [← SwitchingCounting.activeTerm_eq_find hany]; exact hact
    have hp := List.find?_some hfind
    cases hx : SwitchingCounting.termFalsified σ T with
    | false => rfl
    | true => rw [hx] at hp; simp at hp
  have hnf' : ∀ ℓ ∈ T.lits, SwitchingCounting.litFalse σ ℓ = false := by
    intro ℓ hℓ
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have : SwitchingCounting.termFalsified σ T = true := by
      rw [SwitchingCounting.termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓ, hc⟩
    rw [hnf] at this; exact absurd this (by simp)
  rw [SwitchingCounting.termSat, List.all_eq_true]
  intro ℓ hℓ
  have hextσ : Extends σ (blockEncode cs F (killTerm σ T)) :=
    Extends_trans (killTerm_extends σ T) (blockEncode_extends cs F (killTerm σ T))
  cases ℓ with
  | pos v =>
    have hfalse := hnf' (Rung4Literal.pos v) hℓ
    have hbv : blockEncode cs (F + 1) σ v = some true := by
      rw [blockEncode_succ_apply hany hact]
      by_cases hvn : σ v = none
      · rw [if_pos ⟨hvn, Or.inl hℓ⟩, if_pos hℓ]
      · rw [if_neg (fun h => hvn h.1)]
        have hsv : σ v = some true := by
          cases hb : σ v with
          | none => exact absurd hb hvn
          | some b =>
            cases b with
            | true => rfl
            | false => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hb] at hfalse
        exact hextσ v true hsv
    simp [Depth3.litTrue, Depth3.litFixedVal, hbv]
  | neg v =>
    have hfalse := hnf' (Rung4Literal.neg v) hℓ
    have hpos : (Rung4Literal.pos v) ∉ T.lits := fun hp => hcons v ⟨hp, hℓ⟩
    have hbv : blockEncode cs (F + 1) σ v = some false := by
      rw [blockEncode_succ_apply hany hact]
      by_cases hvn : σ v = none
      · rw [if_pos ⟨hvn, Or.inr hℓ⟩, if_neg hpos]
      · rw [if_neg (fun h => hvn h.1)]
        have hsv : σ v = some false := by
          cases hb : σ v with
          | none => exact absurd hb hvn
          | some b =>
            cases b with
            | false => rfl
            | true => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hb] at hfalse
        exact hextσ v false hsv
    simp [Depth3.litTrue, Depth3.litFixedVal, hbv]

/-- **The active term is recovered as the first satisfied term of the boundary `blockEncode`.** -/
theorem blockEncode_firstSat {cs : List (Clause n)} {F : ℕ} {σ : Restriction n} {T : Clause n}
    (hcons : Consistent T) (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) :
    cs.find? (SwitchingCounting.termSat (blockEncode cs (F + 1) σ)) = some T :=
  firstSat_eq_active (blockEncode_extends cs (F + 1) σ) hact (blockEncode_sat_term hcons hany hact)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEncode_sat_term
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockEncode_firstSat
