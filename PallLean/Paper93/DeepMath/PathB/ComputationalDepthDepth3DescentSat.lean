import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BadCard

/-!
# Block-DT model, foundation 48: branching holography, step 4f — satisfying boundary + term recovery (branch only)

The replay device, ported from the single-path arc to the branching descent.  The falsifying boundary
`descentFinal` (brick 41) cannot replay (the decoder cannot identify the term).  The fix, exactly as in
`blockEncode`: a **satisfying** boundary `descentSat` that sets each active term's free variables to their
*satisfying* values — so the active term is the first term *satisfied* by the boundary, recoverable
without storing it (this is what breaks the (cw)^s-vs-set-size circularity flagged in brick 47).

* `descentSat` — the satisfying boundary of the descent (recurses on `extendσ`, the branching descent).
* `descentSat_extends` — it extends `σ`.
* `descentSat_sat_term` — it satisfies the active term of `σ`.
* `descentSat_firstSat` — hence `cs.find? (termSat (descentSat …)) = some T`: the active term is recovered
  from the boundary as the first satisfied term (via the reusable `firstSat_eq_active`).

This is the term-recovery enabler for the branching descent.  The remaining work (the position labels +
peel chain recovering the whole descent + the tight injection replacing brick 47's loose count) builds on
top of this, mirroring the single-path `blockPeel`/`block_recovery`/`block_injective` chain.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `extendσ` extends `σ` (it only fixes free coordinates). -/
theorem extendσ_extends (σ : Fin n → Option Bool) (T : Clause n) (x : Fin n → Bool) :
    Extends σ (extendσ σ T x) := by
  intro v b h
  rw [extendσ, if_neg]
  · exact h
  · intro hv; rw [mem_freeVarsOf_none hv] at h; exact absurd h (by simp)

/-- **The satisfying boundary of the branching descent.**  Like `blockEncode`, but the recursion follows
the descent (`extendσ σ T x`) rather than the single `killTerm` path. -/
def descentSat (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → (Fin n → Option Bool)
  | 0, σ, _ => σ
  | F + 1, σ, x =>
    if anyTermSat cs σ then σ
    else match activeTerm cs σ with
      | none => σ
      | some T =>
        fun v =>
          if σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) then
            (if (Rung4Literal.pos v) ∈ T.lits then some true else some false)
          else descentSat cs w F (extendσ σ T x) x v

/-- The value of `descentSat` at the active step. -/
theorem descentSat_succ_apply {cs : List (Clause n)} {w F : ℕ} {σ : Fin n → Option Bool}
    {T : Clause n} (x : Fin n → Bool) (hany : anyTermSat cs σ = false)
    (hact : activeTerm cs σ = some T) (v : Fin n) :
    descentSat cs w (F + 1) σ x v =
      if σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) then
        (if (Rung4Literal.pos v) ∈ T.lits then some true else some false)
      else descentSat cs w F (extendσ σ T x) x v := by
  rw [descentSat]; simp only [hany, Bool.false_eq_true, if_false, hact]

/-- **The satisfying boundary extends `σ`.** -/
theorem descentSat_extends (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool), Extends σ (descentSat cs w F σ x) := by
  intro F
  induction F with
  | zero => intro σ x v b h; rw [descentSat]; exact h
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => intro v b h; rw [descentSat]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : activeTerm cs σ with
      | none =>
        intro v b h; rw [descentSat]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        intro v b h
        rw [descentSat_succ_apply x hany hact]
        by_cases hc : σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)
        · rw [h] at hc; exact absurd hc.1 (by simp)
        · rw [if_neg hc]
          have hext1 : extendσ σ T x v = some b := extendσ_extends σ T x v b h
          exact ih (extendσ σ T x) x v b hext1

/-- **The satisfying boundary satisfies the active term.** -/
theorem descentSat_sat_term {cs : List (Clause n)} {w F : ℕ} {σ : Fin n → Option Bool} {T : Clause n}
    (x : Fin n → Bool) (hcons : Consistent T) (hany : anyTermSat cs σ = false)
    (hact : activeTerm cs σ = some T) :
    termSat (descentSat cs w (F + 1) σ x) T = true := by
  have hnf : termFalsified σ T = false := by
    have hfind : cs.find?
        (fun U => !termFalsified σ U && decide (0 < (freeLits σ U).length)) = some T := by
      rw [← activeTerm_eq_find hany]; exact hact
    have hp := List.find?_some hfind
    cases hx : termFalsified σ T with
    | false => rfl
    | true => rw [hx] at hp; simp at hp
  have hnf' : ∀ ℓ ∈ T.lits, litFalse σ ℓ = false := by
    intro ℓ hℓ
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have : termFalsified σ T = true := by
      rw [termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓ, hc⟩
    rw [hnf] at this; exact absurd this (by simp)
  rw [termSat, List.all_eq_true]
  intro ℓ hℓ
  have hextσ : Extends σ (descentSat cs w F (extendσ σ T x) x) :=
    Extends_trans (extendσ_extends σ T x) (descentSat_extends cs w F (extendσ σ T x) x)
  cases ℓ with
  | pos v =>
    have hfalse := hnf' (Rung4Literal.pos v) hℓ
    have hbv : descentSat cs w (F + 1) σ x v = some true := by
      rw [descentSat_succ_apply x hany hact]
      by_cases hvn : σ v = none
      · rw [if_pos ⟨hvn, Or.inl hℓ⟩, if_pos hℓ]
      · rw [if_neg (fun h => hvn h.1)]
        have hsv : σ v = some true := by
          cases hb : σ v with
          | none => exact absurd hb hvn
          | some b =>
            cases b with
            | true => rfl
            | false => simp [litFalse, Depth3.litFixedVal, hb] at hfalse
        exact hextσ v true hsv
    simp [Depth3.litTrue, Depth3.litFixedVal, hbv]
  | neg v =>
    have hfalse := hnf' (Rung4Literal.neg v) hℓ
    have hpos : (Rung4Literal.pos v) ∉ T.lits := fun hp => hcons v ⟨hp, hℓ⟩
    have hbv : descentSat cs w (F + 1) σ x v = some false := by
      rw [descentSat_succ_apply x hany hact]
      by_cases hvn : σ v = none
      · rw [if_pos ⟨hvn, Or.inr hℓ⟩, if_neg hpos]
      · rw [if_neg (fun h => hvn h.1)]
        have hsv : σ v = some false := by
          cases hb : σ v with
          | none => exact absurd hb hvn
          | some b =>
            cases b with
            | false => rfl
            | true => simp [litFalse, Depth3.litFixedVal, hb] at hfalse
        exact hextσ v false hsv
    simp [Depth3.litTrue, Depth3.litFixedVal, hbv]

/-- **Term recovery.**  The active term is recovered as the first term satisfied by the boundary — for any
`σ`, without storing it. -/
theorem descentSat_firstSat {cs : List (Clause n)} {w F : ℕ} {σ : Fin n → Option Bool} {T : Clause n}
    (x : Fin n → Bool) (hcons : Consistent T) (hany : anyTermSat cs σ = false)
    (hact : activeTerm cs σ = some T) :
    cs.find? (termSat (descentSat cs w (F + 1) σ x)) = some T :=
  firstSat_eq_active (descentSat_extends cs w (F + 1) σ x) hact (descentSat_sat_term x hcons hany hact)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descentSat_firstSat
