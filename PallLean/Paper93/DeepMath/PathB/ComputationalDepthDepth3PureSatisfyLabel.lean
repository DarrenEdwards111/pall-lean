import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyConfine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPositionLit

/-!
# Pure-satisfy regime: position packaging — the satisfy set decoded from `T₀` + positions

The pure-satisfy regime keeps one clause `T₀` active throughout (`activeTerm_deepestEnd_pure_satisfy`)
with the satisfy variables confined to it (`deepestSatSel_subset_clauseVars`).  This file does the
**position packaging**: it records, per satisfy step, the position of the active literal inside `T₀`,
and proves the decoder — which reads each variable off `T₀` at its recorded position — recovers
`deepestSatSel` exactly.

* `deepestSatPos` — the per-satisfy-step position list (the canonical `pivotPosOf` at each step),
  mirroring `deepestSatSel` with `pivotPosOf cs σ` in place of `litVar ℓ`.
* `decodeSatPos T ps` — the decoder: map each position through clause `T` to a variable.
* `decodeSatPos_cons` — one decoded position prepends its variable.
* `deepestSatSel_eq_decode_pure_satisfy` — **the recovery**: in the pure-satisfy regime,
  `deepestSatSel cs F σ = decodeSatPos T (deepestSatPos cs F σ)` for the constant active clause `T`.
* `deepestSatSel_decoded_from_leaf` — the same with the clause read *from the leaf*,
  `T = activeTerm cs (deepestEnd cs F σ)` (identified there by `activeTerm_deepestEnd_pure_satisfy`):
  the decoder needs only the end-state and the position list.

So the pure-satisfy satisfy recovery is now a closed loop on proved components: identify `T₀` from the
leaf, decode each position through it.  The positions are `idxOf` values `< |T₀.lits| ≤ w`, so the list
embeds into the `(2w)^s` label (`PathLabel w s`) by the existing `flatToLabel` packaging — the last
remaining piece is that pure index→`Fin w` coercion, no new mathematics.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The per-satisfy-step **position list** of the deepest branch: at each satisfy step record the
canonical position `pivotPosOf cs σ` of the active literal inside its clause; skip falsify steps.
Mirrors `deepestSatSel` exactly, with `pivotPosOf cs σ` in place of `litVar ℓ`. -/
def deepestSatPos (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List ℕ
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => []
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ
                 then id else List.cons (SwitchingCounting.pivotPosOf cs σ))
                 (deepestSatPos cs fuel (fixVar σ (litVar ℓ) false))
          else (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ
                 then id else List.cons (SwitchingCounting.pivotPosOf cs σ))
                 (deepestSatPos cs fuel (fixVar σ (litVar ℓ) true))

/-- The decoder: map each recorded position through clause `T` to its variable. -/
def decodeSatPos (T : Clause n) (ps : List ℕ) : Finset (Fin n) :=
  (ps.filterMap (fun p => (SwitchingCounting.clauseLitAt T p).map litVar)).toFinset

/-- One decoded position prepends its variable. -/
theorem decodeSatPos_cons (T : Clause n) {p : ℕ} {v : Fin n} {ps : List ℕ}
    (h : (SwitchingCounting.clauseLitAt T p).map litVar = some v) :
    decodeSatPos T (p :: ps) = insert v (decodeSatPos T ps) := by
  unfold decodeSatPos
  simp only [List.filterMap_cons, h, List.toFinset_cons]

/-- **The pure-satisfy recovery.**  In the pure-satisfy regime, the satisfy set is exactly the
positions decoded through the constant active clause `T`:
`deepestSatSel cs F σ = decodeSatPos T (deepestSatPos cs F σ)`. -/
theorem deepestSatSel_eq_decode_pure_satisfy (cs : List (Clause n)) {T : Clause n}
    (hclean : CleanClause T) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      SwitchingCounting.activeTerm cs σ = some T →
      deepestFalSel cs F σ = ∅ →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      deepestSatSel cs F σ = decodeSatPos T (deepestSatPos cs F σ) := by
  intro F
  induction F with
  | zero => intro σ _ _ _; rw [deepestSatSel, deepestSatPos]; rfl
  | succ F ih =>
    intro σ hact hfal hsat
    have hns : SwitchingCounting.anyTermSat cs σ = false :=
      SwitchingCounting.activeTerm_anyTermSat_false hact
    obtain ⟨_, hTfree⟩ := SwitchingCounting.activeTerm_pred hact
    obtain ⟨ℓ, hℓhead⟩ : ∃ ℓ, (SwitchingCounting.freeLits σ T).head? = some ℓ := by
      cases hh : SwitchingCounting.freeLits σ T with
      | nil => rw [hh] at hTfree; simp at hTfree
      | cons a _ => exact ⟨a, rfl⟩
    have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
      unfold SwitchingCounting.activeTermLit; rw [hact]; exact hℓhead
    have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp (List.mem_of_mem_head? hℓhead)).1
    -- the head position decodes to `litVar ℓ` through the (constant) active clause `T`.
    have hclat : (SwitchingCounting.clauseLitAt T (SwitchingCounting.pivotPosOf cs σ)).map litVar
        = some (litVar ℓ) := by
      rw [SwitchingCounting.clauseLitAt_pivotPosOf hact (by rw [hatl]; rfl), hatl]; rfl
    -- recursive IH, after a satisfy step in bit `b`.
    have body : ∀ b : Bool,
        deepestFalSel cs F (fixVar σ (litVar ℓ) b) = ∅ →
        SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = false →
        SwitchingCounting.anyTermSat cs (deepestEnd cs F (fixVar σ (litVar ℓ) b)) = false →
        deepestSatSel cs F (fixVar σ (litVar ℓ) b)
          = decodeSatPos T (deepestSatPos cs F (fixVar σ (litVar ℓ) b)) := by
      intro b hfal_b hf_b hsat_b
      have hns_b : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false :=
        anyTermSat_of_deepestEnd_false cs F _ hsat_b
      have hnf_b : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T = false :=
        termFalsified_satisfy_step hact hclean hℓT hf_b
      have hfree_b : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length := by
        by_contra hc
        rw [Nat.not_lt, Nat.le_zero, List.length_eq_zero_iff] at hc
        have hsatU : SwitchingCounting.termSat (fixVar σ (litVar ℓ) b) T = false := by
          by_contra hs
          rw [Bool.not_eq_false] at hs
          have : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = true := by
            rw [SwitchingCounting.anyTermSat, List.any_eq_true]
            exact ⟨T, SwitchingCounting.activeTerm_mem hact, hs⟩
          rw [hns_b] at this; exact absurd this (by simp)
        have := SwitchingCounting.term_falsified_of_not_sat_no_free hsatU hc
        rw [this] at hnf_b; exact absurd hnf_b (by simp)
      exact ih _ (activeTerm_advance_stable hact hatl hns_b hnf_b hfree_b) hfal_b hsat_b
    by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
        (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
    · -- `b = false`
      rw [deepestFalSel] at hfal
      rw [deepestEnd] at hsat
      rw [deepestSatSel, deepestSatPos]
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_pos hd] at hfal hsat
      rw [if_pos hd, if_pos hd]
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        rw [if_neg (by rw [hh]; simp), if_neg (by rw [hh]; simp)]
        rw [decodeSatPos_cons T hclat, body false hfal hh hsat]
    · -- `b = true`
      rw [deepestFalSel] at hfal
      rw [deepestEnd] at hsat
      rw [deepestSatSel, deepestSatPos]
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_neg hd] at hfal hsat
      rw [if_neg hd, if_neg hd]
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        rw [if_neg (by rw [hh]; simp), if_neg (by rw [hh]; simp)]
        rw [decodeSatPos_cons T hclat, body true hfal hh hsat]

/-- **The satisfy set decoded from the leaf.**  Reading the clause off the end-state
(`T = activeTerm cs (deepestEnd cs F σ)`, the constant active clause) and decoding the position list
recovers the satisfy set — so the decoder needs only the end-state and the positions. -/
theorem deepestSatSel_decoded_from_leaf (cs : List (Clause n)) {T : Clause n}
    (hclean : CleanClause T) (F : ℕ) (σ : Fin n → Option Bool)
    (hact : SwitchingCounting.activeTerm cs σ = some T) (hfal : deepestFalSel cs F σ = ∅)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false) :
    SwitchingCounting.activeTerm cs (deepestEnd cs F σ) = some T ∧
      deepestSatSel cs F σ = decodeSatPos T (deepestSatPos cs F σ) :=
  ⟨activeTerm_deepestEnd_pure_satisfy cs hclean F σ hact hfal hsat,
   deepestSatSel_eq_decode_pure_satisfy cs hclean F σ hact hfal hsat⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSel_eq_decode_pure_satisfy
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSel_decoded_from_leaf
