import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockInject

/-!
# Block-DT model, foundation 8: star conservation for the boundary (branch only)

The boundary `blockEncode cs F ρ` fixes **exactly** the masked (block) variables: off them it equals
`ρ`, and on them it is fixed (`≠ none`).  Hence

  `stars (blockEncode cs F ρ) + |maskedVars (blockMasks cs F ρ)| = stars ρ`,

so the boundary leaf has fewer stars — by the total number of block variables.  This characterizes the
leaf shell for the holographic count `block_count`.

* `masked_imp_free`, `blockEncode_off_mask` — corollaries of `blockEncode_recover`.
* `blockEncode_masked_fixed` — a masked coordinate is fixed in the boundary.
* `freeVars_blockEncode` — `freeVars (blockEncode cs F ρ) = freeVars ρ \ maskedVars`.
* `stars_blockEncode` — **star conservation**: `stars (blockEncode) + |maskedVars| = stars ρ`.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

**Honest scope.**  The block model sets a *variable* number of variables per block, so `|maskedVars|`
(the total block-variable count, `∈ [s, s·w]` for `s` blocks of width `≤ w`) is the stars dropped — not
the clean `s` of the binary model.  Bounding `|maskedVars| ≥ s` (≥ one per block) gives
`stars (blockEncode) ≤ K - s`; the label-space bound and the regime are the remaining arithmetic.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The set of masked (block) coordinates. -/
def maskedVars (masks : List (Fin n → Bool)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => masks.any (fun mask => mask v))

/-- A masked coordinate is free in `ρ`. -/
theorem masked_imp_free (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) {v : Fin n}
    (hv : (blockMasks cs F ρ).any (fun mask => mask v) = true) : ρ v = none := by
  have h := congrFun (blockEncode_recover cs F ρ) v
  rw [recoverRho, if_pos hv] at h
  exact h.symm

/-- Off the mask, the boundary equals `ρ`. -/
theorem blockEncode_off_mask (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) {v : Fin n}
    (hv : (blockMasks cs F ρ).any (fun mask => mask v) = false) :
    blockEncode cs F ρ v = ρ v := by
  have h := congrFun (blockEncode_recover cs F ρ) v
  rw [recoverRho, if_neg (by rw [hv]; simp)] at h
  exact h

/-- A masked coordinate is fixed in the boundary. -/
theorem blockEncode_masked_fixed (cs : List (Clause n)) :
    ∀ (F : ℕ) (ρ : Restriction n) (v : Fin n),
      (blockMasks cs F ρ).any (fun mask => mask v) = true → blockEncode cs F ρ v ≠ none := by
  intro F
  induction F with
  | zero => intro ρ v h; rw [blockMasks] at h; simp at h
  | succ F ih =>
    intro ρ v h
    cases hany : SwitchingCounting.anyTermSat cs ρ with
    | true => rw [blockMasks] at h; simp [hany] at h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs ρ with
      | none => rw [blockMasks] at h; simp [hany, hact] at h
      | some T =>
        rw [blockMasks] at h
        simp only [hany, Bool.false_eq_true, if_false, hact, List.any_cons] at h
        rw [blockEncode_succ_apply hany hact]
        by_cases hmT : (ρ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits))
        · rw [if_pos hmT]; by_cases hp : (Rung4Literal.pos v) ∈ T.lits <;> simp [hp]
        · rw [if_neg hmT]
          apply ih (killTerm ρ T) v
          rw [decide_eq_false_iff_not.mpr hmT, Bool.false_or] at h
          exact h

/-- `freeVars (blockEncode cs F ρ) = freeVars ρ \ maskedVars`. -/
theorem freeVars_blockEncode (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    SwitchingCounting.freeVars (blockEncode cs F ρ)
      = SwitchingCounting.freeVars ρ \ maskedVars (blockMasks cs F ρ) := by
  ext v
  simp only [SwitchingCounting.mem_freeVars, Finset.mem_sdiff, maskedVars, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hm : (blockMasks cs F ρ).any (fun mask => mask v) = true
  · constructor
    · intro hbn; exact absurd hbn (blockEncode_masked_fixed cs F ρ v hm)
    · intro ⟨_, hnm⟩; exact absurd hm hnm
  · rw [Bool.not_eq_true] at hm
    rw [blockEncode_off_mask cs F ρ hm]
    constructor
    · intro hρn; exact ⟨hρn, by rw [hm]; simp⟩
    · intro ⟨hρn, _⟩; exact hρn

/-- **Star conservation for the boundary.**  `stars (blockEncode) + |maskedVars| = stars ρ`. -/
theorem stars_blockEncode (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    SwitchingCounting.stars (blockEncode cs F ρ) + (maskedVars (blockMasks cs F ρ)).card
      = SwitchingCounting.stars ρ := by
  unfold SwitchingCounting.stars
  rw [freeVars_blockEncode]
  apply Finset.card_sdiff_add_card_eq_card
  intro v hv
  rw [maskedVars, Finset.mem_filter] at hv
  exact SwitchingCounting.mem_freeVars.mpr (masked_imp_free cs F ρ hv.2)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_blockEncode
