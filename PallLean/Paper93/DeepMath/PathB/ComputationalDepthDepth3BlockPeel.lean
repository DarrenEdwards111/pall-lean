import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockAdvance

/-!
# Block-DT model, foundation 6: end-to-end recovery (branch only)

The label-aware peel recovers the whole block stream from the boundary `blockEncode`, composing the
proven head recovery (`blockEncode_firstSat`) and advance (`blockEncode_advance`) by induction.

* `resetMask T mask σ` — reset the `mask`-selected coordinates to `T`'s killing values.
* `blockMasks cs F σ` — the stars-pattern: per block, the block-variable mask `{v : σ v = none ∧ v ∈ T}`.
* `blockPeel cs masks σ` — find first satisfied term, reset its block variables (head mask), recurse.
* `block_recovery` — **the composition theorem**: for a DNF of consistent terms,
  `blockPeel cs (blockMasks cs F ρ) (blockEncode cs F ρ) = blockStream cs F ρ`.  The active-clause
  stream is recovered from the boundary `(blockEncode ρ)` + the stars-pattern, *for any `ρ`* (falsifying
  or not), with **no clause identity** transmitted — the holographic recovery, end to end.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Reset the `mask`-selected coordinates to `T`'s killing values. -/
def resetMask (T : Clause n) (mask : Fin n → Bool) (σ : Restriction n) : Restriction n :=
  fun v => if mask v then (if (Rung4Literal.pos v) ∈ T.lits then some false else some true) else σ v

/-- The stars-pattern: per block, the mask of block variables `{v : σ v = none ∧ v ∈ T}`. -/
def blockMasks (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (Fin n → Bool)
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T =>
        (fun v => decide (σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)))
          :: blockMasks cs fuel (killTerm σ T)

/-- The label-aware peel: find first satisfied term, reset its block variables, recurse. -/
def blockPeel (cs : List (Clause n)) : List (Fin n → Bool) → (Fin n → Option Bool) → List (Clause n)
  | [], _ => []
  | mask :: masks, σ =>
    match cs.find? (SwitchingCounting.termSat σ) with
    | none => []
    | some T => T :: blockPeel cs masks (resetMask T mask σ)

/-- The killing value of a block variable depends only on `T`. -/
theorem killTerm_block_val {σ : Restriction n} {T : Clause n} {v : Fin n} (hvn : σ v = none)
    (hvT : (Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits) :
    killTerm σ T v = (if (Rung4Literal.pos v) ∈ T.lits then some false else some true) := by
  simp only [killTerm]
  rw [if_pos hvn]
  by_cases hp : (Rung4Literal.pos v) ∈ T.lits
  · rw [if_pos hp, if_pos hp]
  · rcases hvT with hp' | hn
    · exact absurd hp' hp
    · rw [if_neg hp, if_pos hn, if_neg hp]

/-- The advance, in `resetMask` form. -/
theorem resetMask_advance {cs : List (Clause n)} {F : ℕ} {σ : Restriction n} {T : Clause n}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) :
    resetMask T
        (fun v => decide (σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)))
        (blockEncode cs (F + 1) σ)
      = blockEncode cs F (killTerm σ T) := by
  funext v
  rw [resetMask, blockEncode_advance hany hact v]
  simp only [decide_eq_true_eq]
  by_cases hc : σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)
  · rw [if_pos hc, if_pos hc, ← killTerm_block_val hc.1 hc.2]
  · rw [if_neg hc, if_neg hc]

/-- The active term is a member of `cs`. -/
private theorem activeTerm_mem {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) : T ∈ cs := by
  have hfind : cs.find?
      (fun U => !SwitchingCounting.termFalsified σ U
        && decide (0 < (SwitchingCounting.freeLits σ U).length)) = some T := by
    rw [← SwitchingCounting.activeTerm_eq_find hany]; exact hact
  exact List.mem_of_find?_eq_some hfind

/-- **End-to-end holographic recovery.**  For a DNF of consistent terms, the label-aware peel of the
boundary `blockEncode` recovers the block active-clause stream — for any `ρ`. -/
theorem block_recovery (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      blockPeel cs (blockMasks cs F σ) (blockEncode cs F σ) = blockStream cs F σ := by
  intro F
  induction F with
  | zero => intro σ; rw [blockMasks, blockPeel, blockStream]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [show blockMasks cs (F + 1) σ = [] by rw [blockMasks]; simp [hany],
          show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany], blockPeel]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [show blockMasks cs (F + 1) σ = [] by rw [blockMasks]; simp [hany, hact],
            show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany, hact], blockPeel]
      | some T =>
        have hTcons : Consistent T := hcons T (activeTerm_mem hany hact)
        have hmask : blockMasks cs (F + 1) σ
            = (fun v => decide (σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits
                ∨ (Rung4Literal.neg v) ∈ T.lits))) :: blockMasks cs F (killTerm σ T) := by
          rw [blockMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hstream : blockStream cs (F + 1) σ = T :: blockStream cs F (killTerm σ T) := by
          rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hmask, hstream, blockPeel]
        simp only [blockEncode_firstSat hTcons hany hact, resetMask_advance hany hact, ih (killTerm σ T)]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_recovery
