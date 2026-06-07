import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockCompat
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockAdvance

/-!
# Block-DT model, foundation 10c: compact-label recovery (branch only)

The compact peel recovers the block stream from the boundary + **in-clause** stars-pattern (positions
`< w`), and the global masks are reconstructed from it.

* `compactMasks` — per block, the free-literal positions (`Finset (Fin w)`).
* `blockPeelC` — the peel using compact labels (reset via `posMaskOf` of the found term).
* `block_recovery_compact` — `blockPeelC cs w (compactMasks cs w F ρ) (blockEncode cs F ρ) = blockStream`.
* `blockMasks_eq_zipWith` — `blockMasks = zipWith posMaskOf (blockStream) (compactMasks)`.

Clean, no `sorry`.  AC⁰/depth-3.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Per block: the free-literal positions (`Fin w`) of the active term. -/
def compactMasks (cs : List (Clause n)) (w : ℕ) : ℕ → (Fin n → Option Bool) → List (Finset (Fin w))
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => freePosOf w σ T :: compactMasks cs w fuel (killTerm σ T)

/-- The active term is a member of `cs`. -/
private theorem activeTerm_mem' {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T) : T ∈ cs := by
  have hf : cs.find? (fun U => !SwitchingCounting.termFalsified σ U
      && decide (0 < (SwitchingCounting.freeLits σ U).length)) = some T := by
    rw [← SwitchingCounting.activeTerm_eq_find hany]; exact hact
  exact List.mem_of_find?_eq_some hf

/-- The compact peel: find first satisfied term, reset via the in-clause positions, recurse. -/
def blockPeelC (cs : List (Clause n)) (w : ℕ) :
    List (Finset (Fin w)) → (Fin n → Option Bool) → List (Clause n)
  | [], _ => []
  | cl :: cls, σ =>
    match cs.find? (SwitchingCounting.termSat σ) with
    | none => []
    | some T => T :: blockPeelC cs w cls (resetMask T (posMaskOf w T cl) σ)

/-- **Compact recovery.**  The compact peel of the boundary recovers the block stream. -/
theorem block_recovery_compact (cs : List (Clause n)) (w : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      blockPeelC cs w (compactMasks cs w F σ) (blockEncode cs F σ) = blockStream cs F σ := by
  intro F
  induction F with
  | zero => intro σ; rw [compactMasks, blockPeelC, blockStream]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [show compactMasks cs w (F + 1) σ = [] by rw [compactMasks]; simp [hany],
          show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany], blockPeelC]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [show compactMasks cs w (F + 1) σ = [] by rw [compactMasks]; simp [hany, hact],
            show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany, hact], blockPeelC]
      | some T =>
        have hTcons : Consistent T := hcons T (activeTerm_mem' hany hact)
        have hTw : T.lits.length ≤ w := hw T (activeTerm_mem' hany hact)
        have hcm : compactMasks cs w (F + 1) σ
            = freePosOf w σ T :: compactMasks cs w F (killTerm σ T) := by
          rw [compactMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hstream : blockStream cs (F + 1) σ = T :: blockStream cs F (killTerm σ T) := by
          rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hcm, hstream, blockPeelC]
        simp only [blockEncode_firstSat hTcons hany hact, posMaskOf_freePosOf w σ T hTw,
          resetMask_advance hany hact, ih (killTerm σ T)]

/-- **Mask reconstruction.**  The global masks are the per-block `posMaskOf` of the stream and the
compact labels. -/
theorem blockMasks_eq_zipWith (cs : List (Clause n)) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      blockMasks cs F σ
        = List.zipWith (posMaskOf w) (blockStream cs F σ) (compactMasks cs w F σ) := by
  intro F
  induction F with
  | zero => intro σ; rw [blockMasks, blockStream, compactMasks]; rfl
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [show blockMasks cs (F + 1) σ = [] by rw [blockMasks]; simp [hany],
          show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany]]
      rfl
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [show blockMasks cs (F + 1) σ = [] by rw [blockMasks]; simp [hany, hact],
            show blockStream cs (F + 1) σ = [] by rw [blockStream]; simp [hany, hact]]
        rfl
      | some T =>
        have hTw : T.lits.length ≤ w := hw T (activeTerm_mem' hany hact)
        have hbm : blockMasks cs (F + 1) σ
            = blockMaskPred σ T :: blockMasks cs F (killTerm σ T) := by
          rw [blockMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hstream : blockStream cs (F + 1) σ = T :: blockStream cs F (killTerm σ T) := by
          rw [blockStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hcm : compactMasks cs w (F + 1) σ
            = freePosOf w σ T :: compactMasks cs w F (killTerm σ T) := by
          rw [compactMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hbm, hstream, hcm, List.zipWith_cons_cons, posMaskOf_freePosOf w σ T hTw,
            ih (killTerm σ T)]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.block_recovery_compact
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.blockMasks_eq_zipWith
