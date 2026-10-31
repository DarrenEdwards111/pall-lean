import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFullSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestPathLabel

/-!
# The full path realises the tree depth — the integration bridge (branch only)

`deepestFullSeq` (the satisfy/falsify-bit path) and the existing `deepestPathLabel` (the branch-bit
path) have *identical control flow* and record one entry per step — they differ only in the recorded
bit.  Hence they have the same length, and by `deepestPathLabel_length_eq_depth` that length is the
canonical tree depth:

  `deepestFullSeq_length_eq_depth : (deepestFullSeq cs F σ).length = (canonicalDT cs F σ).depth`.

This is the bridge that turns the full-path switching count into a genuine **max-depth** count: the
exponent `s` is the tree depth.  It is exactly the quantity the depth-3 collapse needs, and the one the
satisfy-position (Side-A) route provably could *not* control (`encLits_length_lt_depth`, Fence 1).

Clean, no `sorry`.  `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The full path and the branch-bit path have the same length (identical control flow). -/
theorem deepestFullSeq_length_eq_pathLabel (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      (deepestFullSeq cs F σ).length = (deepestPathLabel cs F σ).length := by
  intro F
  induction F with
  | zero => intro σ; rfl
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestFullSeq, deepestPathLabel]; simp [hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [deepestFullSeq, deepestPathLabel]; simp [hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => rw [deepestFullSeq, deepestPathLabel]; simp [hany, hact, hh]
        | some ℓ =>
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestFullSeq, deepestPathLabel]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd, List.length_cons,
              ih (fixVar σ (litVar ℓ) false)]
          · rw [deepestFullSeq, deepestPathLabel]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd, List.length_cons,
              ih (fixVar σ (litVar ℓ) true)]

/-- **The full path realises the canonical tree depth.** -/
theorem deepestFullSeq_length_eq_depth (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) :
    (deepestFullSeq cs F σ).length = (canonicalDT cs F σ).depth :=
  (deepestFullSeq_length_eq_pathLabel cs F σ).trans (deepestPathLabel_length_eq_depth cs F σ)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestFullSeq_length_eq_depth
