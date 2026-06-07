import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFullSeq

/-!
# `hpos` from clause width (branch only)

For a width-`w` DNF (every clause has at most `w` literals), every position recorded in the deepest
full path is `< w`: the recorded position is the pivot `pivotPosOf cs σ`, which is the index of the
active literal in its (active, hence `cs`-member) clause, so it is below that clause's width
(`pivotPosOf_lt`), which is `≤ w` by hypothesis.

* `deepestFullSeq_pos_lt_width` — discharges the `hpos` hypothesis of the switching count from the
  structural width bound `∀ T ∈ cs, T.lits.length ≤ w`.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **`hpos` from clause width.**  If every clause of `cs` has at most `w` literals, every position in
the deepest full path is `< w`. -/
theorem deepestFullSeq_pos_lt_width (cs : List (Clause n)) (w : ℕ)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool), ∀ p ∈ deepestFullSeq cs F σ, p.1 < w := by
  intro F
  induction F with
  | zero => intro σ p hmem; rw [deepestFullSeq] at hmem; exact absurd hmem (by simp)
  | succ F ih =>
    intro σ p hmem
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [deepestFullSeq] at hmem; simp only [hany, if_true] at hmem; exact absurd hmem (by simp)
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestFullSeq] at hmem
        simp only [hany, Bool.false_eq_true, if_false, hact] at hmem; exact absurd hmem (by simp)
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestFullSeq] at hmem
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hmem; exact absurd hmem (by simp)
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hTmem : T ∈ cs := by
            have hfind : cs.find?
                (fun T => !SwitchingCounting.termFalsified σ T
                  && decide (0 < (SwitchingCounting.freeLits σ T).length)) = some T := by
              rw [← SwitchingCounting.activeTerm_eq_find hany]; exact hact
            exact List.mem_of_find?_eq_some hfind
          have hpiv : SwitchingCounting.pivotPosOf cs σ < w := by
            have h1 := pivotPosOf_lt hact hatl
            have h2 := hw T hTmem
            omega
          have body : ∀ b : Bool,
              deepestFullSeq cs (F + 1) σ
                = (SwitchingCounting.pivotPosOf cs σ,
                    !SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ)
                  :: deepestFullSeq cs F (fixVar σ (litVar ℓ) b) →
              p.1 < w := by
            intro b hSeq
            rw [hSeq, List.mem_cons] at hmem
            rcases hmem with heq | htl
            · rw [heq]; exact hpiv
            · exact ih (fixVar σ (litVar ℓ) b) p htl
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · refine body false ?_
            rw [deepestFullSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_pos hd]
          · refine body true ?_
            rw [deepestFullSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh, if_neg hd]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestFullSeq_pos_lt_width
