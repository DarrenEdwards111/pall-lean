import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestBranch

/-!
# The satisfy-step count is at most the tree depth

The replay tight count is parameterised by `s = (deepestSatSeq …).length` — the number of *satisfy*
steps, the only steps the `(2w)^s` label pays for (falsify steps are recovered label-free by
`decodedSel`).  Here we connect that `s` to the switching-lemma quantity, the canonical decision-tree
depth: every satisfy step is a step of the deepest branch, so

    (deepestSatSeq cs F ρ).length ≤ (canonicalDT cs F ρ).depth.

So the label cost `(2w)^s` is at most `(2w)^depth` — the replay count is sharp relative to the depth.

* `deepestSatSeq_length_le_deepestPath_length` — satisfy steps are a subset of the deepest branch.
* `deepestSatSeq_length_le_depth` — hence at most the canonical decision-tree depth.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Satisfy steps are a subset of the deepest branch.**  `deepestPath` records every step;
`deepestSatSeq` records only the satisfy steps — so its length is no larger. -/
theorem deepestSatSeq_length_le_deepestPath_length (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      (deepestSatSeq cs F σ).length ≤ (deepestPath cs F σ).length := by
  intro F
  induction F with
  | zero => intro σ; simp [deepestSatSeq, deepestPath]
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [deepestSatSeq, deepestPath, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp [deepestSatSeq, deepestPath, hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp [deepestSatSeq, deepestPath, hany, hact, hh]
        | some ℓ =>
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestSatSeq, deepestPath]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_pos hd, if_pos hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
            · rw [if_pos hf, id_eq, List.length_cons]
              exact le_trans (ih (fixVar σ (litVar ℓ) false)) (Nat.le_succ _)
            · rw [if_neg hf, List.length_cons, List.length_cons]
              exact Nat.succ_le_succ (ih (fixVar σ (litVar ℓ) false))
          · rw [deepestSatSeq, deepestPath]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_neg hd, if_neg hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
            · rw [if_pos hf, id_eq, List.length_cons]
              exact le_trans (ih (fixVar σ (litVar ℓ) true)) (Nat.le_succ _)
            · rw [if_neg hf, List.length_cons, List.length_cons]
              exact Nat.succ_le_succ (ih (fixVar σ (litVar ℓ) true))

/-- **The satisfy-step count is at most the tree depth.**  Combining with
`deepestPath_length_eq_depth`. -/
theorem deepestSatSeq_length_le_depth (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) :
    (deepestSatSeq cs F σ).length ≤ (canonicalDT cs F σ).depth := by
  rw [← deepestPath_length_eq_depth]
  exact deepestSatSeq_length_le_deepestPath_length cs F σ

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_length_le_depth
