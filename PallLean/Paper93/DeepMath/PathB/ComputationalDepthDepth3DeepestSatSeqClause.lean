import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestLeafActive

/-!
# The decode's clauses are leaf-readable

Bridge between the per-step-clause decode (`deepestSatSel_eq_decodeSatSeq`) and the end-state: every
clause recorded in `deepestSatSeq` is either falsified at the leaf or is the leaf's active clause —
both readable from the end-state.  So the decoder's `(clause, position)` sequence draws its clauses
from the finite, end-state-readable family, and only the *order/blocking* of positions remains to be
recovered.

* `deepestSatSeq_clause_leaf` — every `(C, p) ∈ deepestSatSeq cs F σ` has `C` falsified at the leaf or
  equal to the leaf's active clause (when the leaf is unsatisfied).

The proof mirrors `deepestSel_mem_leaf_clause`, with the head entry's clause `T` (the step's active
clause) classified at the leaf via `activeTerm_deepestEnd_of_not_falsified`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The decode's clauses are leaf-readable.**  Every clause recorded in `deepestSatSeq` is falsified
at the leaf or is the leaf's active clause. -/
theorem deepestSatSeq_clause_leaf (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) {C : Clause n} {p : ℕ},
      (C, p) ∈ deepestSatSeq cs F σ →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      SwitchingCounting.termFalsified (deepestEnd cs F σ) C = true ∨
        SwitchingCounting.activeTerm cs (deepestEnd cs F σ) = some C := by
  intro F
  induction F with
  | zero => intro σ C p hmem _; rw [deepestSatSeq] at hmem; exact absurd hmem (by simp)
  | succ F ih =>
    intro σ C p hmem hsat
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSatSeq] at hmem; simp only [hany, if_true] at hmem; exact absurd hmem (by simp)
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSatSeq] at hmem
        simp only [hany, Bool.false_eq_true, if_false, hact] at hmem; exact absurd hmem (by simp)
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSatSeq] at hmem
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hmem; exact absurd hmem (by simp)
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          have body : ∀ b : Bool,
              deepestEnd cs (F + 1) σ = deepestEnd cs F (fixVar σ (litVar ℓ) b) →
              deepestSatSeq cs (F + 1) σ =
                (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ
                  then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                  (deepestSatSeq cs F (fixVar σ (litVar ℓ) b)) →
              SwitchingCounting.termFalsified (deepestEnd cs (F + 1) σ) C = true ∨
                SwitchingCounting.activeTerm cs (deepestEnd cs (F + 1) σ) = some C := by
            intro b hEnd hSeq
            rw [hEnd] at hsat ⊢
            rw [hSeq] at hmem
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = true
            · rw [if_pos hf, id_eq] at hmem
              exact ih (fixVar σ (litVar ℓ) b) hmem hsat
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp)] at hmem
              rw [List.mem_cons] at hmem
              rcases hmem with heq | hmem'
              · have hCT : C = T := congrArg Prod.fst heq
                subst hCT
                by_cases hTf :
                    SwitchingCounting.termFalsified (deepestEnd cs F (fixVar σ (litVar ℓ) b)) C = true
                · exact Or.inl hTf
                · rw [Bool.not_eq_true] at hTf
                  have hns_b : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false :=
                    anyTermSat_of_deepestEnd_false cs F _ hsat
                  have hnf_b : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) C = false := by
                    by_contra hc
                    rw [Bool.not_eq_false] at hc
                    have hp := termFalsified_deepestEnd cs F (fixVar σ (litVar ℓ) b) C hc
                    rw [hp] at hTf; exact absurd hTf (by simp)
                  have hfree_b : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) C).length := by
                    by_contra hc0
                    rw [Nat.not_lt, Nat.le_zero, List.length_eq_zero_iff] at hc0
                    have hsatC : SwitchingCounting.termSat (fixVar σ (litVar ℓ) b) C = false := by
                      by_contra hs
                      rw [Bool.not_eq_false] at hs
                      have : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = true := by
                        rw [SwitchingCounting.anyTermSat, List.any_eq_true]
                        exact ⟨C, SwitchingCounting.activeTerm_mem hact, hs⟩
                      rw [hns_b] at this; exact absurd this (by simp)
                    have hff := SwitchingCounting.term_falsified_of_not_sat_no_free hsatC hc0
                    rw [hff] at hnf_b; exact absurd hnf_b (by simp)
                  have hactτ : SwitchingCounting.activeTerm cs (fixVar σ (litVar ℓ) b) = some C :=
                    activeTerm_fixVar_stable hact hfree hns_b hnf_b hfree_b
                  exact Or.inr (activeTerm_deepestEnd_of_not_falsified cs F
                    (fixVar σ (litVar ℓ) b) C hactτ hsat hTf)
              · exact ih (fixVar σ (litVar ℓ) b) hmem' hsat
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · refine body false ?_ ?_
            · rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
            · rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
          · refine body true ?_ ?_
            · rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]
            · rw [deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_clause_leaf
