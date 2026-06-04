import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestLeafActive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyConfine

/-!
# Selected variables live in leaf-readable clauses

The capstone of the general structural picture (and the lemma deferred earlier with a `sorry`, now
fully proved): **every selected variable lies in a clause that is either falsified at the leaf or is
the leaf's active clause** — both readable directly from the end-state.

The proof is a direct induction using the step layer `deepestEnd_succ`: the head variable's clause `T`
is the step's active clause, and at the leaf it is either falsified (left) or — having survived —
still active (`activeTerm_deepestEnd_of_not_falsified`, right); the tail is the induction hypothesis
on the first-step successor (whose leaf is the same leaf).

* `deepestSel_mem_leaf_clause` — the identification.

So under "the leaf is unsatisfied", the decoder's relevant clauses are exactly the leaf-falsified
clauses plus the single leaf-active clause — a finite, end-state-readable family.  (The remaining open
core is sequencing the satisfy positions within each clause's block; not faked.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Selected variables live in leaf-readable clauses.**  If the leaf is unsatisfied, every
`v ∈ deepestSel cs F σ` lies in `clauseVars C` for a clause `C` that is either falsified at the leaf
or is the leaf's active clause. -/
theorem deepestSel_mem_leaf_clause (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) {v : Fin n}, v ∈ deepestSel cs F σ →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      ∃ C, v ∈ clauseVars C ∧
        (SwitchingCounting.termFalsified (deepestEnd cs F σ) C = true ∨
          SwitchingCounting.activeTerm cs (deepestEnd cs F σ) = some C) := by
  intro F
  induction F with
  | zero => intro σ v hv _; rw [deepestSel] at hv; exact absurd hv (by simp)
  | succ F ih =>
    intro σ v hv hsat
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSel] at hv; simp only [hany, if_true] at hv; exact absurd hv (by simp)
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSel] at hv
        simp only [hany, Bool.false_eq_true, if_false, hact] at hv; exact absurd hv (by simp)
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSel] at hv
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hv; exact absurd hv (by simp)
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp (List.mem_of_mem_head? hh)).1
          -- a body covering both depth-branches, given the step decomposition
          have body : ∀ b : Bool,
              deepestEnd cs (F + 1) σ = deepestEnd cs F (fixVar σ (litVar ℓ) b) →
              deepestSel cs (F + 1) σ = insert (litVar ℓ) (deepestSel cs F (fixVar σ (litVar ℓ) b)) →
              ∃ C, v ∈ clauseVars C ∧
                (SwitchingCounting.termFalsified (deepestEnd cs (F + 1) σ) C = true ∨
                  SwitchingCounting.activeTerm cs (deepestEnd cs (F + 1) σ) = some C) := by
            intro b hEnd hSel
            rw [hEnd] at hsat ⊢
            rw [hSel, Finset.mem_insert] at hv
            rcases hv with hvl | hvr
            · -- head: `v = litVar ℓ`, clause `T`
              by_cases hTf :
                  SwitchingCounting.termFalsified (deepestEnd cs F (fixVar σ (litVar ℓ) b)) T = true
              · exact ⟨T, by rw [hvl]; exact mem_clauseVars hℓT, Or.inl hTf⟩
              · rw [Bool.not_eq_true] at hTf
                have hns_b : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false :=
                  anyTermSat_of_deepestEnd_false cs F _ hsat
                have hnf_b : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T = false := by
                  by_contra hc
                  rw [Bool.not_eq_false] at hc
                  have hp := termFalsified_deepestEnd cs F (fixVar σ (litVar ℓ) b) T hc
                  rw [hp] at hTf; exact absurd hTf (by simp)
                have hfree_b : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length := by
                  by_contra hc0
                  rw [Nat.not_lt, Nat.le_zero, List.length_eq_zero_iff] at hc0
                  have hsatC : SwitchingCounting.termSat (fixVar σ (litVar ℓ) b) T = false := by
                    by_contra hs
                    rw [Bool.not_eq_false] at hs
                    have : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = true := by
                      rw [SwitchingCounting.anyTermSat, List.any_eq_true]
                      exact ⟨T, SwitchingCounting.activeTerm_mem hact, hs⟩
                    rw [hns_b] at this; exact absurd this (by simp)
                  have hff := SwitchingCounting.term_falsified_of_not_sat_no_free hsatC hc0
                  rw [hff] at hnf_b; exact absurd hnf_b (by simp)
                have hactτ : SwitchingCounting.activeTerm cs (fixVar σ (litVar ℓ) b) = some T :=
                  activeTerm_fixVar_stable hact hfree hns_b hnf_b hfree_b
                exact ⟨T, by rw [hvl]; exact mem_clauseVars hℓT,
                  Or.inr (activeTerm_deepestEnd_of_not_falsified cs F (fixVar σ (litVar ℓ) b) T
                    hactτ hsat hTf)⟩
            · -- tail: induction hypothesis on the first-step successor
              exact ih (fixVar σ (litVar ℓ) b) hvr hsat
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · refine body false ?_ ?_
            · rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
            · rw [deepestSel]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_pos hd]
          · refine body true ?_ ?_
            · rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]
            · rw [deepestSel]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rw [if_neg hd]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_mem_leaf_clause
