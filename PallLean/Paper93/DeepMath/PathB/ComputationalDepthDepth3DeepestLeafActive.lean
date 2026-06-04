import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestStep

/-!
# Leaf active-clause identification: a surviving active clause stays active to the leaf

Using the step infrastructure (`deepestEnd_succ`), we prove the forward result the general decoder
needs and that was previously out of reach: **if the active clause at `σ` is not falsified at the
leaf (and the leaf is unsatisfied), it is still the active clause at the leaf.**

This is a *strict generalization* of the pure-satisfy stability `activeTerm_deepestEnd_pure_satisfy`:
it needs neither `CleanClause` nor "no falsify step" — only that the clause *survives* (is not
falsified) to the leaf.  The mechanism: the deepest branch only ever acts on the active clause, so the
first step either advances within it (and the clause survives) or falsifies it (and then it would be
falsified at the leaf, contradicting survival).  Survival therefore forces every step to advance, and
`activeTerm_advance_stable` carries the clause forward, one `deepestEnd_succ` step at a time.

* `activeTerm_deepestEnd_of_not_falsified` — the identification.

So the leaf's active clause (when the leaf is unsatisfied) is exactly the surviving start clause; for a
general branch this pins the *final* block's clause.  The remaining open core is sequencing the
satisfy positions across the falsify steps; not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A surviving active clause stays active to the leaf.**  If `C` is active under `σ`, the leaf is
unsatisfied, and `C` is not falsified at the leaf, then `C` is the active clause at the leaf.  No
`CleanClause` / "no falsify step" hypotheses — survival to the leaf does the work. -/
theorem activeTerm_deepestEnd_of_not_falsified (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (C : Clause n),
      SwitchingCounting.activeTerm cs σ = some C →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      SwitchingCounting.termFalsified (deepestEnd cs F σ) C = false →
      SwitchingCounting.activeTerm cs (deepestEnd cs F σ) = some C := by
  intro F
  induction F with
  | zero => intro σ C hact _ _; rw [deepestEnd]; exact hact
  | succ F ih =>
    intro σ C hact hsat hnf
    have hns : SwitchingCounting.anyTermSat cs σ = false :=
      SwitchingCounting.activeTerm_anyTermSat_false hact
    obtain ⟨_, hTfree⟩ := SwitchingCounting.activeTerm_pred hact
    obtain ⟨ℓ, hℓhead⟩ : ∃ ℓ, (SwitchingCounting.freeLits σ C).head? = some ℓ := by
      cases hfl : SwitchingCounting.freeLits σ C with
      | nil => rw [hfl] at hTfree; simp at hTfree
      | cons a _ => exact ⟨a, rfl⟩
    have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
      unfold SwitchingCounting.activeTermLit; rw [hact]; exact hℓhead
    have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
    obtain ⟨b, hb⟩ : ∃ b, deepestStep cs F σ = fixVar σ (litVar ℓ) b := by
      rw [deepestStep_active cs F σ C hns hact hℓhead]
      split
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    rw [deepestEnd_succ, hb] at hsat hnf ⊢
    have hns_b : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false :=
      anyTermSat_of_deepestEnd_false cs F _ hsat
    have hnf_b : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) C = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have hp := termFalsified_deepestEnd cs F (fixVar σ (litVar ℓ) b) C hc
      rw [hp] at hnf; exact absurd hnf (by simp)
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
    exact ih (fixVar σ (litVar ℓ) b) C
      (activeTerm_fixVar_stable hact hfree hns_b hnf_b hfree_b) hsat hnf

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_deepestEnd_of_not_falsified
