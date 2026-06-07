import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfy

/-!
# A foothold into `recoverStream`: bad ρ is live everywhere, first active clause = `cs.head?`

`recoverStream` (the genuine Razborov reconstruction) must recover the active-clause stream from the
leaf, and the obstruction is a circularity: at a general step the active clause depends on the running
state, which mixes ρ-fixed and queried variables that the leaf cannot separate.

This file proves the **first step is circularity-free**.  A bad restriction ρ (falsifies nothing,
`hnf`; leaf unsatisfied, `hleaf`) is *live everywhere*: it neither falsifies nor satisfies any clause
(`bad_live_everywhere`).  A live clause has a free literal (`has_free_of_live`), so **every** clause
passes the active predicate at ρ, and therefore the very first active clause is just the first clause of
`cs` (`activeTerm_eq_head_of_bad`) — recoverable with no reference to the leaf at all.

So the base of `recoverStream` is settled.  The recursion (the *next* active clause, after the queries
have changed the state) is where the running-state circularity bites and the canonical-tree-walk
reconstruction is needed — that remains the switching-lemma core.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A clause that is neither falsified nor satisfied has a free literal (else, fully assigned and
unsatisfied, it would be falsified). -/
theorem has_free_of_live {ρ : Restriction n} {T : Clause n}
    (hf : SwitchingCounting.termFalsified ρ T = false) (hs : SwitchingCounting.termSat ρ T = false) :
    SwitchingCounting.freeLits ρ T ≠ [] := by
  intro h
  have ht := SwitchingCounting.term_falsified_of_not_sat_no_free hs h
  rw [hf] at ht
  exact absurd ht (by simp)

/-- **A bad restriction is live everywhere.**  If ρ falsifies nothing and the deepest leaf is
unsatisfied, then ρ neither falsifies nor satisfies any clause. -/
theorem bad_live_everywhere {cs : List (Clause n)} {F : ℕ} {ρ : Restriction n}
    (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false ∧ SwitchingCounting.termSat ρ T = false := by
  have hns : SwitchingCounting.anyTermSat cs ρ = false :=
    anyTermSat_of_deepestEnd_false cs F ρ hleaf
  intro T hT
  refine ⟨hnf T hT, ?_⟩
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have hsat : SwitchingCounting.anyTermSat cs ρ = true := by
    rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨T, hT, hc⟩
  rw [hns] at hsat; exact absurd hsat (by simp)

/-- **The first active clause is recoverable with no leaf reference.**  For a bad ρ — live everywhere —
every clause passes the active predicate, so the active clause is simply the head of `cs`. -/
theorem activeTerm_eq_head_of_bad {cs : List (Clause n)} {F : ℕ} {ρ : Restriction n}
    (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    SwitchingCounting.activeTerm cs ρ = cs.head? := by
  have hns : SwitchingCounting.anyTermSat cs ρ = false :=
    anyTermSat_of_deepestEnd_false cs F ρ hleaf
  have hlive := bad_live_everywhere hnf hleaf
  rw [SwitchingCounting.activeTerm_eq_find hns]
  cases cs with
  | nil => rfl
  | cons C rest =>
    have hC := hlive C List.mem_cons_self
    have hpred : (!SwitchingCounting.termFalsified ρ C
        && decide (0 < (SwitchingCounting.freeLits ρ C).length)) = true := by
      rw [hC.1]
      simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq]
      exact List.length_pos_iff_ne_nil.mpr (has_free_of_live hC.1 hC.2)
    rw [List.find?_cons]
    simp [hpred]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.bad_live_everywhere
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_eq_head_of_bad
