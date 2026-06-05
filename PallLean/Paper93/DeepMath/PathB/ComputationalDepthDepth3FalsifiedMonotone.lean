import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatisfyStepRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifyAdvance

/-!
# Global clause-order invariant: falsified clauses stay falsified through the whole branch

The per-step clause-order facts — advance keeps the active term live
(`activeTerm_advance_stable`), a falsify step moves strictly past it
(`activeTerm_falsify_advances`) — rest on a single monotonicity backbone:
`termFalsified_fixVar_of_free` (fixing a free variable cannot revive a falsified term).  This file
lifts that from one step to the **whole deepest branch**, the global invariant the threading needs.

* `termFalsified_deepestStep_stable` — one deepest step preserves falsification.
* `termFalsified_deepestEnd_stable` — **a clause falsified at `σ` is falsified at the full deepest
  end-state** `deepestEnd cs F σ` (induction over the branch).
* `prefix_falsified_through_branch` — consequently every clause *before* the first active term `T`
  stays falsified all the way to the leaf.

So the active clause never returns to an earlier clause: across the entire branch the falsified
prefix only grows, and the active clause sweeps `cs` strictly forward — the global no-backtrack
invariant, now a theorem rather than a per-step observation.

## What remains (honest)

This is the global form of the clause-order half.  The remaining open core is still the *threading*:
assembling value recovery (`litTrue_deepestEnd_of_satisfy_step`) and this monotone clause sweep into a
decoder recovering the selected-variable sequence from `(deepestEnd, label)`.  That assembly — a
reverse induction identifying, at each step, the active clause from the end-state via this
monotonicity plus the label position — is **not** faked here.  AC⁰/depth-3; `Depth3CollapseModel.collapse`
and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **One deepest step preserves falsification.**  Each step either leaves `σ` unchanged (stuck) or
fixes the active literal's *free* variable; either way a falsified term stays falsified
(`termFalsified_fixVar_of_free`). -/
theorem termFalsified_deepestStep_stable (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (T : Clause n) (h : SwitchingCounting.termFalsified σ T = true) :
    SwitchingCounting.termFalsified (deepestStep cs F σ) T = true := by
  cases hany : SwitchingCounting.anyTermSat cs σ with
  | true => rw [deepestStep]; simp only [hany, if_true]; exact h
  | false =>
    cases hact : SwitchingCounting.activeTerm cs σ with
    | none =>
      rw [deepestStep]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
    | some T' =>
      cases hh : (SwitchingCounting.freeLits σ T').head? with
      | none =>
        rw [deepestStep]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact h
      | some ℓ =>
        have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
          unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
        have hv : σ (litVar ℓ) = none := activeTermLit_var_free hatl
        rw [deepestStep_active cs F σ T' hany hact hh]
        split <;> exact termFalsified_fixVar_of_free h hv

/-- **A falsified clause stays falsified through the whole branch.**  If `T` is falsified at `σ`, it
is falsified at the full deepest end-state `deepestEnd cs F σ` — by induction over the branch using
single-step stability. -/
theorem termFalsified_deepestEnd_stable (cs : List (Clause n)) (T : Clause n) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      SwitchingCounting.termFalsified σ T = true →
      SwitchingCounting.termFalsified (deepestEnd cs F σ) T = true := by
  intro F
  induction F with
  | zero => intro σ h; rw [deepestEnd]; exact h
  | succ F ih =>
    intro σ h
    rw [deepestEnd_succ]
    exact ih _ (termFalsified_deepestStep_stable cs F σ T h)

/-- **The active clause never backtracks across the whole branch.**  Every clause before the first
active term `T` (in `cs`) is falsified at `σ` (`activeTerm_prefix_falsified`) and therefore stays
falsified at the full deepest end-state.  So the falsified prefix only grows and the active clause
sweeps `cs` strictly forward. -/
theorem prefix_falsified_through_branch (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    {T : Clause n} (hact : SwitchingCounting.activeTerm cs σ = some T) :
    ∃ pre post, cs = pre ++ T :: post ∧
      ∀ C' ∈ pre, SwitchingCounting.termFalsified (deepestEnd cs F σ) C' = true := by
  obtain ⟨pre, post, hcs, hpre⟩ := SwitchingCounting.activeTerm_prefix_falsified hact
  exact ⟨pre, post, hcs, fun C' hC' => termFalsified_deepestEnd_stable cs C' F σ (hpre C' hC')⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_deepestStep_stable
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_deepestEnd_stable
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.prefix_falsified_through_branch
