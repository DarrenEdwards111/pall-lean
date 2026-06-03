import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ForwardScan

/-!
# Forward-scan invariant: path-level persistence to the end-state

The per-step monotonicity `termFalsified_fixVar_of_free` (a falsified clause survives any step on a
free variable) lifts to the whole deepest branch: a clause falsified at `σ` stays falsified at the
**end-state** `deepestEnd cs fuel σ`.  So the falsified frontier built up along the path persists to
the leaf — the forward scan's ordering is consistent all the way to the end-state, where the decoder
reads it.

* `termFalsified_deepestEnd` — `termFalsified σ C → termFalsified (deepestEnd cs fuel σ) C`.
* `termFalsified_deepestEnd_iff_aux` — packaged: the clauses already falsified at `σ` are a subset of
  those falsified at the end-state.

This is the persistence half of the forward-scan invariant.  The remaining open content (the
*satisfied* clause's path-variables, which carry no false literal and need the `(2w)^s` label) is
unchanged and not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Path-level persistence.**  A clause falsified at `σ` stays falsified at the deepest-branch
end-state `deepestEnd cs fuel σ`: each step fixes a free variable, so `termFalsified_fixVar_of_free`
applies all the way down. -/
theorem termFalsified_deepestEnd (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool) (C : Clause n),
      SwitchingCounting.termFalsified σ C = true →
      SwitchingCounting.termFalsified (deepestEnd cs fuel σ) C = true := by
  intro fuel
  induction fuel with
  | zero => intro σ C h; exact h
  | succ fuel ih =>
    intro σ C h
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestEnd]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact h
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          rw [deepestEnd]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · exact ih _ _ (termFalsified_fixVar_of_free h hfree)
          · exact ih _ _ (termFalsified_fixVar_of_free h hfree)

/-- The clauses falsified at `σ` are still falsified at the deepest end-state. -/
theorem termFalsified_subset_deepestEnd (cs : List (Clause n)) (fuel : ℕ)
    (σ : Fin n → Option Bool) {C : Clause n} (h : SwitchingCounting.termFalsified σ C = true) :
    SwitchingCounting.termFalsified (deepestEnd cs fuel σ) C = true :=
  termFalsified_deepestEnd cs fuel σ C h

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_deepestEnd
