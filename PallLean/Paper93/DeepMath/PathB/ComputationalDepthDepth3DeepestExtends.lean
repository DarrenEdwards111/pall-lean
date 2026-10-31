import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BlockDescent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreeLitPos
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# Tight switching, step 78: the deepest leaf extends the restriction (branch `razborov-recoverRho-wip`)

The relative switching budget (`tight_descent_switching_prob_witness` with `Short := extBox τ`) needs
`deepestEnd cs F σ ∈ extBox τ` for `σ` extending `τ` — i.e. the canonical deepest leaf is itself an extension
of `σ`.  `deepestEnd` only ever recurses by `fixVar`-ing a *free* literal of the active term, so it adds
fixings and never overwrites — hence `Extends σ (deepestEnd cs F σ)`.

* `fixVar_extends_of_free` — fixing a free variable extends the restriction.
* `deepestEnd_extends` — the deepest leaf extends the restriction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Fixing a *free* variable extends the restriction. -/
theorem fixVar_extends_of_free {σ : Fin n → Option Bool} {v : Fin n} {b : Bool}
    (hfree : σ v = none) : Extends σ (fixVar σ v b) := by
  intro w c hw
  by_cases hwv : w = v
  · subst hwv; rw [hfree] at hw; simp at hw
  · rw [fixVar, Function.update_of_ne hwv]; exact hw

/-- **The deepest leaf extends the restriction.**  `deepestEnd cs F σ` only fixes free variables, so it
extends `σ`. -/
theorem deepestEnd_extends (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool), Extends σ (deepestEnd cs fuel σ) := by
  intro fuel
  induction fuel with
  | zero => intro σ; rw [deepestEnd]; exact fun _ _ h => h
  | succ fuel ih =>
    intro σ
    rw [deepestEnd]
    split
    · exact fun _ _ h => h
    · split
      · exact fun _ _ h => h
      · split
        · exact fun _ _ h => h
        · next heq =>
          have hmem := List.mem_of_mem_head? heq
          simp only [SwitchingCounting.freeLits, List.mem_filter] at hmem
          have hlf := hmem.2
          rw [litFree_var] at hlf
          have hfree := Option.isNone_iff_eq_none.mp hlf
          split <;> exact Extends_trans (fixVar_extends_of_free hfree) (ih _)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_extends
