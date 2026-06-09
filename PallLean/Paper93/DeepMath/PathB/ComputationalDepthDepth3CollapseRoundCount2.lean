import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeCountMul
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount

/-!
# Tight switching, step 98: a collapse round bounds the per-gate clause-count by `M·2^t` (branch `razborov-recoverRho-wip`)

The clause-count companion of `collapseRound_count_le` (step 90).  A collapse round at depth threshold `t`
leaves every bottom gate with `≤ M·2^t` clauses: the leaf-switch makes each new bottom gate have `≤ 2^t`
clauses (`leafCollapse_tower_BottomCount`, step 93), and the merge multiplies by the gate count `≤ M`
(`mergePass_count_mul`, step 94; the leaf-switch preserves the gate count and the non-empty shape).  With `t`
the *small* depth threshold (step 95), `M·2^t` is a *constant* — so the per-gate clause-count is uniformly
bounded and the rate is constant.

* `collapseRound_BottomCount` — `BottomCount (M·2^t) (collapseRound F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **A collapse round bounds the per-gate clause-count by `M·2^t`.**  Given non-empty gates, the survivor
shallowness at depth `t`, and the gate count `≤ M`, the round output has every bottom gate with `≤ M·2^t`
clauses. -/
theorem collapseRound_BottomCount (F : ℕ) (ρ : Fin n → Option Bool) {t M : ℕ} {C : Layered n}
    (hM1 : 1 ≤ M) (hC : NonEmptyGates C) (hsh : Shallows F ρ t C)
    (hcnt : (bottomGates C).length ≤ M) :
    BottomCount (M * 2 ^ t) (collapseRound F ρ C) := by
  show BottomCount (M * 2 ^ t) (mergePass (leafCollapse F ρ C))
  refine mergePass_count_mul hM1 (leafCollapse_NonEmptyGates F ρ hC) ?_
    (leafCollapse_tower_BottomCount F ρ hsh)
  rw [leafCollapse_bottomGates_length]; exact hcnt

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_BottomCount
