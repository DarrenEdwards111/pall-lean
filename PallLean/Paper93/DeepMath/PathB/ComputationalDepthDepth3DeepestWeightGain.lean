import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WeightGain
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarShell

/-!
# Tight switching, step 1: the `deepestEnd` weight gain (branch `razborov-recoverRho-wip`)

The bridge piece for porting the **tight `(2w)^s` count** (`fullpath_switching_count`, a clean
*cardinality* bound over the `canonicalDT` reconstruction) into the **p-biased** weighted setting that the
collapse uses.  The crude weighted bound (`descent_switching_prob`) gains a factor `(2p/(1-p))^s` by moving
`σ` to its satisfying boundary `descentSat σ`; the tight route instead moves `σ` to the *deepest-branch*
leaf `deepestEnd cs F σ`, whose star count drops by exactly the canonical-tree depth
(`stars_deepestEnd_add_depth`).  On the deep event (`depth ≥ s`) that drop is `≥ s`, so the same
`pweight_le_ratio_pow` gain applies.

* `pweight_le_ratio_pow_deepestEnd` — `pweight σ ≤ (2p/(1-p))^s · pweight (deepestEnd cs F σ)` whenever the
  canonical tree of `σ` has depth `≥ s`.

This is the weight half of a *tight* weighted switching bound; combined with a weighted form of the
deepest-branch reconstruction (the `(2w)^s` label half) it would replace `(4^w+1)^F` by `(2w)^s` in the
p-biased bound — the fix for the depth-3 vacuity (`depth3_budgets_unsatisfiable`).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The `deepestEnd` weight gain.**  Moving `σ` to its deepest-branch leaf gains the factor
`(2p/(1-p))^s` once the canonical tree has depth `≥ s` (the leaf fixes `depth ≥ s` of `σ`'s stars). -/
theorem pweight_le_ratio_pow_deepestEnd {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (F s : ℕ) (σ : Fin n → Option Bool)
    (hdepth : s ≤ (canonicalDT cs F σ).depth) :
    pweight p σ ≤ (2 * p / (1 - p)) ^ s * pweight p (deepestEnd cs F σ) := by
  have hadd := stars_deepestEnd_add_depth cs F σ
  exact pweight_le_ratio_pow hp0 hp3 (by omega) (by omega)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_le_ratio_pow_deepestEnd
