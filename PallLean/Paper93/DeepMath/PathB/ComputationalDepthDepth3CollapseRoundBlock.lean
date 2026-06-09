import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafCollapseBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergePass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseMergeRound

/-!
# Block-DT model, route-2 step [169b]: the block per-round collapse (switch + merge)

The block twin of `collapseRound`: switch every bottom gate via the block tree (`leafCollapseBlock`,
[169a]), then merge the same-type siblings the switch creates (`mergePass`, reused — it is
tree-agnostic).  `EquivOn` to the original tower, needing only `stars ρ < F` (block fuel).

* `collapseRoundBlock w F ρ C := mergePass (leafCollapseBlock w F ρ C)`.
* `collapseRoundBlock_EquivOn` — `EquivOn ρ C (collapseRoundBlock w F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- One block depth-reducing round: switch every bottom gate via the block tree, then merge. -/
def collapseRoundBlock (w F : ℕ) (ρ : Fin n → Option Bool) (C : Layered n) : Layered n :=
  mergePass (leafCollapseBlock w F ρ C)

/-- **The block per-round collapse is subcube-equivalent to the original tower** (`stars ρ < F`). -/
theorem collapseRoundBlock_EquivOn (w F : ℕ) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ < F) (C : Layered n) :
    EquivOn ρ C (collapseRoundBlock w F ρ C) :=
  EquivOn.trans (leafCollapseBlock_EquivOn w F hstars C)
    (mergePass_EquivOn ρ (leafCollapseBlock w F ρ C))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRoundBlock_EquivOn
