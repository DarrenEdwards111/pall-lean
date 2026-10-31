import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergePass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseMergeRound

/-!
# Tight switching, step 47: the per-round collapse (switch + merge) (branch `razborov-recoverRho-wip`)

The complete per-round collapse at any depth, as a single `EquivOn`: switch every bottom gate
(`leafCollapse`, step 45) then merge the same-type siblings the switch creates (`mergePass`, step 46).  For an
alternating tower this reduces depth by one and stays `EquivOn` to the original, needing only `stars ρ ≤ F`.

* `collapseRound F ρ C := mergePass (leafCollapse F ρ C)` — one depth-reducing round.
* `collapseRound_EquivOn` — `EquivOn ρ C (collapseRound F ρ C)` (via `EquivOn.trans` of the switch and the
  merge), unconditional in shallowness.

This is the per-round transformation the recursive-tower oracle (step 43) applies: pick `ρ` extending the
running subcube with survivors (`exists_survivor_shallow_extends_uncond`, step 36), then `collapseRound`.  The
remaining bookkeeping is purely combinatorial: a `Valid` predicate tracking that `d` rounds drive the tower
to a bottom `DNF` (depth `2`), which the merge guarantees one level per round on an alternating tower.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- One depth-reducing round: switch every bottom gate, then merge the same-type siblings created. -/
def collapseRound (F : ℕ) (ρ : Fin n → Option Bool) (C : Layered n) : Layered n :=
  mergePass (leafCollapse F ρ C)

/-- **The per-round collapse is subcube-equivalent to the original tower** (only `stars ρ ≤ F` needed). -/
theorem collapseRound_EquivOn (F : ℕ) {ρ : Fin n → Option Bool}
    (hstars : SwitchingCounting.stars ρ ≤ F) (C : Layered n) :
    EquivOn ρ C (collapseRound F ρ C) :=
  EquivOn.trans (leafCollapse_EquivOn F hstars C) (mergePass_EquivOn ρ (leafCollapse F ρ C))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_EquivOn
