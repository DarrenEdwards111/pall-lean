import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerBounded

/-!
# Tight switching, step 58: one collapse round preserves the bottom width (branch `razborov-recoverRho-wip`)

The glue composing the switch (step 57) and the merge (step 56): `collapseRound F ρ C = mergePass (leafCollapse
F ρ C)`, so if `ρ` shallows every bottom gate of `C` below `s`, the leaf-switch makes the new bottoms
`BottomWidth s` (step 57) and the merge preserves it (step 56).  With `s ≤ w` (`BottomWidth_mono`) the round
keeps the uniform width budget `w` — the width invariant the recursive tower threads.

* `BottomWidth_mono` — widening the budget weakens `BottomWidth`.
* `collapseRound_BottomWidth` — `Shallows F ρ s C ⟹ BottomWidth s (collapseRound F ρ C)`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- `BottomWidth` is monotone: a wider budget is weaker. -/
theorem BottomWidth_mono {w w' : ℕ} (h : w ≤ w') {C : Layered n} (hbw : BottomWidth w C) :
    BottomWidth w' C :=
  fun cs hcs T hT => le_trans (hbw cs hcs T hT) h

/-- **One collapse round preserves the bottom width.**  If `ρ` shallows every bottom gate of `C` below `s`,
the round output `collapseRound F ρ C` is `BottomWidth s` (switch sets it, step 57; merge keeps it, step 56). -/
theorem collapseRound_BottomWidth (F : ℕ) (ρ : Fin n → Option Bool) {s : ℕ} {C : Layered n}
    (hsh : Shallows F ρ s C) : BottomWidth s (collapseRound F ρ C) := by
  show BottomWidth s (mergePass (leafCollapse F ρ C))
  exact mergePass_BottomWidth (leafCollapse_tower_BottomWidth F ρ hsh)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.collapseRound_BottomWidth
