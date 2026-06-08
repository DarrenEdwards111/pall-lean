import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeSwap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore

/-!
# Tight switching, step 3: the `BoolDecisionTree ↔ DTree` type bridge (branch `razborov-recoverRho-wip`)

The two arcs use two structurally **identical** decision-tree types:
* `BoolDecisionTree` (`leaf`/`query`) — carries the tight `(2w)^s` count (`canonicalDT`, the single-literal
  tree);
* `DTree` (`leaf`/`node`) — carries the collapse machinery (`canonicalDTree`, `dtreeToCNF`, …, the block
  tree).

Their constructors, `eval`, and `depth` coincide verbatim (`query i low high` ↦ `node i lo hi`, both
`if x i then high else low`, both `max + 1`).  This file makes the identification explicit: a conversion
`toDTree` preserving `eval` and `depth` exactly.  This unifies the *types* the tight count and the collapse
live in — the prerequisite for moving the collapse onto `toDTree (canonicalDT …)`, where the tight cap
(`tight_descent_switching_prob`) applies directly.

* `toDTree` — `BoolDecisionTree n → DTree n`.
* `toDTree_eval` / `toDTree_depth` — it preserves evaluation and depth.

## Honest scope

This bridges the two *type* representations; it does **not** identify the two *algorithms* `canonicalDT`
(single-literal, re-checks after each query) and `canonicalDTree` (whole-block `queryAll`), whose depths
genuinely differ (the block tree never stops mid-term).  Closing the depth-3 vacuity with the tight cap
still needs the collapse re-expressed over `toDTree (canonicalDT …)` (or the block tree's own tight count);
the type bridge is the first, clean step of that port.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

variable {n : ℕ}

/-- Convert a `BoolDecisionTree` to the structurally-identical `DTree`. -/
def toDTree : BoolDecisionTree n → DTree n
  | BoolDecisionTree.leaf b => DTree.leaf b
  | BoolDecisionTree.query i lo hi => DTree.node i (toDTree lo) (toDTree hi)

/-- **The conversion preserves evaluation.** -/
theorem toDTree_eval (t : BoolDecisionTree n) (x : Fin n → Bool) :
    (toDTree t).eval x = t.eval x := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
    simp only [toDTree, DTree.eval, BoolDecisionTree.eval, ihlo, ihhi]

/-- **The conversion preserves depth.** -/
theorem toDTree_depth (t : BoolDecisionTree n) : (toDTree t).depth = t.depth := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
    simp only [toDTree, DTree.depth, BoolDecisionTree.depth, ihlo, ihhi]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.toDTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.toDTree_depth
