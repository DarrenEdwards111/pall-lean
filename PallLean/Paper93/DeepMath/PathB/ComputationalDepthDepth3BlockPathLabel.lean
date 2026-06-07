import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Block-DT model, foundation 10a: the compact in-clause label type (branch only)

The tight switching count needs a **compact** label: per block, only the *in-clause positions* (`< w`)
of the block variables — not a global-variable mask.  This is the block analogue of the depth-3
`PathLabel`.

* `BlockPathLabel w s := Fin s → Finset (Fin w)` — per block, a subset of the `w` literal positions.
* `card_blockPathLabel` — `|BlockPathLabel w s| = (2^w)^s` (the canonical switching base, **no** `|cs|`).

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- A compact stars-pattern: per block, the subset of literal positions (`< w`) that were block
variables. -/
abbrev BlockPathLabel (w s : ℕ) : Type := Fin s → Finset (Fin w)

/-- **The label space has size `(2^w)^s`** — the canonical switching base, with no `|cs|` factor. -/
theorem card_blockPathLabel (w s : ℕ) :
    Fintype.card (BlockPathLabel w s) = (2 ^ w) ^ s := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.card_blockPathLabel
