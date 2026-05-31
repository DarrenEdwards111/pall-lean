import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# The tight path label `(2w)^s` (replacing the loose full-structure label)

**STATUS: REAL.  THE TIGHT LABEL TYPE + COUNT; THE ENCODING INJECTION IS NEXT.**

The loose `circuitLabelSpace` recorded the whole circuit traversal and was
exponential in circuit *size* — too weak for the switching gate.  The switching
savings live in recording **only the recoverable path**: at each of the `≤ s`
queried coordinates, store just

* which literal of the *active* (bottom width `≤ w`) clause was queried — `≤ w`
  choices, and
* a sign/value bit — `2` choices,

so each step has `≤ 2w` possibilities, and a length-`s` path has `≤ (2w)^s`
labels.  This file fixes that tight label type and proves the count:

  `card_pathLabels : |PathLabel w s| = (2w)^s`.

Combined with the proved `binom_layer_ratio` and the star-layer counts, this is
the label factor that lets the `t`-star layer outnumber `(t-s)`-star × labels in
the Håstad regime `w < 1/(2p)`.  The remaining work is the **encoding injection**:
the canonical path of a bad restriction maps injectively into `PathLabel w s` — to
be wired against `card_bad_le_of_label_bound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- One canonical-path step: which literal of the active width-`≤w` clause was
queried (`Fin w`) and its sign/value bit (`Bool`).  At most `2w` possibilities. -/
abbrev PathStepLabel (w : ℕ) : Type := Fin w × Bool

/-- A canonical-path label of length `s`: one step-label per queried coordinate.
Records **only** the path, not the whole circuit. -/
abbrev PathLabel (w s : ℕ) : Type := Fin s → PathStepLabel w

/-- Each path step has exactly `2w` possible labels. -/
theorem card_pathStepLabel (w : ℕ) : Fintype.card (PathStepLabel w) = 2 * w := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]

/-- **The tight label count:** a length-`s` path has exactly `(2w)^s` labels — the
switching savings, recording only the path rather than the whole circuit. -/
theorem card_pathLabels (w s : ℕ) : Fintype.card (PathLabel w s) = (2 * w) ^ s := by
  rw [Fintype.card_fun, card_pathStepLabel, Fintype.card_fin]

/-- The label-count bound in the form the switching count consumes. -/
theorem card_pathLabels_le (w s : ℕ) : Fintype.card (PathLabel w s) ≤ (2 * w) ^ s :=
  le_of_eq (card_pathLabels w s)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_pathLabels
