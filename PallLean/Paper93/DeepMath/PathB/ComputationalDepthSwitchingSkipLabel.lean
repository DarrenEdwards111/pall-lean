import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive

/-!
# Tight switching, skip-encoded decoder step 1: the `m`-free skip-augmented label (branch `razborov-recoverRho-wip`)

The witness-augmented label `WitLabel w s m = Fin s → (Fin w × Bool × Fin m)` (step 24) records, per step,
the *active-clause index* `Fin m`, giving the count `(2·w·m)^s`.  That `m` (clause-count) is the binding
looseness: fed into the per-gate switching rate it forces the restriction probability `p ≈ 1/m`, which blows
the multi-round survivor size past `n` — so the assembled depth-`(d+2)` parity bound is numerically vacuous
for `d ≥ 1`.  The `(2·w)^s` *conditional* tight count (`card_bad_le_pathlabel`,
`reconstructionCorrect_fullpath`) drops the `m`, but only under `hnf`/`hleaf`/`hpos` (the "empty-skip wall" —
no clause falsified, no term satisfied at the deepest end), which fail on the general survivor shells.

Håstad's actual decoder recovers the active clause from the **canonical order** of the live clauses — *not*
from a recorded index — and handles the skip over dead/satisfied clauses with an **O(1) marker per step**, not
a `log m`-bit index.  This file is the first brick of that decoder: the `m`-free skip-augmented label space.

The augmented step is the path step `Fin w × Bool` plus a single **advance bit** `Bool`:

```
  SkipStepLabel w := Fin w × Bool × Bool,     |SkipStepLabel w| = 4·w,
  SkipLabel w s   := Fin s → SkipStepLabel w,  |SkipLabel w s|   = (4·w)^s.
```

The advance bit is the replacement for the `Fin m` clause index: it tells the decoder, at each step, whether
the current active clause is *exhausted* (advance to the next live clause, located by re-scanning in canonical
order) or still live (stay).  Because the next active clause is *recovered* by the canonical scan rather than
*recorded*, the count is `(4·w)^s` — **independent of the clause count `m`** (and of the fuel `F`).  Crucially
`(4·w)^s` is still the `(O(w))^s` shape: fed into the switching rate it gives `p = O(1/w)`, a constant for
constant-width AC⁰ bottom gates, so the multi-round survivor size stays `O(w)^{(d+1)}` and the parity regime
closes for all `d`.

* `SkipStepLabel`, `SkipLabel` — the `m`-free skip-augmented label space.
* `card_skipStepLabel`, `card_skipLabels`, `card_skipLabels_le` — `|SkipLabel w s| = (4·w)^s`, `m`- and
  `F`-independent.

## Honest scope

This is **only** the label space and its cardinality — the `m`-free target the unconditional decoder must
inject into.  The skip-aware encoder (recording the advance bit at each clause boundary), the canonical-order
recovery of the active clause (dropping `hnf`/`hleaf`/`hpos`), and the resulting unconditional `(4·w)^s`
descent bound are the subsequent bricks of this sub-arc.  Nothing here yet discharges the empty-skip wall; it
fixes the label space against which that work is measured.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- One skip-augmented step: the path step `(Fin w × Bool)` plus a single **advance bit** `Bool` (does the
current active clause exhaust at this step, so the decoder scans to the next live clause in canonical order).
The advance bit is the `m`-free replacement for `WitStepLabel`'s `Fin m` clause index. -/
abbrev SkipStepLabel (w : ℕ) : Type := Fin w × Bool × Bool

/-- A skip-augmented label of length `s`: a path step plus an advance bit per step.  The label space the
unconditional (`hnf`/`hleaf`/`hpos`-free) decoder injects the bad set into. -/
abbrev SkipLabel (w s : ℕ) : Type := Fin s → SkipStepLabel w

/-- Each skip-augmented step has `4 · w` possibilities (`w` positions × `2` values × `2` advance bits). -/
theorem card_skipStepLabel (w : ℕ) : Fintype.card (SkipStepLabel w) = 4 * w := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **The skip-augmented label count is `m`- and `F`-independent:** `(4·w)^s`, the `(O(w))^s` shape with the
advance bit in place of the `Fin m` clause index — no clause-count factor at all. -/
theorem card_skipLabels (w s : ℕ) : Fintype.card (SkipLabel w s) = (4 * w) ^ s := by
  rw [Fintype.card_fun, card_skipStepLabel, Fintype.card_fin]

/-- The skip-label bound in the form the switching count consumes. -/
theorem card_skipLabels_le (w s : ℕ) : Fintype.card (SkipLabel w s) ≤ (4 * w) ^ s :=
  le_of_eq (card_skipLabels w s)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_skipLabels
