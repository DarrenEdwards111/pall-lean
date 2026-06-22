import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingLiveDNFPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder

/-!
# Håstad switching lemma — live-DNF general-case identity (third brick)

Combining the path/selected-set invariance (`replayPath_liveCs`, `replaySel_liveCs`) with the proved
`hnf` decoder (`decodedSel_eq_replaySel`, applied to the live sub-DNF whose `hnf` is `liveCs_hnf`)
gives, for a **general** `ρ` (no `hnf` on `cs`), the clean identity

  `replaySel cs ρ s = decodedSel (liveCs ρ cs) (replayPath cs ρ s)`   (`replaySel_eq_decodedSel_liveCs`).

So the selected set of a general `ρ` is exactly the end-state set decoder applied to the **live
sub-DNF**.  This is the complete mathematical reduction of the general case to the `hnf` case.

## Honest finding — the confound is relocated, not removed

This identity is unconditional in `cs`, but its right side depends on `liveCs ρ cs` — the terms `ρ`
does *not* falsify — which a decoder seeing only the end-state `replayPath cs ρ s` **cannot compute**:
a term falsified at the end-state may be `ρ`-falsified (dropped from `liveCs`) or path-falsified (an
active term the path killed), and these are indistinguishable from the end-state.  This is the **same
confound, relocated from the variable level (`{ρ-free}` filter, `replaySel_eq_decodedSel_filter`) to
the term level (identify `liveCs ρ cs`)**.  The two reductions are parallel reformulations; neither
gives a from-end-state decoder for general `ρ`.

This confirms (now via the live-DNF route too) that **no deterministic end-state-only decoder breaks
the confound** — consistent with `confound_uncovered`.  The classical switching lemma is
*probabilistic*: it bounds `|Bad|` by an injective encoding into short restriction × star pattern, not
by a single deterministic decoder valid for all `ρ`.  That probabilistic step is the genuine
remaining frontier; it is **not** faked.

## What is proved (clean axioms, no `sorry`)

* `replaySel_eq_decodedSel_liveCs` — the general-case identity `replaySel = decodedSel over liveCs`.

## Honest scope

The complete deterministic reduction of the general case to `hnf` (the live-DNF identity).  The
from-end-state decoder gap (identify `liveCs`/ρ-falsified terms) is the relocated confound and needs
the probabilistic argument; **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.  See `STAR_ENCODING_SCOPE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **General-case live-DNF identity.**  For any `ρ` (no `hnf`), the selected set equals the end-state
set decoder applied to the live sub-DNF. -/
theorem replaySel_eq_decodedSel_liveCs (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    replaySel cs ρ s = decodedSel (liveCs ρ cs) (replayPath cs ρ s) := by
  have h := decodedSel_eq_replaySel (liveCs_hnf ρ cs) s
  rw [replayPath_liveCs, replaySel_liveCs] at h
  exact h.symm

/-!
**General-case live-DNF identity, proved.**  `replaySel cs ρ s = decodedSel (liveCs ρ cs)
(replayPath cs ρ s)` for general `ρ` — the deterministic reduction to `hnf` complete.  The decoder
still needs `liveCs ρ cs` (the ρ-falsified terms), which the end-state alone does not determine — the
confound, relocated to the term level; it needs the probabilistic switching lemma and is **not**
faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_eq_decodedSel_liveCs
