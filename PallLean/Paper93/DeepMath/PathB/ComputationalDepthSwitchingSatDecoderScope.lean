import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingLiveDNF
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MaintainInvariant

/-!
# Håstad switching lemma — satisfy/deepest decoder scope (the `hnf`-base, and live-DNF connection)

Scoping the satisfy/deepest decoder `recoverStream` (the codebase's switching-lemma decoder) and the
exact origin of its `hnf` restriction.

**Why `recoverStream` needs `hnf`.**  `recoverStream_eq` carries the invariant
`∀ U ∈ cs, termFalsified τ U = termFalsified σ U` (falsification-agreement), consumed at each step by
`activeTerm_eq_of_falsified_agree` (the recursion engine: agreement ⟹ same active term, so the
decoder recomputes the descent's active stream).  The bad-`ρ` theorem starts the decoder at
`τ = (fun _ => none)` (all-free).  All-free falsifies nothing (`termFalsified_allFree`), so the base
agreement `termFalsified (all-free) U = termFalsified ρ U` forces `termFalsified ρ U = false` —
exactly `hnf`.

**Live-DNF connection.**  The base agreement *does* hold on the **live sub-DNF** (`liveCs_base_agree`):
both sides are `false` there (`termFalsified_allFree` and `liveCs_hnf`).  So `recoverStream` applied to
`liveCs ρ cs` is correct unconditionally — the decoder's `hnf`-base is satisfied on the live sub-DNF.
The remaining gap is that the decoder must *know* to run on `liveCs ρ cs` (identify the `ρ`-falsified
terms from the leaf) — the confound, exactly as the four other routes found.

**Plan to discharge `hinj`.**  Either (a) reformulate the switching bound on the live DNF from the
start (standard: the bad event is about `F|ρ` with dead terms removed, so `hnf` holds by construction
and `recoverStream` gives `hinj`), or (b) a Razborov-style forward decoder that, from the leaf + star
code, un-sets path variables and recomputes active terms on partial states without an all-free base.
Route (a) is the cleaner formalization target: it makes `hinj` available on `liveCs`, and the
remaining work is the bad-event/measure reindexing onto live sub-DNFs.

## What is proved (clean axioms, no `sorry`)

* `termFalsified_allFree` — the all-free restriction falsifies no term.
* `liveCs_base_agree` — the decoder's falsification-agreement base holds on the live sub-DNF.

## Honest scope

The `hnf`-origin analysis plus the live-DNF connection to the decoder's base.  Discharging `hinj`
unconditionally (the confound) is the genuine remaining core; not faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.  See `SATISFY_DECODER_SCOPE.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The all-free restriction falsifies no term.** -/
theorem termFalsified_allFree (T : Clause n) : termFalsified (fun _ => none) T = false := by
  rw [termFalsified, List.any_eq_false]
  intro m _
  have hm : litFalse (fun _ : Fin n => none) m = false := litFalse_free_eq_false rfl
  simp [hm]

/-- **The decoder's falsification-agreement base holds on the live sub-DNF.**  On `liveCs ρ cs`,
all-free agrees with `ρ` on falsification (both falsify nothing) — so `recoverStream`'s `hnf`-base is
satisfied there. -/
theorem liveCs_base_agree (ρ : Restriction n) (cs : List (Clause n)) :
    ∀ U ∈ liveCs ρ cs, termFalsified (fun _ => none) U = termFalsified ρ U := by
  intro U hU
  rw [termFalsified_allFree, liveCs_hnf ρ cs U hU]

/-!
**Satisfy/deepest decoder scoped.**  The decoder's `hnf` comes from its all-free base; that base holds
on the live sub-DNF (`liveCs_base_agree`), so the decoder is correct on `liveCs ρ cs` — but
identifying `liveCs` from the leaf is the confound.  Discharging `hinj` (via live-DNF reindexing or a
Razborov forward decoder) is the genuine remaining core; not faked.  AC⁰/depth-3; collapse + P≠NP
untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.liveCs_base_agree
