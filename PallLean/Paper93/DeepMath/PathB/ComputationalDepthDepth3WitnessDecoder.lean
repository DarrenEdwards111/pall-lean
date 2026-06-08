import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterFalsified
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatRecovery

/-!
# Tight switching, step 23: the live-witness decoder — `hnf`-free reconstruction (branch `razborov-recoverRho-wip`)

The minimal-label fix for the empty-skip wall (brick 49 `decodedSel_not_filter_invariant`).  The wall: the
leaf-scan decoder `decodedSel cs π` reads the false-literal variables of *every* falsified clause, so dead
clauses (falsified by the base `ρ`, off the path) contribute ghost variables indistinguishable from genuine
path variables — forcing the `hnf` (term-alive) hypothesis throughout the tight count.

The fix (HAL's minimal per-step witness, not the expander): decode against the **live sublist**
`cs' := cs.filter (¬ termFalsified ρ ·)` — the clauses *not* dead under `ρ`.  Then:

* the path and selected set are filter-invariant (`replayPath_filter_eq`, `replaySel_filter_eq`, via
  `activeTerm_filter_eq`, since the running state always extends `ρ` and `termFalsified` is monotone);
* `cs'` is alive by construction (`hnf_filter`), so `decodedSel_eq_replaySel` applies to it with **no `hnf`
  assumption on `cs`**.

Composing gives, *unconditionally in `cs`*:

```
  decodedSel (cs.filter (¬ termFalsified ρ ·)) (replayPath cs ρ s) = replaySel cs ρ s.
```

So the decoder recovers the true path-selected set with dead clauses present — the empty-skip wall is
discharged at the decoder level, the witness being exactly "which clauses are live under `ρ`".

* `replayPath_extends`, `replaySel_filter_eq`, `replayPath_filter_eq` — the filter-invariances.
* `decodedSel_filter_eq_replaySel` — the `hnf`-free live-witness decoder correctness.

## Honest scope

This removes the `hnf` *assumption*: correctness now holds with dead clauses present, given the live-sublist
witness.  The remaining cost is *encoding* that witness in the label (which clauses are live) — the live set
depends only on `ρ`, and the path touches `≤ s` clauses, so a per-step active-clause witness keeps the count
`F`-independent (`(Cw)^s`-shape).  That label-cost accounting, and threading this decoder through
`reconstructionCorrect_fullpath` to drop `hnf` from the tight count, is the next step; the expander/Ramanujan
selector remains a Plan-B only if the naive witness blows up.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The replay path always **extends** the base `ρ`: it only falsifies free literals, never touching a
`ρ`-fixed variable. -/
theorem replayPath_extends (cs : List (Clause n)) (ρ : Restriction n) (k : ℕ) :
    Extends ρ (replayPath cs ρ k) := by
  intro v b hb
  by_cases hv : v ∈ replaySel cs ρ k
  · have hnone := mem_freeVars.mp (replaySel_subset_freeVars cs ρ k hv)
    simp [hnone] at hb
  · rw [replayPath_eq_outside cs ρ k hv]; exact hb

/-- The active literal is invariant under dropping `ρ`-dead clauses, on any state extending `ρ`. -/
theorem activeTermLit_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, termFalsified ρ T = true → termFalsified σ T = true) :
    activeTermLit (cs.filter (fun T => !termFalsified ρ T)) σ = activeTermLit cs σ := by
  unfold activeTermLit
  rw [activeTerm_filter_eq hinv]

/-- One replay step is invariant under dropping `ρ`-dead clauses, on a state extending `ρ`. -/
theorem replayStep_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, termFalsified ρ T = true → termFalsified σ T = true) :
    replayStep (cs.filter (fun T => !termFalsified ρ T)) σ = replayStep cs σ := by
  unfold replayStep
  rw [activeTermLit_filter_eq hinv]

/-- The replay path is invariant under dropping `ρ`-dead clauses. -/
theorem replayPath_filter_eq (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ k, replayPath (cs.filter (fun T => !termFalsified ρ T)) ρ k = replayPath cs ρ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [replayPath]
    rw [ih]
    exact replayStep_filter_eq
      (fun T hT => termFalsified_mono (replayPath_extends cs ρ k) hT)

/-- The selected set is invariant under dropping `ρ`-dead clauses. -/
theorem replaySel_filter_eq (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ k, replaySel (cs.filter (fun T => !termFalsified ρ T)) ρ k = replaySel cs ρ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [replaySel]
    rw [ih, replayPath_filter_eq cs ρ k,
      activeTermLit_filter_eq
        (fun T hT => termFalsified_mono (replayPath_extends cs ρ k) hT)]

/-- **The live-witness decoder is correct — with dead clauses present, no `hnf`.**  Decoding the leaf
against the live sublist `cs' = cs.filter (¬ termFalsified ρ ·)` recovers the true path-selected set,
*unconditionally in `cs`*.  This discharges the empty-skip wall at the decoder level. -/
theorem decodedSel_filter_eq_replaySel (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    decodedSel (cs.filter (fun T => !termFalsified ρ T)) (replayPath cs ρ s)
      = replaySel cs ρ s := by
  rw [← replayPath_filter_eq cs ρ s,
    decodedSel_eq_replaySel (Depth3.hnf_filter cs ρ) s,
    replaySel_filter_eq cs ρ s]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodedSel_filter_eq_replaySel
