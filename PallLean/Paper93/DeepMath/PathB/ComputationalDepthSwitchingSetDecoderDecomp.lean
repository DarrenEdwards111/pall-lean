import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSetDecoderComplete

/-!
# Håstad switching lemma — exact set-decoder decomposition (set-based route, second brick)

Completeness (`replaySel_subset_decodedSel`) gave `replaySel ⊆ decodedSel` unconditionally.  This
brick pins down the **exact** relationship for general ρ:

  `replaySel cs ρ s = (decodedSel cs (replayPath cs ρ s)).filter (fun v => ρ v = none)`.

That is: the selected set is *exactly* the **ρ-free** part of `decodedSel`.  The over-count is
precisely the ρ-**fixed** variables that `decodedSel` reads off (a false literal of a falsified term
that `ρ` itself fixed, not the path).  In the ρ-falsifies-nothing regime there are no such variables,
recovering `decodedSel_eq_replaySel`; in general the gap is exactly "restrict `decodedSel` to the
ρ-free coordinates."

This makes the remaining decoder obligation completely explicit: the decoder sees the end-state
(`decodedSel` is computable from it) but **not** `ρ`, so it cannot apply the `ρ v = none` filter
directly — the `(2w)^s` label must supply the ρ-free indicator on `decodedSel`.  That label-side
recovery is the open general-case core and is **not** faked.

## What is proved (clean axioms, no `sorry`)

* `replaySel_eq_decodedSel_filter` — **the exact decomposition**: `replaySel` = `decodedSel`
  restricted to ρ-free variables.

## Honest scope

The exact characterization of the over-count.  Supplying the ρ-free indicator from the label alone
(without `ρ`) — the general-case soundness — is **not** done here and is **not** faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Exact set-decoder decomposition.**  The selected set is exactly the ρ-free part of the
end-state decoder `decodedSel`; the over-count is precisely the ρ-fixed variables. -/
theorem replaySel_eq_decodedSel_filter (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    replaySel cs ρ s
      = (decodedSel cs (replayPath cs ρ s)).filter (fun v => ρ v = none) := by
  ext v
  rw [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨replaySel_subset_decodedSel cs ρ s hv,
      mem_freeVars.mp (replaySel_subset_freeVars cs ρ s hv)⟩
  · rintro ⟨hvd, hρv⟩
    rw [decodedSel, Finset.mem_filter] at hvd
    obtain ⟨_, C, hC, hTf, ℓ, hℓC, hℓv, hℓf⟩ := hvd
    by_contra hnotin
    have heqo := replayPath_eq_outside cs ρ s hnotin
    rw [hρv] at heqo
    have hnone : replayPath cs ρ s (litVar ℓ) = none := by rw [hℓv]; exact heqo
    exact litFalse_litVar_fixed hℓf hnone

/-!
**Exact decomposition, proved.**  `replaySel = decodedSel ∩ {ρ-free}` for general ρ — the over-count
is precisely the ρ-fixed variables.  The decoder sees `decodedSel` (end-state) but not `ρ`, so the
remaining obligation is to supply the ρ-free indicator from the `(2w)^s` label; that is the open
general-case core and is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_eq_decodedSel_filter
