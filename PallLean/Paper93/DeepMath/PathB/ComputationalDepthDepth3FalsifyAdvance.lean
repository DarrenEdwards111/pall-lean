import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AdvanceStability

/-!
# Falsify-step clause-order monotonicity: the active clause never backtracks

The clause-ordering half of the deepest-branch decoder is Håstad's forward reconstruction: identify
*which* clause is active at *which* step.  Two step directions, two mechanisms:

* **Advance step** (satisfy within a term, `T` stays live): the scan re-finds `T` —
  `activeTerm_advance_stable` (already proved in `AdvanceStability`).
* **Falsify step** (`T` dies): the active clause must jump *forward* in `cs`.  This file proves that.

`activeTerm_falsify_advances` shows: when fixing a free variable falsifies the current active term
`T`, the new active clause is found **strictly after `T`** in `cs` — every clause up to and including
`T` is falsified under the successor state, so the deterministic clause-order scan resumes in the
suffix past `T`.  Together with advance-stability, the active clause therefore sweeps `cs`
**monotonically forward**, never backtracking — the structural backbone of the forward
reconstruction.

## What remains (honest)

This gives the no-backtrack monotonicity (advance keeps `T`; falsify moves strictly past `T`).  The
*threading* — that interleaving advance and falsify steps along the whole deepest branch reconstructs
the full selected-variable sequence from `(deepestEnd, label)` — is still the open core, now reduced
to assembling these two monotone mechanisms (value recovery via `litTrue_deepestEnd_of_satisfy_step`,
clause order via this file) rather than to any missing per-step fact.  **Not** faked.  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The active clause never backtracks across a falsify step.**  If `T` is the active term under
`σ`, and fixing a free variable `v` to `b` *falsifies* `T` (under `σ' := fixVar σ v b`, with no term
satisfied), then the new active clause is found strictly after `T`: `cs` decomposes as
`pre ++ T :: suf` (the canonical split at `σ`), and `activeTerm cs σ' = suf.find? P'` — the scan
skips the entire falsified prefix `pre ++ [T]` and resumes in `suf`.

Proof: the prefix `pre` is falsified under `σ` (`activeTerm`'s `find?` decomposition + the
no-free-literal dichotomy), and falsification persists under `σ'`
(`termFalsified_fixVar_of_free`); `T` itself is now falsified by hypothesis.  So `find?` of the
successor predicate skips `pre ++ [T]` and lands in `suf`. -/
theorem activeTerm_falsify_advances {cs : List (Clause n)} {σ : Restriction n} {v : Fin n} {b : Bool}
    {T : Clause n} (hact : SwitchingCounting.activeTerm cs σ = some T) (hv : σ v = none)
    (hns' : SwitchingCounting.anyTermSat cs (fixVar σ v b) = false)
    (hfals' : SwitchingCounting.termFalsified (fixVar σ v b) T = true) :
    ∃ pre suf, cs = pre ++ T :: suf ∧
      SwitchingCounting.activeTerm cs (fixVar σ v b)
        = suf.find? (fun U => !SwitchingCounting.termFalsified (fixVar σ v b) U
            && decide (0 < (SwitchingCounting.freeLits (fixVar σ v b) U).length)) := by
  have hns : SwitchingCounting.anyTermSat cs σ = false :=
    SwitchingCounting.activeTerm_anyTermSat_false hact
  -- Decompose `cs = pre ++ T :: suf` from the `σ`-scan.
  have hfind := hact
  rw [SwitchingCounting.activeTerm_eq_find hns, List.find?_eq_some_iff_append] at hfind
  obtain ⟨_hPT, pre, suf, hsplit, hpre⟩ := hfind
  refine ⟨pre, suf, hsplit, ?_⟩
  -- Switch to the `σ'`-scan and split at the decomposition.
  rw [SwitchingCounting.activeTerm_eq_find hns', hsplit, List.find?_append]
  -- The prefix yields nothing under `σ'`.
  have hpre_none : pre.find? (fun U => !SwitchingCounting.termFalsified (fixVar σ v b) U
      && decide (0 < (SwitchingCounting.freeLits (fixVar σ v b) U).length)) = none := by
    rw [List.find?_eq_none]
    intro U hU
    -- `P U = false` under `σ` ⟹ `U` falsified under `σ` (no-free case is unsatisfied ⟹ falsified).
    have hPUfalse : SwitchingCounting.termFalsified σ U = true ∨
        SwitchingCounting.freeLits σ U = [] := by simpa using hpre U hU
    have hUmem : U ∈ cs := by rw [hsplit]; exact List.mem_append_left _ hU
    have hfalsσ : SwitchingCounting.termFalsified σ U = true := by
      rcases hPUfalse with h | h
      · exact h
      · have hsatU : SwitchingCounting.termSat σ U = false := by
          by_contra hsc
          rw [Bool.not_eq_false] at hsc
          have : SwitchingCounting.anyTermSat cs σ = true := by
            rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨U, hUmem, hsc⟩
          rw [hns] at this; exact absurd this (by simp)
        exact SwitchingCounting.term_falsified_of_not_sat_no_free hsatU h
    have hfalsσ' : SwitchingCounting.termFalsified (fixVar σ v b) U = true :=
      termFalsified_fixVar_of_free hfalsσ hv
    simp [hfalsσ']
  -- `none.orElse` drops to the cons; `T` fails the predicate under `σ'` (now falsified), so the
  -- scan resumes in `suf`.
  rw [hpre_none]
  simp [List.find?_cons, hfals']

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_falsify_advances
