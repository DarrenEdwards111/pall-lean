import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestBranch

/-!
# The deepest-branch decoder: the recovery loop generalised, the core isolated

The `(2w)^s` decoder for the deepest branch factors into two halves:

1. **recovery loop** — re-free the queried variables to recover `ρ`;
2. **active-clause identification** — convert each label `(position, bit)` into the queried variable
   `litVar ℓ` (needs the active clause at that step from the end-state).

The single-path `decodeLoop` discharged (1) for the *falsify* path (`freeOn_replayStep_recover`,
which baked in the falsify bit).  The deepest branch takes general bits (a `true` step satisfies),
so the recovery must work for **any** bit.  It does:

* `freeOn_fixVar_free` — `σ v = none ⟹ freeOn (fixVar σ v b) {v} = σ` for **any** `b`.  Re-freeing a
  just-fixed free variable recovers the prior state regardless of the bit.
* `deepestPath_step_free` — along `deepestPath`, the queried variable is the active literal's
  variable, which is free; so each step is exactly a `fixVar` of a free variable, and the recovery
  loop applies step-by-step.

So (1) is now general: given the deepest path's active-literal variables, the recovery loop recovers
`ρ` for the deepest (non-falsify) branch, not just the falsify path.

## The irreducible core (honest)

What remains is purely (2): recovering the active-literal *variables* from the end-state plus the
`(2w)^s` label.  For the falsify path this was free (`decodedSel_eq_replaySel`: queried vars carry
false literals).  For the deepest branch a `true` step leaves no false literal, so the position must
be resolved against the active clause at that step — Håstad's active-clause identification, the
genuine research core.  It is **not** discharged here and **not** faked.  This file completes the
recovery half generally and pins the whole remaining content to the active-clause identifier.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Generalised per-step recovery.**  Re-freeing a just-fixed *free* variable recovers the prior
state, for **any** bit (not only the falsify bit).  This is the recovery step for general (deepest)
branches. -/
theorem freeOn_fixVar_free {σ : Fin n → Option Bool} {v : Fin n} {b : Bool} (h : σ v = none) :
    SwitchingCounting.freeOn (fixVar σ v b) {v} = σ := by
  funext j
  simp only [SwitchingCounting.freeOn, Finset.mem_singleton]
  by_cases hj : j = v
  · rw [if_pos hj, hj]; exact h.symm
  · rw [if_neg hj, fixVar, Function.update_of_ne hj]

/-- **Each deepest-path step fixes a free variable.**  The queried variable is the active literal's
variable, which is free under the current state — so `freeOn_fixVar_free` applies at every step, and
the recovery loop recovers `ρ` along the deepest branch given its active-literal variables. -/
theorem activeTermLit_var_free {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {ℓ : Rung4Literal n} (h : SwitchingCounting.activeTermLit cs σ = some ℓ) :
    σ (litVar ℓ) = none := by
  have hf := SwitchingCounting.activeTermLit_free h
  rw [SwitchingCounting.litFree_var] at hf
  exact Option.isNone_iff_eq_none.mp hf

/-- **Recovery for one deepest-branch step.**  At a step with active literal `ℓ`, re-freeing
`litVar ℓ` from either branch child recovers the current state — the recovery loop step for the
deepest branch (any bit). -/
theorem freeOn_fixVar_active {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {ℓ : Rung4Literal n} (h : SwitchingCounting.activeTermLit cs σ = some ℓ) (b : Bool) :
    SwitchingCounting.freeOn (fixVar σ (litVar ℓ) b) {litVar ℓ} = σ :=
  freeOn_fixVar_free (activeTermLit_var_free h)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.freeOn_fixVar_free
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.freeOn_fixVar_active
