import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting

/-!
# The reverse-decode single step: un-fixing recovers the previous state

**STATUS: REAL.  THE PER-STEP INVERSE OF THE FAITHFUL PATH.**

The breakthrough that makes the canonical decoder tractable: `activeClause_stable`
says the active clause is **recomputable from the more-fixed state** `σ_{i+1}` (it
is unchanged across a within-clause step), so the *reverse* decoder, holding only
`σ_{i+1}`, can recompute it.  The per-step inverse this file proves is:

> un-fixing the just-fixed variable recovers the previous state —
> `freeOn (actStep cs σ) {litVar ℓ} = σ`  when  `activeLit cs σ = some ℓ`.

This is `decode_step ∘ encode_step = id` at one step.  Iterated against the active
clause recomputed at each `σ_{i+1}` (stable within a clause, advancing at the
length-1 boundary), it is the spine of `decode_encode_id`.  The remaining content
is to drive the iteration off a `(2w)^s` label (which clause-literal index, and the
within/boundary bit) — the Håstad bookkeeping.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Per-step inverse.**  Un-fixing the coordinate the step fixed recovers the
state before the step.  The fixed coordinate was free before (`activeLit` is free),
so setting it back to `none` agrees with the previous restriction there, and `actStep`
changed nothing else. -/
theorem freeOn_actStep_recover {cs : List (Clause n)} {σ : Restriction n}
    {ℓ : Rung4Literal n} (h : activeLit cs σ = some ℓ) :
    freeOn (actStep cs σ) {litVar ℓ} = σ := by
  have hfree : Depth3.litFree σ ℓ = true := activeLit_free h
  have hnone : σ (litVar ℓ) = none := by
    rw [litFree_var] at hfree; exact Option.isNone_iff_eq_none.mp hfree
  have hstep : actStep cs σ = falFix σ ℓ := by rw [actStep, h]
  funext j
  rw [hstep]
  simp only [freeOn]
  by_cases hj : j = litVar ℓ
  · subst hj
    rw [if_pos (Finset.mem_singleton_self _)]
    exact hnone.symm
  · rw [if_neg (by rw [Finset.mem_singleton]; exact hj)]
    exact falFix_eq_outside σ ℓ hj

/-- **Active clause recomputable across a within-clause step (decoder form).**  When
the active clause has `≥ 2` free literals, the state after the step has the *same*
active clause — so the reverse decoder, holding `actStep cs σ`, recovers the clause
whose literal it must un-fix without any label information. -/
theorem activeClause_actStep_eq {cs : List (Clause n)} {σ : Restriction n}
    {C : Clause n} (hnodup : (C.lits.map litVar).Nodup)
    (hC : activeClause cs σ = some C) (hlen : 1 < (freeLits σ C).length) :
    activeClause cs (actStep cs σ) = activeClause cs σ := by
  rw [activeClause_stable hnodup hC hlen, hC]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_actStep_recover
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeClause_actStep_eq
