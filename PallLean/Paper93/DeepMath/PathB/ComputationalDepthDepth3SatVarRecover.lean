import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AdvanceStability
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPositionLit

/-!
# Satisfy-variable label recovery: the per-step engine

The threading (`reconstruction_of_satSel_decoder`) reduced the open kernel to recovering
`deepestSatSel` — the **satisfy-step variables** — from the end-state and a `(2w)^s` position label.
This file builds and proves the **engine** of that recovery: a single backward satisfy step.

The mechanism: a satisfy step fixes the active literal `ℓ` of the active clause `T` to its
*satisfying* value `satValue ℓ`, leaving `T` live.  So at the **successor** state
`σ' := fixVar σ (litVar ℓ) (satValue ℓ)`:

* `T` is **still the active clause** — `activeTerm_advance_stable` (the scan re-identifies it);
* indexing `T` at the recorded position `pivotPosOf cs σ` returns `ℓ` — `clauseLitAt_pivot`;

so the decoder recovers `ℓ` (hence the satisfy variable `litVar ℓ`) from `σ'` and the position
*alone*, and freeing `litVar ℓ` inverts the step back to `σ` (`freeOn_fixVar_free`).

* `satVar_recover` — **the engine.**  From the successor state + recorded position, recover the
  active clause (`= activeTerm cs σ'`) and the active literal `ℓ`.
* `satStep_freeOn` — freeing the recovered variable inverts the satisfy step (`freeOn σ' {litVar ℓ} = σ`).
* `satStep_backward` — the two packaged: one backward satisfy step recovers `litVar ℓ` and restores `σ`.

## Honest scope

This is the **per-step** recovery — it recovers a satisfy variable from the *immediate* successor
state.  In a backward reconstruction it fires whenever the current reconstruction equals the step's
successor and the step is a satisfy step.  Assembling these into a full `Dsat` for the whole deepest
branch additionally requires sequencing the backward steps through the interleaved **falsify** steps —
i.e. identifying, from the *final* end-state, the active clause at each step (the falsify steps move
the active clause forward, so the backward scan must re-liven falsified clauses in the right order).
That active-clause identification from the non-satisfying deepest leaf is the documented research core
and is **not** discharged here and **not** faked.  The satisfy step's own recovery — the part the
`(2w)^s` label exists to enable — is proved.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The satisfy-variable recovery engine.**  At a satisfy step (the active literal `ℓ` set to its
satisfying value, leaving the active clause `T` live with a free literal and no term satisfied), the
successor state `σ'` *still* has `T` as its active clause, and indexing `T` at the recorded position
`pivotPosOf cs σ` returns `ℓ`.  So the decoder recovers the active literal — hence the satisfy
variable `litVar ℓ` — from `σ'` and the position alone. -/
theorem satVar_recover {cs : List (Clause n)} {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hT : SwitchingCounting.activeTerm cs σ = some T)
    (hℓ : SwitchingCounting.activeTermLit cs σ = some ℓ)
    (hns' : SwitchingCounting.anyTermSat cs
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) = false)
    (hnf' : SwitchingCounting.termFalsified
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) T = false)
    (hfree' : 0 < (SwitchingCounting.freeLits
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) T).length) :
    SwitchingCounting.activeTerm cs (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) = some T ∧
    SwitchingCounting.clauseLitAt T (SwitchingCounting.pivotPosOf cs σ) = some ℓ := by
  refine ⟨activeTerm_advance_stable hT hℓ hns' hnf' hfree', ?_⟩
  have hpos : SwitchingCounting.pivotPosOf cs σ = T.lits.idxOf ℓ := by
    unfold SwitchingCounting.pivotPosOf; rw [hT, hℓ]
  rw [hpos]
  exact SwitchingCounting.clauseLitAt_pivot hT hℓ

/-- **Freeing the recovered variable inverts the satisfy step.**  Since the active literal's variable
is free under `σ`, freeing it from the successor state recovers `σ`. -/
theorem satStep_freeOn {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (hℓ : SwitchingCounting.activeTermLit cs σ = some ℓ) (b : Bool) :
    SwitchingCounting.freeOn (fixVar σ (litVar ℓ) b) {litVar ℓ} = σ :=
  freeOn_fixVar_free (activeTermLit_var_free hℓ)

/-- **One backward satisfy step.**  Packaging `satVar_recover` and `satStep_freeOn`: from the
successor state `σ'` and the recorded position, the decoder recovers the satisfy variable `litVar ℓ`
(`v = litVar (clauseLitAt (activeTerm cs σ') p)`) and freeing it restores the predecessor `σ`. -/
theorem satStep_backward {cs : List (Clause n)} {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hT : SwitchingCounting.activeTerm cs σ = some T)
    (hℓ : SwitchingCounting.activeTermLit cs σ = some ℓ)
    (hns' : SwitchingCounting.anyTermSat cs
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) = false)
    (hnf' : SwitchingCounting.termFalsified
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) T = false)
    (hfree' : 0 < (SwitchingCounting.freeLits
      (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) T).length) :
    ∃ T', SwitchingCounting.activeTerm cs
        (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) = some T' ∧
      SwitchingCounting.clauseLitAt T' (SwitchingCounting.pivotPosOf cs σ) = some ℓ ∧
      SwitchingCounting.freeOn
        (fixVar σ (litVar ℓ) (SwitchingCounting.satValue ℓ)) {litVar ℓ} = σ := by
  obtain ⟨hT', hrec⟩ := satVar_recover hT hℓ hns' hnf' hfree'
  exact ⟨T, hT', hrec, satStep_freeOn hℓ _⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.satVar_recover
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.satStep_freeOn
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.satStep_backward
