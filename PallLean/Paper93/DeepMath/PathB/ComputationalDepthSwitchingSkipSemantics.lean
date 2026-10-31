import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AdvanceStability
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSkipSeq

/-!
# Tight switching, skip-encoded decoder step 3: the advance-bit semantics (branch `razborov-recoverRho-wip`)

The semantic correctness of the advance bit recorded by the skip-aware encoder (skip-decoder step 2).  The
bit is `termFalsified σ' T || (freeLits σ' T).length = 0` — the negation of `activeTerm`'s predicate
`!termFalsified ∧ hasFree` applied to the just-processed clause `T` at the taken-branch state `σ'`.  We prove
it means exactly what the decoder needs:

```
  advance bit = false   ⟺   activeTerm cs σ' = some T     (the active clause PERSISTS),
```

at every continuing canonical step (`anyTermSat cs σ' = false`).  This is the foundational fact that lets a
forward replay track the active clause from the advance bit alone — *without* recording its `Fin m` index and
*without* `hnf`/`hleaf`/`hpos`:

* The `⟸`/persist-to-false direction is just unpacking `activeTerm`'s `find?` predicate for `T` at `σ'`.
* The `⟹`/false-to-persist direction is the **monotonicity backbone** `activeTerm_fixVar_stable`: fixing the
  canonical free literal never makes an *earlier* clause newly active (the falsified prefix stays falsified),
  so if `T` is still unfalsified with a free literal, the deterministic clause-order scan re-finds `T`.

So the single advance bit carries the full block-boundary information that the `Fin m` index carried, at
`O(1)` cost — this is why the skip label is `(4w)^s`, not `(2wm)^s`.

* `advanceBit_false_iff_active_persists` — advance bit `false` ⟺ the active clause persists, per step.

## Honest scope

This is the per-step semantics of the advance bit (persist ⟺ bit false), resting on the existing canonical
monotonicity (`activeTerm_fixVar_stable`).  Assembling it into a forward-replay decoder that recovers
`deepestSel` from `(σ_end, skip label)` over the whole path — and feeding the resulting `m`-free injection
into the `(4w)^s` descent bound — is the remaining work.  Nothing here yet builds the full decoder; it
establishes that the bit the encoder writes is the right one.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Advance-bit semantics.**  At a continuing canonical step — active term `T` under `σ`, canonical free
literal `ℓ`, and the taken branch `σ' := fixVar σ (litVar ℓ) b` still unsatisfied — the recorded advance bit
`termFalsified σ' T || (freeLits σ' T).length = 0` is `false` **iff** the active term persists
(`activeTerm cs σ' = some T`).  Hence the decoder can track the active clause from the bit alone. -/
theorem advanceBit_false_iff_active_persists {cs : List (Clause n)} {σ : Restriction n}
    {T : Clause n} {ℓ : Rung4Literal n} {b : Bool}
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ)
    (hns' : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false) :
    (SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T
        || decide ((SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length = 0)) = false
      ↔ SwitchingCounting.activeTerm cs (fixVar σ (litVar ℓ) b) = some T := by
  -- `litVar ℓ` is free under `σ` (it is the head of `T`'s free literals).
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  have hv : σ (litVar ℓ) = none := by
    rw [litFree_var] at hfree; exact Option.isNone_iff_eq_none.mp hfree
  constructor
  · -- bit `false` ⟹ persists: monotonicity re-finds `T`.
    intro hbit
    rw [Bool.or_eq_false_iff] at hbit
    obtain ⟨hnf', hfl⟩ := hbit
    have hfree' : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length := by
      rw [decide_eq_false_iff_not] at hfl; omega
    exact activeTerm_fixVar_stable hact hv hns' hnf' hfree'
  · -- persists ⟹ bit `false`: unpack `activeTerm`'s `find?` predicate for `T` at `σ'`.
    intro hpersist
    have hfind : cs.find? (fun U => !SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) U &&
        decide (0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) U).length)) = some T := by
      rw [← SwitchingCounting.activeTerm_eq_find hns']; exact hpersist
    have hP := List.find?_some hfind
    rw [Bool.and_eq_true] at hP
    obtain ⟨hnf, hfl⟩ := hP
    rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hnf
    rw [decide_eq_true_eq] at hfl
    rw [Bool.or_eq_false_iff]
    exact ⟨hnf, by rw [decide_eq_false_iff_not]; omega⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.advanceBit_false_iff_active_persists
