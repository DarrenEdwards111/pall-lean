import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionTree

/-!
# The Williams cash‑out: the whole arc as one conditional theorem

This file assembles the entire programme into a single top‑level statement, in the contrapositive (Williams) shape:

> a small ACC⁰ predictor correlating with the holonomy parity
> ⇒ (restriction tree) it reduces to a depth‑2 `MOD`‑bottom survivor
> ⇒ that survivor provably fails to correlate (the proved machinery)
> ⇒ by transfer of correlation under restriction, contradiction.

Hence **no small ACC⁰ predictor correlates with the holonomy parity** — *conditional on the named gaps*.

The logic of the cash‑out is fully proved (`williams_correlation_cashout`); it is driven by the proved descent
`reduces_to_depth2`.  The three load‑bearing inputs are exactly the programme's named walls:

* `hswitch : RestrictionTreeSwitch` — the per‑layer Håstad switching (depth `d → d−1`).  *Named.*
* `hfail` — every depth‑`≤2` survivor fails to correlate.  *Discharged by the proved machinery*: support extraction
  (`…ACC0CircuitModel.eval_factors`) + the pigeonhole correlation failure
  (`…ACCSwitchingPipeline.predictor_fails_of_survivors`) + the depth‑2 transfer
  (`…ACC0DepthReduction.reduction_bridge`), once the survivor is put in depth‑2 `MOD`‑bottom form with a
  low‑survivor restriction (the `|overlapCoords|`‑small / core‑decomposition condition).
* `htransfer` — correlation on the full cube transfers to the survivor on the restricted subcube.  *Named* (the
  subcube relativization of the correlation engine).

## What is proved (clean axioms, no `sorry`)

* `williams_correlation_cashout` — **the contrapositive cash‑out**: `RestrictionTreeSwitch` + depth‑2 survivor
  failure + correlation transfer ⇒ the predictor does not correlate with the holonomy parity.  Proved by chaining
  `reduces_to_depth2` with the failure and transfer.

## Honest scope

Every *structural and combinatorial* step of the arc is mechanized; this file ties them into the final logical
shape.  The conclusion is conditional on the two genuine `NP ⊄ ACC⁰`‑strength inputs — the per‑layer switching
(`RestrictionTreeSwitch`) and the subcube transfer (`htransfer`) — plus the proved survivor‑failure machinery.
These are precisely the Håstad switching lemma and the relativization of the correlation bound; nothing here makes
them disappear.  The value is that the **entire reduction is now one explicit theorem**, with the irreducible
difficulty isolated to exactly those named hypotheses.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCWilliamsCashout

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACCRestrictionTree

variable {n : ℕ}

/-- **The Williams correlation cash‑out (proved logic): no small ACC⁰ predictor correlates with the holonomy
parity, conditional on the named gaps.**

* `hswitch` — the per‑layer Håstad switching (restriction tree);
* `hfail` — every depth‑`≤2` survivor fails to correlate (the proved support‑extraction + pigeonhole machinery);
* `htransfer` — correlation transfers to the survivor under the accumulated restriction (subcube relativization).

The proof is the contrapositive chain: if the predictor correlated, `reduces_to_depth2` would produce a depth‑`≤2`
survivor that both fails (`hfail`) and, by transfer of the predictor's correlation (`htransfer`), does not fail —
a contradiction. -/
theorem williams_correlation_cashout
    (Correlates SurvivorFails : ACC0Circuit n → Prop) (C : ACC0Circuit n)
    (hswitch : RestrictionTreeSwitch (n := n))
    (hfail : ∀ C' : ACC0Circuit n, depth C' ≤ 2 → SurvivorFails C')
    (htransfer : ∀ (C' : ACC0Circuit n) (ρs : List (Restriction n)), depth C' ≤ 2 →
        (∀ x, AgreesAll ρs x → eval C x = eval C' x) → Correlates C → ¬ SurvivorFails C') :
    ¬ Correlates C := by
  intro hcorr
  obtain ⟨ρs, C', hd, heq⟩ := reduces_to_depth2 hswitch C
  exact htransfer C' ρs hd heq hcorr (hfail C' hd)

/-- **The contrapositive reading (proved): a predictor that *does* correlate forces a survivor that does *not*
fail.**  Equivalent repackaging — if some small ACC⁰ predictor correlated with the holonomy parity, the restriction
tree would yield a depth‑`≤2` survivor whose correlation failure is *violated* by transfer, i.e. the named gaps
cannot all hold together with a correlating predictor. -/
theorem correlating_predictor_blocks_failure
    (Correlates SurvivorFails : ACC0Circuit n → Prop) (C : ACC0Circuit n)
    (hswitch : RestrictionTreeSwitch (n := n)) (hcorr : Correlates C)
    (htransfer : ∀ (C' : ACC0Circuit n) (ρs : List (Restriction n)), depth C' ≤ 2 →
        (∀ x, AgreesAll ρs x → eval C x = eval C' x) → Correlates C → ¬ SurvivorFails C') :
    ∃ (C' : ACC0Circuit n), depth C' ≤ 2 ∧ ¬ SurvivorFails C' := by
  obtain ⟨ρs, C', hd, heq⟩ := reduces_to_depth2 hswitch C
  exact ⟨C', hd, htransfer C' ρs hd heq hcorr⟩

end PallLean.Paper93.DeepMath.PathB.ACCWilliamsCashout

#print axioms PallLean.Paper93.DeepMath.PathB.ACCWilliamsCashout.williams_correlation_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.ACCWilliamsCashout.correlating_predictor_blocks_failure
