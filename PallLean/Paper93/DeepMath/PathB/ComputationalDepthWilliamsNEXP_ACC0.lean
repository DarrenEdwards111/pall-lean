import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCWilliamsCashout

/-!
# Williams' route to `NEXP ⊄ ACC⁰`: the algorithmic‑method scaffold

`NEXP ⊄ ACC⁰` is a *theorem* (Williams 2011), unlike `NP ⊄ ACC⁰`.  This file mechanizes the **logical skeleton** of
Williams' algorithmic method for it, with the two genuinely hard ingredients named as known inputs:

> a nontrivial ACC⁰‑circuit‑SAT algorithm  (`ACC0SatSpeedup`, Williams' algorithm)
> together with `NEXP ⊆ ACC⁰`             (`NEXPHasACC0Circuits`, the assumption to refute)
> collapses the nondeterministic time hierarchy (`Collapse`)
> but the hierarchy does **not** collapse  (`¬ Collapse`, the unconditional hierarchy theorem)
> ⇒ `NEXP ⊄ ACC⁰`.

The cash‑out *logic* is proved here (pure implication, no axioms).  The load‑bearing inputs — `williams` (the
algorithmic method's core implication, powered by the SAT speedup) and `hierarchy` (the nondeterministic time
hierarchy) — are real theorems supplied as hypotheses, not re‑proved.

## The N‑frame angle (honest)

The N‑frame / holonomy + correlation machinery built in this corpus identifies the hard restricted predictor target
and explains, geometrically, why structured circuits cannot correlate with it.  It can *supply the route to a
structured ACC⁰‑SAT speedup* — but **N‑frame alone does not replace Williams' SAT‑speedup theorem**.  So the honest
N‑frame statement is the conditional `nframe_williams_cashout`: *if* the N‑frame structure yields the ACC⁰‑SAT
speedup (`NFrameGivesACC0SatSpeedup`), *then* `NEXP ⊄ ACC⁰`.  Proving `NFrameGivesACC0SatSpeedup` — that the
holonomy/restriction structure gives a nontrivial ACC⁰‑SAT speedup — is the genuine research target (the Williams
bridge); it is **not** proved by what we have.

## What is proved (clean axioms, no `sorry`)

* `acc0_sat_speedup_implies_NEXP_not_ACC0` — **the Williams cash‑out**: `ACC0SatSpeedup` + (`williams`) + (`¬
  Collapse`) ⇒ `¬ NEXPHasACC0Circuits`.
* `nframe_williams_cashout` — **the N‑frame route**: `NFrameGivesACC0SatSpeedup` (+ the bridge to a speedup, + the
  same Williams/hierarchy inputs) ⇒ `¬ NEXPHasACC0Circuits`.

## Honest scope

This is the *scaffold* of a known theorem: the implication structure of Williams' method, mechanized.  It does
**not** prove `NEXP ⊄ ACC⁰` outright — that needs `williams` (the SAT‑speedup‑powered collapse) and `hierarchy`
(the time hierarchy), both real theorems named here as hypotheses.  Nor does it prove `NP ⊄ ACC⁰` or `P ≠ NP`.  Its
value is an honest, explicit account of *exactly which known inputs* close `NEXP ⊄ ACC⁰`, and *where* the N‑frame
machinery would plug in (supplying `NFrameGivesACC0SatSpeedup`, the open Williams bridge).
-/

namespace PallLean.Paper93.DeepMath.PathB.WilliamsNEXP_ACC0

/-- **The Williams cash‑out (proved logic): a nontrivial ACC⁰‑SAT algorithm refutes `NEXP ⊆ ACC⁰`.**

* `ACC0SatSpeedup` — a nontrivial ACC⁰‑circuit‑SAT algorithm (Williams' algorithm; named known input);
* `NEXPHasACC0Circuits` — `NEXP ⊆ ACC⁰` (the assumption to refute);
* `Collapse` — a collapse of the nondeterministic time hierarchy;
* `williams` — Williams' algorithmic method: the speedup together with `NEXP ⊆ ACC⁰` forces the collapse;
* `hierarchy` — the nondeterministic time hierarchy theorem: no such collapse.

Then `NEXP ⊄ ACC⁰`.  The proof is the one‑line algorithmic‑method contradiction. -/
theorem acc0_sat_speedup_implies_NEXP_not_ACC0
    (ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) (speedup : ACC0SatSpeedup) :
    ¬ NEXPHasACC0Circuits :=
  fun hacc => hierarchy (williams speedup hacc)

/-- **The N‑frame route (proved logic): if the N‑frame structure yields the ACC⁰‑SAT speedup, then `NEXP ⊄ ACC⁰`.**

The N‑frame holonomy/correlation machinery supplies `NFrameGivesACC0SatSpeedup`; `bridge` turns it into the
ACC⁰‑SAT speedup; the rest is the Williams cash‑out.  Proving `bridge` (N‑frame ⇒ nontrivial ACC⁰‑SAT) is the open
Williams bridge — the genuine research target; it is *not* established here. -/
theorem nframe_williams_cashout
    (NFrameGivesACC0SatSpeedup ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (bridge : NFrameGivesACC0SatSpeedup → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) (hnframe : NFrameGivesACC0SatSpeedup) :
    ¬ NEXPHasACC0Circuits :=
  acc0_sat_speedup_implies_NEXP_not_ACC0 ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    williams hierarchy (bridge hnframe)

end PallLean.Paper93.DeepMath.PathB.WilliamsNEXP_ACC0

#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsNEXP_ACC0.acc0_sat_speedup_implies_NEXP_not_ACC0
#print axioms PallLean.Paper93.DeepMath.PathB.WilliamsNEXP_ACC0.nframe_williams_cashout
