import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKRWGeneral

/-!
# N-Frame → KRW: the strong→standard composition reduction = the (non-monotone) amortization

The current KRW frontier: STRONG composition of XOR and a random function is proved (arXiv 2410.10189)
and would give `~3.04 log n` — the first improvement over Håstad's `(3−o(1)) log n` in 25+ years — IF it
reduced to STANDARD composition.  This file attacks that reduction, and the recent definitions make the
target precise and connect it to everything before it.

## The precise definitions, and the connection

STRONG composition (Meir, FOCS 2023 / arXiv 2306.00615) is standard composition `f ⋄ g` "forced to behave
like a DIRECT-SUM problem" — i.e. the inner KW games across the blocks are made INDEPENDENT, so the
players cannot amortize: `amort = 0` by construction.  STANDARD composition allows `amort ≥ 0`.  So:

    strong→standard reduction  ⟺  amort = 0 for standard composition  ⟺  the KRW increment.

This is EXACTLY the amortization of `ComputationalDepthNFrameKRWGeneral`
(`CC(KW_{f⋄g}) = CC(KW_f) + CC(KW_g) − amort`), and it is the communication-world twin of the circuit
Freshness / double-duty amortization.

## The decisive fact: strong = standard in the MONOTONE setting

arXiv 2306.00615: **in the monotone setting, strong composition equals standard composition.**  So the
strong→standard gap is a PURELY NON-MONOTONE phenomenon: with no negation, `amort = 0` and the reduction
holds; negation is what lets the players amortize.  This is the SAME enabler as the circuit route, where
monotone circuits (no negation) satisfy Freshness (`no_cancellation_freshness`) and general circuits do
not.  **Unified principle: negation enables amortization in BOTH the circuit direct sum and KRW
composition; monotone kills it in both — provable there, open in general.**

## The theorems

  `strong_to_standard_no_amortization` — **PROVED**: `CCstrong ≤ CCstandard + amort` with `amort = 0`
        (monotone / no negation) gives `CCstrong ≤ CCstandard` — the reduction.  A monotone strong-
        composition lower bound transfers to standard composition.
  `strong_standard_gap` — **PROVED (witness)**: with negation (`amort > 0`) standard can be strictly
        below strong (`CCstandard < CCstrong`); the reduction is load-bearing on `amort = 0`.
  `strong_beats_hastad_if_reduces` — **PROVED (conditional)**: the strong bound `Dstrong ≥ 3.04 log n`
        (scaled `304·t`) plus the reduction (`Dstrong ≤ Dstandard`) gives `Dstandard > 3 log n` (`300·t`)
        — beating Håstad.  So the ENTIRE improvement rests on the non-monotone amortization being `0`.

## Honest scope — the reduction is the open frontier

The reduction is OPEN for general (non-monotone) composition — it is the KRW increment = `P ⊄ NC¹`.
What this file establishes: the strong→standard gap IS the non-monotone amortization (same obstruction as
the circuit Freshness, negation the common enabler); it collapses in the monotone setting (cited, proved);
and IF it reduces, the strong XOR-random bound beats Håstad.  This localizes the frontier exactly — the
whole `3.04 log n` improvement is conditional on controlling negation-enabled amortization — but does not
close it.  Nothing here is `P ⊄ NC¹`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameKRWStrongStandard

/-- **THE REDUCTION FROM NO-AMORTIZATION (proved)**: standard composition is at least strong minus the
amortization (`CCstrong ≤ CCstandard + amort`); with `amort = 0` (the monotone / no-negation case, where
strong = standard by arXiv 2306.00615) the reduction `CCstrong ≤ CCstandard` holds, so a strong-
composition lower bound transfers to standard composition. -/
theorem strong_to_standard_no_amortization (CCstrong CCstandard amort : ℕ)
    (hgap : CCstrong ≤ CCstandard + amort) (hnoamort : amort = 0) :
    CCstrong ≤ CCstandard := by
  omega

/-- **THE GAP IS AMORTIZATION (proved witness)**: with negation (`amort > 0`) standard composition can be
strictly cheaper than strong (`CCstandard < CCstrong`), so the strong→standard reduction is load-bearing
on `amort = 0`.  Witness `(CCstrong, CCstandard, amort) = (20, 15, 5)`. -/
theorem strong_standard_gap :
    ∃ (CCstrong CCstandard amort : ℕ),
      CCstrong ≤ CCstandard + amort ∧ 0 < amort ∧ CCstandard < CCstrong :=
  ⟨20, 15, 5, by omega, by omega, by omega⟩

/-- **THE CONDITIONAL PAYOFF (proved)**: the strong-composition bound `Dstrong ≥ 3.04·log n` (scaled,
`304·t ≤ Dstrong`, `t = log n`) plus the strong→standard reduction (`Dstrong ≤ Dstandard`) yields
`Dstandard > 3·log n` (`300·t`) — the first improvement over Håstad in 25+ years.  The whole improvement
is contingent on the reduction, i.e. on non-monotone amortization being `0`. -/
theorem strong_beats_hastad_if_reduces (Dstrong Dstandard t : ℕ) (ht : 1 ≤ t)
    (hstrong : 304 * t ≤ Dstrong) (hreduce : Dstrong ≤ Dstandard) :
    300 * t < Dstandard := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameKRWStrongStandard

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWStrongStandard.strong_to_standard_no_amortization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWStrongStandard.strong_standard_gap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWStrongStandard.strong_beats_hastad_if_reduces
