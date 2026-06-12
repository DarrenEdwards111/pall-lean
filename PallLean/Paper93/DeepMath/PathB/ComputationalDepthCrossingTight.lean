import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObliviousCrossings

/-!
# Route F — the crossing bound is tight: the width/spread condition is *necessary*

The previous file proved the `O(log n)`-crossings claim (hence `poly(n)` rank) **for oblivious, wide
machines** (active width `≥ T/log n`).  The natural worry: is the width condition a real requirement, or an
artifact of loose analysis?  This file settles it — the crossing bound `T/W` is **tight**, so the condition
is genuinely necessary.

## Proved

`shuttle_crosses_every_step` — the **shuttle** trajectory `pos t = t mod 2` (a small-space machine looping
over a width-2 region) crosses the cut at `0` on **every** step: `crossings = T`.

So `Θ(T)` crossings of a single cut are achievable.  Plugged into the crossing-sequence rank bound
(`CrossingBound.crossing_bound_general`), this gives a rank bound of `A^{Θ(T)}` — **exponential** — and no
choice of cut helps a machine that genuinely concentrates its work (the active region is width-2, every
cut inside it is crossed `Θ(T)` times).

## The two-sided picture (both proved)

* **Sufficient** (`oblivious_fixed_cut_few_crossings`): if the head spreads — oblivious with active width
  `≥ T/log n` — then some fixed cut has `O(log n)` crossings ⇒ `poly(n)` rank.
* **Necessary** (`shuttle_crosses_every_step`): if the head concentrates — small active space, shuttling —
  then crossings are `Θ(T)` ⇒ the crossing bound gives only `A^{Θ(T)}` (exponential).

## Why this is exactly where Route F's difficulty lives — and not a free win

You **cannot** pad your way around it: widening the tape with blank cells creates many `0`-crossing cuts,
but those are in the padding (the head never visits them) — the rank across such a cut is trivial and says
nothing about the computation.  The meaningful cuts lie **inside the active region**, and there the shuttle
shows crossings can be `Θ(T)`.

So `CookLevinFrontierHyp` via Route F requires the compilation to **spread** — active width `≥ T/log n` —
which is *not* automatic: a **small-space** SAT-decider (if one exists) would shuttle, cross `Θ(T)` times,
and defeat the rank bound.  That is precisely the `P`-vs-`NP`-strength obstruction: bounding the rank for an
*arbitrary* bounded machine demands controlling its space/spread, which one cannot do for free.  The honest
conclusion of the whole Route-F line: **the mechanism is proved end-to-end, and the single remaining lemma
is the genuine, hard, structural claim that the Cook–Levin compilation spreads (oblivious + active width
`≥ T/log n`).**  Nothing here asserts it.
-/

namespace PallLean.Paper93.DeepMath.PathB.Crossings

open Finset

/-- A **shuttle** trajectory crosses the cut at `0` on every step, so `crossings = T` — the crossing bound
`T/W` is tight, and `Θ(T)` crossings are achievable by a concentrated (small-space) computation. -/
theorem shuttle_crosses_every_step (T : ℕ) : crossings (fun t => t % 2) 0 T = T := by
  rw [crossings, Finset.filter_true_of_mem (fun t _ => ?_), Finset.card_range]
  omega

end PallLean.Paper93.DeepMath.PathB.Crossings

#print axioms PallLean.Paper93.DeepMath.PathB.Crossings.shuttle_crosses_every_step
