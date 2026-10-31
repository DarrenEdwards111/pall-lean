# Route F — complete arc summary, and the bedrock open lemma

This maps the full Route-F formalization (P-side rank bound for `CookLevinFrontierHyp`) built across this
session, and states precisely where it terminates: a single open lemma, equivalent in strength to a space
lower bound for SAT that is far beyond known results.

## The arc (all sorry-free, clean axioms unless noted)

| File | Result | Status |
|---|---|---|
| `…ProfileCount` | `#profiles ≤ poly(n)` for an `O(log n)` window (`s^{c·log₂ n} ≤ n^{c(log₂ s+1)}`) | proved |
| `…RouteFProbe` | F₂ matrix rank; identity (full) vs profile-compressed (low) | proved + `native_decide` |
| `…ProductSheetGap` | independent (tensor) product ⇒ rank multiplies `2^m` (the gap) | proved + computed |
| `…LaneClassification` | shared-lane (Hadamard) product ⇒ rank bounded by #lanes (the fix); `CookLevinLaneClassified` stated | proved + computed |
| `…TableauTest` | tiny Bool CA tableau: space-cut rank bounded/saturating | `native_decide` |
| `…TMTableauTest` | real 3-symbol two-way TM tableau: space-cut rank ~linear in depth, bounded in width | `native_decide` |
| `…CrossingBound` | crossing-sequence reduction: rank `≤ A^C`, `poly(n)` iff `C = O(log n)` | proved |
| `…ObliviousCrossings` | Hennie pigeonhole: some cut crossed `≤ T/W`; oblivious + width `⇒ O(log n)` crossings `⇒ poly` | proved |
| `…CrossingTight` | shuttle crosses a cut `Θ(T)` times — the width condition is *necessary* | proved |
| `…SpreadObstruction` | `Spreads ⟺ space ≥ T/log n`; small-space ⇒ `¬ Spreads` (shuttle witness) | proved |

**The mechanism is proved end-to-end.**  Reading top to bottom: low-degree windows give few profiles;
independent products would blow the rank up exponentially; lane-sharing (coupling) prevents that; real
tableaux empirically stay low-rank; the *reason* is the crossing-sequence bound `rank ≤ A^{crossings}`; the
crossing count is `O(log n)` for oblivious wide machines (pigeonhole) but `Θ(T)` for concentrated ones
(tight); and "wide" means space `≥ T/log n`.

## The bedrock open lemma

`CookLevinFrontierHyp` (via Route F) holds **iff** the Cook–Levin compilation *spreads*, i.e.

> **every bounded SAT-decider uses space `S ≥ T / log n`.**

This is a **space lower bound for SAT**, and it is the terminus: it is not a polynomial/geometric fact to
grind out, it is open mathematics of `P`-vs-`NP` strength.

## Positioning against known results (why it is genuinely hard)

* **Known SAT time–space tradeoffs** (Fortnow–Lipton–Viglas–Van Melkebeek; Williams): SAT on
  *subpolynomial-space* machines requires time `≥ n^{2cos(π/7)} ≈ n^{1.801}`.  These lower-bound *time given
  small space* — they are `Ω(n^{1.8})`-scale and do **not** force large space.
* **What Route F needs** is the opposite and far stronger: space `≥ T/log n` for *every* poly-time decider —
  i.e. SAT-deciders cannot be (poly-time, sub-`T/log n`-space).  In particular it would imply
  NP-complete problems are not in poly-time small-space classes (`SC`-like), which is open and would be a
  major separation (`NP ⊄` poly-time-polylog-space).
* The gap between known (`Ω(n^{1.8})` time for tiny space) and required (`Ω(T/log n)` space for all
  poly time) is enormous.  So Route F's last lemma is **well beyond current techniques**.

## Honest verdict

Route F is a **faithful reduction**: it transforms "explicit super-polynomial general-circuit lower bound"
into "`T/log n` space lower bound for SAT".  Both endpoints are open and of the same strength; the value is
that the transformation, and every link in it, is now a *theorem*, and the obstruction (small-space
deciders, the shuttle) is a *theorem* rather than a worry.

This is the end of what can be honestly formalized along Route F short of a genuine new idea for the space
lower bound (or its refutation).  Nothing in the arc asserts `CookLevinFrontierHyp`, `GlobalGodMoveHyp`, or
`P ≠ NP`; what is proven is the scaffolding, the reductions, and the barriers.

## If the work continues

The only honest moves from here are *research*, not formalization-of-known-facts:
1. attack the space lower bound "SAT-deciders use `≥ T/log n` space" directly (a recognized hard open
   problem — likely needs a new idea);
2. or refute it by exhibiting a small-space poly-time SAT-decider (which would itself imply `P = NP`-class
   collapses) — i.e. the same frontier from the other side.

Either is genuine new mathematics; neither is a Lean exercise.  The formalization has done its job: it has
made the target exact, the reductions rigorous, and the difficulty precisely located.
