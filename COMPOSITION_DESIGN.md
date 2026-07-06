# Multi-cut composition design — after the 21-rung arc

Status: DESIGN DOCUMENT, no Lean. The single-cut framework is closed at
`cbudget ≥ 2·live + Ω(√N)` uniformly at every band (rung 21,
`sat3_uniform_band_bound`, commit 6db5678f). One cut cannot give more: `j`
straddling blocks may lawfully carry `j·v` mass (rung 20), and every pin
census self-caps at pool scale `Θ(m)` (rung 8). The question set by HAL:

> When do Ω(√N) charges from separate balanced cuts ADD, rather than all
> being paid by the same straddling/exits?

## 1. The answer in one line

Charges add exactly when they are billed to **disjoint regions of the
circuit's excess ledger**, and the only billing scheme whose regions are
disjoint *by construction* — rather than by an unforceable topological
assumption — is billing by **annulus** (the gate set between two nested
balanced boundaries), not by cone. Cones nest; annuli partition.

## 2. Why the naive composition laws are dead

**(a) Horizontal: many gate-disjoint balanced cones.** If a minimal circuit
contained `k` pairwise gate-disjoint balanced wires, their coneExcesses
would add against the global gate count and rung 21 would multiply by `k`.
But nothing forces this: a caterpillar-shaped circuit (absorb one leaf at a
time along a single path) has balanced wires at every band, all on ONE
nested chain — no two disjoint cones at any scale. Horizontal multiplicity
is a property the adversary controls. DEAD as a forcing strategy.

**(b) Vertical: stack the bands of one chain.** Nested cones
`cone(w_T) ⊆ cone(w_{4T})` can share all their excess: coneExcess of the
outer wire need not exceed that of the inner one by anything (extend a cone
by single-new-leaf gates and the excess is constant). Rung 21 charges every
band `Ω(m)`, but on a chain all those charges can be paid by the SAME
`Ω(m)` pool of excess gates. This is precisely the rung-12 finding
(poison prices 1:1; m-amplification dead) seen from the circuit side. DEAD.

**(c) Restriction-recovery (gate-elimination style).** Charge the top band,
pin `g` blocks with the private kit (a clean reduction `sat3[m] → sat3[m−g]`
— proven tool), recurse; additivity by induction requires each pinning to
DESTROY the `Ω(m)` excess just charged. It doesn't: excess realized as
routing shared among all blocks (see §4) survives any block pinning
untouched, so the recovered amount can be ~0 while the baseline drops by
`Θ(g·D)`. DEAD as stated.

## 3. The annulus law (the composition theorem to aim at)

**Setup.** Nested balanced wires `w ⊑ w'` on one chain, `S = varsOf w ⊂ S'
= varsOf w'`, bands `T < T'`. Define the annulus
`Ann(w, w') := cone(w') ∖ cone(w)` (a gate set) and its excess
`E_a := |Ann| − (|S'| − |S|)` (gates above the tree-cost of the new leaves).

**Conjecture (Annulus Factorization).** The induced map

    (rows of the S-cut) × (inputs read in S' ∖ S)  →  (rows of the S'-cut)

factors through `2^{j_a}` classes with `j_a ≤ E_a + O(1)`.

Intuition: everything the outer boundary knows is computed from (i) the
inner boundary's `2^j` row classes and (ii) gates living in the annulus;
new row diversity must be paid for by annulus gates alone. This is the
two-cut analogue of `cut_row_capacity` and is a genuinely NEW instrument —
nothing in rungs 1–21 conditions one cut on another.

**Why this composes.** Annuli of a nested chain are pairwise disjoint gate
sets BY CONSTRUCTION. So for any chain of bands `T_1 < T_2 < …`:

    Σ_i j_a(i)  ≤  Σ_i E_a(i) + O(#bands)  ≤  totalExcess + O(#bands).

The additive ledger is free. ALL difficulty moves into per-annulus row-
diversity lower bounds — and that is exactly what the 21-rung toolbox
produces, localized: patterns stored in `S' ∖ S`, probes outside `S'`,
private kit unchanged, pins drawn from blocks outside `S'`, live pin slot
by the squeeze. Expect per-annulus horn structure like rung 21's (the
straddle/heavy analysis recurs at each annulus — that is fine, it caps each
annulus at its own scale, not the sum).

**Payoff arithmetic (pressure-tested, honest).**
- Weak version: doubling scales `T, 2T, 4T, …` with `Ω(m)` diversity per
  annulus ⇒ `Σ = Ω(m log N) = Ω(√N · log N)`. A strict, CHEAP improvement
  over rung 21 — the right first validation target for the law.
- Strong version: bands spaced `Δ = Θ(v)` ⇒ `Θ(m)` annuli; per-annulus
  diversity target `Ω(Δ) = Ω(v)` ⇒ `Σ = Ω(m·v) = Ω(N)` ⇒
  `cbudget ≥ 2·live + Ω(N) = (2+c)·N`. This is HAL's step-1 target — IF
  §4 does not kill it first.

## 4. THE GATING PRESSURE-TEST: the sat3 upper-bound audit (do FIRST)

Designing the composition law exposed a threat that must be settled before
any Lean: **`(2+c)·N` may simply be FALSE for `sat3Family`.**

`sat3Family`'s only cross-block state is the shared `v`-bit assignment tail
(plus O(v) sign/tail structure). Each block needs data-DEPENDENT access to
assignment bits (its selectors choose which), which naively costs a `Θ(v)`
multiplexer per block ⇒ `Θ(m·v) = Θ(N)` extra — that would make `(2+c)N`
plausible. BUT the lookups of all `m` blocks can plausibly be served
TOGETHER by one shared sorting/routing network (bitonic / Beneš-style,
data-dependent control computed from the selectors) in `Õ(m + v) = Õ(√N)`
gates total. If such a circuit is valid in the CGate model, then

    cbudget(sat3Family) ≤ 2N + Õ(√N),

rung 21 is Θ̃-TIGHT, and NO composition theorem can reach `(2+c)N` for this
encoding — the strong annulus payoff would contradict a true upper bound,
so at least one of them fails, and the audit decides which.

**Audit task (paper math):** construct the explicit circuit — per-block
evaluators + shared assignment-routing network + AND-tree — and count its
cbudget and per-band coneExcess in the model's own accounting (exact CGate
fan-in/fan-out pricing matters and must be read off the definitions, not
assumed). Two outcomes:

- **(i) The routing circuit is valid and cheap.** Then `(2+c)N` moves to a
  REDESIGNED family (§5) and rung 21 stands as the tight answer for sat3.
  This would be a real result in itself: matching Θ̃(√N) bounds.
- **(ii) The model's wire accounting blocks the shared routing** (fan-out
  priced per wire-end, or CGate structural limits). Then `(2+c)N` is live
  for sat3 itself and the annulus law attacks it directly.

## 5. Dimension hierarchy = scaling the shared state (HAL step 3, reframed)

The reason sat3 caps near `√N` crossing-information: only `v = Θ(√N)` bits
are global; everything else is block-local. The hierarchy family should
make shared state scale with `N`: `k = Θ(m)` coupled assignment copies
with cross-consistency constraints between copies, arranged so that at
every scale `s`, balanced cuts of size `s` must carry `Ω(s)` bits that
cannot be locally summarized. Requirements to respect:

- crossing-info `Ω(s)` at every scale is superconcentrator-like; it can
  force at most LINEAR total wires by itself (superconcentrators have
  linear-size constructions — the classical Valiant lesson), which is
  exactly the `(2+c)N` regime and no more. Beyond-linear needs a new
  idea beyond information flow; do not claim otherwise;
- the family must stay NP-verifiable (a real SAT relative) or the step-5
  escape loses its target;
- the adversary walls already mapped (straddle channel, pool cap,
  Zarankiewicz spread) recur at each level — each level's charge is capped
  at that level's pool scale, which is exactly why the hierarchy's levels,
  not any single level, must carry the total.

### 5b. The expander coupling (where Ramanujan legitimately enters)

HAL's proposal: connect the copies by a bounded-degree Ramanujan expander
`G` on `k` nodes; edge `(i,j)` carries a partial-consistency check (copies
`a_i, a_j` must agree on a window `W_ij ⊂ [v]`, `|W_ij| = w₀`). The honest
mechanism, stated against the rung-20 blocker:

> In sat3, ONE straddling block can lawfully carry `v` mass — reuse is
> unbounded, so all cuts recharge the same straddlers. On a `d`-regular
> expander coupling, one straddling gadget can absorb at most `d`
> edge-charges — **reuse is bounded by degree**. Spectral expansion
> (`λ ≤ 2√(d−1)`) gives edge-boundary `Ω(d·s)` for every node-set of size
> `s ≤ k/2`, with controlled overlaps — so a balanced cut at node-scale
> `s` must cross `Ω(s)` independent edge-checks, and at most a `1/d`
> fraction can be absorbed by any one gadget. Charges add up to a
> constant factor.

Target composition lemma (the shape HAL asked for, made precise):

    (local edge law: each cut separating copies i,j prices Ω(w₀) rows
     for the edge (i,j))
    + (G Ramanujan, d-regular on k nodes)
    + (annulus ledger of §3)
    ⇒ total excess ≥ Σ_scales Ω(s·w₀)-per-annulus ≥ Ω(k·w₀·c_d)
    with k·w₀ = Θ(N) by parameter choice ⇒ cbudget ≥ (2+c)·N.

Three honest caveats, so this stays a rung and not a leap:

1. **The expander does NOT rescue flat-bus sat3.** Routing networks are
   universal — an `Õ(m+v)` router serves expander-shaped demand as cheaply
   as flat demand, so restructuring WHO reads the `v`-bit tail changes
   nothing (§4 still gates). And hard-wiring the neighborhoods into the
   function (fixed selectors) collapses the family to fixed-formula
   evaluation — general circuit lower bounds, the P≠NP-strength wall
   (Tseitin-on-expander territory: width bounds real, size bounds = the
   wall; see the BSW kernel finding). The expander must live in the
   FAMILY's consistency structure (data still selects, demands stay
   `Θ(N)`-bit), not in the wiring diagram.
2. **The annulus factorization (§3) is still load-bearing.** Expansion
   makes per-scale demands non-localizable, but without the annulus ledger
   nested cuts can still bill one shared excess pool. Both lemmas are
   needed; neither implies the other.
3. **Ramanujan buys constants, not the mechanism.** Any spectral expander
   gives the composition; Ramanujan optimizes `d` vs `λ` so the `1/d`
   reuse loss is minimal. Use LPS/explicit constructions at spec time;
   don't let optimality claims creep into the statement.

## 6. Order of work

1. **Upper-bound audit of sat3Family** (§4) — paper math, decides the
   target family; it is also the audit template for the expander family
   (which needs its own honest upper bound before any lower-bound claim).
   No Lean.
2. **Precise statement of the Annulus Factorization** (§3) against the
   actual CutFactorization/mixOn definitions; pressure-test on the
   caterpillar and on the §4 routing circuit. No Lean.
3. **Expander-family specification** (§5b): parameters `(k, d, w₀, G)`,
   NP-verifiability check, its upper bound, and the local edge law drafted
   with the existing drag/window toolbox. No Lean.
4. If 1–3 survive: **rung 22 = weak annulus validation**
   (`Ω(√N log N)` via doubling scales, flat sat3) — first Lean of the new
   phase, validating the ledger before the expander family raises stakes.
5. Then the expander composition lemma toward `(2+c)N` on whichever
   family 1–3 select.

## 7. Honest scope

Everything here is the restricted wire model. Steps 4–5 of the roadmap
(observer-captures-P, NP escape) are untouched and remain the
P≠NP-strength bridges; nothing in this document reduces them. The annulus
law is a conjecture until proved; §4 may falsify the `(2+c)N` target for
sat3Family specifically, and if it does, that finding must be reported as
the result, not worked around. Nothing here is NEXP ⊄ ACC⁰ or P ≠ NP.
