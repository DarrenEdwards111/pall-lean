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
`Ann(w, w') := cone(w') ∖ cone(w)` (a wire set) and its excess `E_a` in the
model's own currency — excess fan-out attributed to annulus wires (precise
form fixed by the audit, §4(d)); annuli of a chain then partition the root
cone's wires and `Σ_a E_a ≤ coneExcess(root)` is an identity.

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

## 4. THE UPPER-BOUND AUDIT — RESOLVED: threat withdrawn, `(2+c)N` is live

**Audit performed against the actual definitions**
(`ComputationalDepthNFrameSATTarget.lean`,
`ComputationalDepthNFrameCircuitUpgrade.lean`,
`ComputationalDepthNFrameSlotConnectivity.lean`). Findings:

**(a) The threat scenario rested on a misreading and is withdrawn.**
`sat3Family N x = decide (∃ a : Fin v → Bool, sat3Eval N x a)` — it is
GENUINE SATISFIABILITY. The input `x` encodes only the instance (`m`
clauses × 3 slots × (`v` selectors + sign)); the assignment is
existentially quantified over all `2^v` candidates and is NOT part of the
input. (The "assignment tail" this section previously assumed does not
exist — the ledger's `3v+3` slack term is the `N mod D` remainder junk.)
The `Õ(m+v)` routing circuit routes lookups into an input tail that isn't
there; it does not compute `sat3Family`. No cheap upper bound follows.

**(b) Honest upper-bound status.** Best known construction is brute force
over assignments: `cbudget(sat3Family) ≤ 2^v · poly(N) = 2^{Θ(√N)}`. The
encoding is genuinely NP-hard-shaped: singleton selectors embed arbitrary
sparse 3-CNF over `v` variables with `m ≈ v/3` clauses, so polynomial-size
circuits for the family (at scale) are an NP ⊆ P/poly-strength event. Every
target on the amplification ladder — `(2+c)N`, superlinear, polynomial —
is consistent with the function's expected complexity.

**(c) Consequence: rung 21 is NOT tight, and the `Ω(√N)` ceiling is in the
INSTRUMENTS, not the function** — the pool cap (rung 8) and the straddle
channel (rung 20) are limits of the pin machinery; no circuit realizing
`2N + Õ(√N)` was ever exhibited, and none is expected to exist. The
composition program attacks flat sat3 directly; no family redesign is
forced.

**(d) Model facts fixed by the audit (for the annulus statement).** CGate
circuits have FREE fan-out (gates read earlier wires by index); `cbudget`
counts gates; `coneExcess c root = Σ_{w ∈ cone∖{root}} (#readers(w) − 1)`
is total EXCESS FAN-OUT, and the proven ledger is
`2·m·D + coneExcess(root) ≤ cbudget + 1` (`sat3_excess_priced`). Rung 21's
band bound is a lower bound on the ROOT's excess — every band charges the
same global quantity, which is exactly the reuse problem §3 addresses. The
annulus excess must therefore be defined in fan-out currency:
`E_a := Σ_{w ∈ cone(w')∖cone(w)} (#readers-in-root-cone(w) − 1)`, with
each excess read attributed to the annulus of the wire being READ; then
annuli of a chain partition the cone's wire set and
`Σ_a E_a ≤ coneExcess(root)` is exact — the additive ledger is an identity,
and the whole burden is the factorization conjecture plus per-annulus
diversity.

## 5. Dimension hierarchy / expander family — now ROUTE B, not forced

The §4 audit removed the original motivation (tightness-fear for flat
sat3): the `Ω(√N)` ceiling is in the pin INSTRUMENTS (pool cap, straddle
channel), not in the function, so the primary target of the composition
program is flat sat3 itself. The family redesign below stays on the board
as Route B — a vehicle on which the composition may be strictly EASIER to
prove, because its coupling structure is engineered for exactly the
additivity the tools need. The idea: `k = Θ(m)` coupled assignment copies
with cross-consistency constraints between copies, arranged so that at
every scale `s`, balanced cuts separating copies must carry `Ω(s)` bits
that cannot be locally summarized. Requirements to respect:

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

1. **Upper-bound audit of sat3Family** — DONE (§4). Verdict: threat
   withdrawn; `sat3Family` is genuine ∃-SAT with brute-force upper bound
   `2^{Θ(√N)}`; `(2+c)N` and everything above it is live for flat sat3;
   rung 21 is instrument-capped, not function-capped.
2. **Precise statement of the Annulus Factorization** (§3, currency fixed
   by §4(d)) against the actual CutFactorization/mixOn/coneExcess
   definitions; pressure-test on the caterpillar. This is now the sole
   load-bearing new instrument. No Lean until the statement survives.
3. If 2 survives: **rung 22 = weak annulus validation**
   (`Ω(√N log N)` via doubling scales, flat sat3) — first Lean of the new
   phase, validating the ledger at low stakes.
4. Then the dense chain (`Θ(m)` annuli spaced `Θ(v)`) toward `(2+c)N` on
   flat sat3.
5. Route B in parallel if 2 stalls: expander-family specification (§5b) —
   parameters `(k, d, w₀, G)`, NP-verifiability, its own honest upper
   bound, local edge law from the drag/window toolbox.

## 7. Honest scope

Everything here is the restricted wire model. Steps 4–5 of the roadmap
(observer-captures-P, NP escape) are untouched and remain the
P≠NP-strength bridges; nothing in this document reduces them. The annulus
law is a conjecture until proved; §4 may falsify the `(2+c)N` target for
sat3Family specifically, and if it does, that finding must be reported as
the result, not worked around. Nothing here is NEXP ⊄ ACC⁰ or P ≠ NP.
