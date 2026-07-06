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

**Theorem candidate (k-scale trace capacity) — statement verified against
the actual definitions (task 2, DONE).** Let `w_1 ⊑ w_2 ⊑ … ⊑ w_k` be a
nested chain of wires (each in the next's cone; such chains exist at all
prescribed size bands along the max-child root-to-leaf path, since
`|varsOf|` at most doubles child→parent — a routine new selection lemma).
Set `S_i := varsOf w_i`, `Ann_i := coneOf w_i ∖ coneOf w_{i−1}`, and
`a_e(i) := #(wireExits(w_i) ∩ Ann_i)`. Then for any family `Y` of rows
pairwise distinguished at SOME scale (for each pair, ∃i and an
`S_iᶜ`-probe separating them):

    |Y| ≤ 2^{ |wireExits(w_1)| + Σ_{i≥2} a_e(i) }
    with   Σ_{i≥2} a_e(i) ≤ coneExcess(root) + (k−1).

**The proof mechanism is nearly free — pure coordinate counting.** The key
containment: `wireExits(w_i) ∩ coneOf(w_{i−1}) ⊆ wireExits(w_{i−1})` (a
reader outside `cone(w_i)` is outside `cone(w_{i−1})`, by `cone_trans` —
one easy lemma). So the joint trace vector `(φ_1(y), …, φ_k(y))` has, at
scale `i`, only `a_e(i)` coordinates not already present at scale `i−1`:
its range is at most `2^{j_1 + Σ a_e(i)}` — no functional analysis of the
annulus computation is needed at all (my earlier worry about duplicate
var-gates was a phantom: duplicates feed the trace's VALUES, they do not
add trace COORDINATES). Per-scale `CutFactorization` is the existing
`sat3_wire_cut_factorization`; the ledger `Σ (a_e(i) − 1) ≤ coneExcess` is
the existing `wireExits_card_le` argument localized (each non-top exit in
`Ann_i` has an inside and an outside reader, hence is multi-read; the
`Ann_i` are disjoint, and `Σ #multiread(Ann_i) ≤ coneExcess(root)`). This
is real, provable infrastructure: it makes the excess ledger ADDITIVE
across scales, permanently.

### 3b. The pressure-test verdict: the diversity side caps at `Θ(v)` —
### annuli buy constants and infrastructure, NOT `(2+c)N`

Running the forcing arithmetic honestly against the toolbox kills the
payoff claims of the previous revision (both of them), for one reason:

**The pin channel dies exactly at the `Θ(v)` threshold, at every scale
simultaneously.** The min-form dichotomy is a two-sided weapon: at a
moderate band (`|S_i| = εN`), `Q_t(S_i) ≥ j_i + 3` forces the slot-full
horn `m·(v − j_i) ≤ |S_i|`, i.e. `j_i ≥ v(1 − 6ε)` — so an adversary who
poisons any moderate cut's sign columns beyond `j_i + 2` has ALREADY paid
`coneExcess = Θ(v)`. Conversely, while `CE ≲ v/2`, every moderate cut has
a live slot and all instruments run. But that is precisely the trap: every
diversity instrument in the pin paradigm is APPLICABLE only while
`CE ≲ v/2` (pin room `|W| + 2|C| + Q ≤ m` with `Q ≤ CE + 3`), so the
contradiction argument can push `CE` only up to its own applicability
threshold. With the k-scale capacity in place the assembly reads
`Θ(N) ≤ CE + 2k` under the hypothesis `CE ≲ v/2` — which refutes the
hypothesis and yields `CE ≥ ~v/2`, i.e. `Θ(√N)` with a better constant
(≈9× the rung-21 horn `m ≤ 6j+48`), and nothing more. The same analysis
invalidates the previous revision's `Ω(√N log N)` doubling-scales claim —
per-annulus charges are not independent of the global poison budget; they
all share the same `Θ(v)`-threshold pin supply. And partial-row windows
(`V_c := W ∩ S-row(c)`, admissible in `sat3_private_window` as stated)
change constants, not the exponent: the `hroom` coupling of poison and
pool self-caps them identically.

**So the honest theorem reachable from the annulus law on flat sat3 is:**
`coneExcess ≥ ~v/2 = Θ(√N)` uniformly (constant-factor upgrade of rung 21)
PLUS the additive-capacity infrastructure. `(2+c)·N` requires a diversity
channel that survives total sign poisoning — a PINLESS channel carrying
`ω(1)` bits per block. The only pinless channel in the toolbox (rung 18's
emptiness channel) carries exactly 1 bit per block, `Θ(m)` total. That is
the true frontier, stated exactly.

**Consequence for Route B (re-elevated to the `(2+c)N` path).** The pin
bottleneck is an ARTIFACT OF THE ENCODING: probes must be synthesized from
pool clauses, and the pin machinery is guarded by only `3m` sign bits. A
redesigned family can build the probe channel into the function — e.g. a
per-gadget "probe port" (an input bit that satisfies its gadget outright,
or richer per-gadget control words), making per-gadget diversity readable
WITHOUT pool pins. The adversary's counterplay against ports (absorb them
into `S`) converts them into free pattern bits instead of killing the
channel — the port design goal is exactly this no-lose dichotomy, and it
needs careful specification (task 3). With an unpoisonable channel
carrying `Θ(v)` bits per gadget, the k-scale capacity (§3) turns the
per-gadget charges additive: `Θ(m)` annuli × `Θ(v)` bits ⇒
`coneExcess = Ω(N)` ⇒ `cbudget ≥ (2+c)N` — on the redesigned family, with
the expander coupling (§5b) preventing gadget-reuse across scales.

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
   `2^{Θ(√N)}`; rung 21 is instrument-capped, not function-capped.
2. **Annulus Factorization statement + pressure-test** — DONE (§3/§3b).
   Verdict: the k-scale trace capacity is real and nearly free
   (coordinate counting over nested exit sets); it makes the excess
   ledger additive permanently. BUT the diversity side of the pin
   paradigm caps at `Θ(v)` — the poison/full dichotomy is a global
   constraint shared by all scales — so on flat sat3 the law buys a
   ~9× constant and infrastructure, not `(2+c)N`. The previous
   revision's `Ω(√N log N)` and flat-sat3 `(2+c)N` payoff claims are
   WITHDRAWN.
3. **Rung 22 — DONE (`aa9514b5`,
   `ComputationalDepthNFrameAnnulusCapacity.lean`):** `wireExits_nested`,
   `exit_multiread`, `chain_union_card`, `chain_exit_ledger`
   (`Σ newExits ≤ coneExcess + (k+1)`, disjoint annuli),
   `exit_value_separation` (trace exposed as exit values — the form that
   composes; the `∃φ` CutFactorization form does not),
   `sat3_chain_capacity_excess` (`|Y| ≤ 2^{coneExcess + k + 1}`),
   `balanced_chain_exists` (recurse `balanced_wire_exists` inside the
   previous cone — no path formalization needed), and the packaged
   `sat3_annulus_capacity`. All on `[propext, Classical.choice,
   Quot.sound]`, no sorry. The Θ(v) diversity cap is stated in the file's
   docstring so it cannot be silently resurrected.
3b. **Rung 23 — DONE (`4caf0835`,
   `ComputationalDepthNFramePartialRowBound.lean`):** the honest
   flat-sat3 consequence —
   uniform `coneExcess ≥ ~Θ(v)` with visible applicability threshold,
   explicitly NOT `(2+c)N`. Blueprint: partial-row window instantiation
   (`V_c := W ∩ S-row(c)` in the rung-20 parametric window) + two-stage
   MARKOV selection for the greedy rectangle (no sorting needed: heavy
   blocks = rowmass ≥ A/2m; if enough heavy blocks, any `γm` of them
   carry `γA/2`; else heavy mass alone is `≥ A/2` — repeat on columns)
   + the per-slot dichotomy tree of rung 21 with the full-mass-three
   escape.
4. **Task 3 — DRAFTED (`PROBE_PORT_FAMILY.md`): the expander-affine
   family `sat3X`.** Literals = affine functionals `(λ, b)`, `λ ∈ Λ =
   singletons ∪ expander edges` over the hidden witness `a ∈ F₂^v` — NO
   sign bits; negation is by position; forcing is redundant through
   `Λ`-decompositions, so no `O(m)`-sized guardian set exists (kill-cost
   `Θ(m)` per functional, expander-closure amplified, `Θ(N)` total).
   Four checks audited; naive per-bit no-lose REFUTED (dual-rail
   counterexample) and replaced by the kill-cost form. GATE before any
   Lean: the kill-cost lemma (closed dead sets on the expander), the
   forcing-consistency lemma, and a red-team round (§5 of the spec).
5. Only after that: superlinear targets and the P-side bridges (§7).

## 7. Honest scope

Everything here is the restricted wire model. Steps 4–5 of the roadmap
(observer-captures-P, NP escape) are untouched and remain the
P≠NP-strength bridges; nothing in this document reduces them. The annulus
law is a conjecture until proved; §4 may falsify the `(2+c)N` target for
sat3Family specifically, and if it does, that finding must be reported as
the result, not worked around. Nothing here is NEXP ⊄ ACC⁰ or P ≠ NP.
