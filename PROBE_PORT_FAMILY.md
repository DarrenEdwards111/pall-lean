# Route B: the expander-affine family `sat3X` — probe-port specification

Status: PAPER DESIGN (task 3 of COMPOSITION_DESIGN.md). No Lean. This is the candidate
"missing diversity channel" family: SAT-like, with an unpoisonable `Θ(v)`-bit forcing
channel per gadget, targeted at `CE = Ω(N)` ⇒ `cbudget ≥ (2+c)N` through the frozen
engine (rungs 1–23, in particular the rung-20 window/drag pattern and the rung-22
additive capacity).

## 0. The root cause to remove, stated exactly

In flat sat3 the probe reads a data block's pattern by FORCING assignment variables,
and forcing a variable FALSE requires a negative literal — negation lives solely in
the `3m` sign bits. That is the entire poison ceiling: a `Θ(m)`-sized guardian set
(one bit per block-slot) whose occupation by `S` kills every instrument, and which
the adversary can afford whenever it is willing to pay `Θ(v)` excess (the rung-23
horns make this exact). **Design principle: no `O(m)`-sized guardian set may exist.
Negation must be structural, redundant, and `Θ(N)`-expensive to kill.**

## 1. The family

Fix `v` (hidden-witness width), a `d`-regular Ramanujan graph `G` on vertex set
`[v]` (`d` a fixed constant, LPS or any explicit spectral expander), and the
**functional set**

    Λ := { e_w : w ∈ [v] } ∪ { e_w + e_{w'} : (w,w') ∈ E(G) }   ⊆ F₂^v,
    |Λ| = v + d·v/2 = Θ(v).

A **literal** is a pair `(λ, b) ∈ Λ × F₂`, true under witness `a ∈ F₂^v` iff
`⟨λ, a⟩ = b`. Note `(λ, b)` and `(λ, 1−b)` are complementary literals — **negation
is by position, not by a sign bit. The encoding has NO sign bits.**

**Input layout.** `m` blocks ("gadgets"), each of `D' = 3 · 2|Λ| = 3(2+d)·v` bits:
3 slots, each slot a characteristic vector of a set `T ⊆ Λ × F₂` of selected
literals. Additionally the constant functional `λ = 0` is allowed in `Λ` (giving
per-slot tautology `(0,0)` and contradiction `(0,1)` selectors — the intrinsic
neutralization kit). `N = m·D' = Θ(m·v)`; with `v = Θ(√N)`, `m = Θ(√N)` — the same
shape the engine is calibrated for.

**Semantics.**

    sat3X N x := decide (∃ a : F₂^v,  ∀ block c,  ∃ slot t,
                          ∃ (λ,b) selected at (c,t) :  ⟨λ, a⟩ = b).

Clause = OR of 3 slots; slot = OR of its selected affine literals; instance = AND
of clauses; the witness is existential. Structurally parallel to `sat3Family`
(the engine's block/slot machinery transfers), with literals upgraded from
signed variables to expander-affine functionals.

## 2. The probe channel and why it cannot be poisoned

**Forcing.** A "pin" is a pool block whose slot selects the single literal
`(λ, b)`: any satisfying witness has `⟨λ, a⟩ = b`. Forcing `⟨λ,a⟩ = 0` uses
position `(λ,0)`; forcing `= 1` uses `(λ,1)` — different POSITIONS, so there is no
per-block mode bit for the adversary to buy (the rung-19 discovery — only
mode-dependent bits are poisonable — is designed into the encoding: nothing is
mode-dependent).

**Redundancy (where Ramanujan enters).** `λ` is *directly* pinnable at a pool block
`p` iff `p` has a free `(λ, ·)` selector position. It is *indirectly* forcible via
any decomposition within `Λ`:

    e_w = (e_w + e_{w'}) + e_{w'}          (any neighbor w', d ways),
    e_w + e_{w'} = (e_w + e_u) + (e_u + e_{w'})   (any common neighbor u),

and pinning a set of functionals forces every functional in their span (choose the
pinned family linearly independent; the linear system stays consistent).

**The kill-cost claim (the design's load-bearing lemma — to be proved on paper
next).** Call `λ` DEAD if the probe cannot force its value. Deadness must be closed
under decomposition: `e_w` dead requires, for EVERY neighbor `w'`, that
`e_w + e_{w'}` is dead or `e_{w'}` is dead. Killing any single functional directly
costs `Θ(m)` S-bits (all its selector positions across the pool); the closure
requirement propagates along `G`, and on a spectral expander any closed dead set is
either huge (`≥ ζ·v` singletons ⇒ cost `Θ(m·v) = Θ(N)`, unaffordable at any
moderate band) or must kill `≥ d/2` incident pair-functionals per dead singleton
(cost `Θ(d·m)` per kill). Consequence:

    with |S| ≤ 2T−2 = Θ(εN), at most O(ε)·v functionals die;
    the LIVE channel keeps Θ(v) functionals at every balanced cut.

There is no `Θ(m)`-sized guardian set anywhere: the guardian set of a single
functional is `Θ(m)` positions PLUS its expander closure, and of the channel as a
whole is `Θ(N)`.

**The no-lose dichotomy, honest form.** It is NOT a naive per-bit 1:1 leak (an
earlier draft of this idea fails: burial in fully-dead company leaks only the
per-slot emptiness bit — the dual-rail version of this family dies exactly there).
The correct statement is two-part:
- selector bits the adversary buries at DATA blocks are priced by the drag even
  when they select dead functionals, provided their pattern-company is live
  (detection: force the live companions to 0 via complements/decompositions —
  avoiding the target's span — and let the ∃ pick the free target rail);
- selector bits buried at POOL blocks are not priced directly, but they are
  exactly the kill-cost purchase, and the kill-cost claim caps what they buy.

## 3. Why the engine then closes (the cash-out sketch)

At a balanced cut `S` (band `T = εN`):
1. Markov block-selection (rung 23's `markov_select`, unchanged): `C` = `m/8`
   heaviest blocks captures `≥ 1/8` of the S-mass; pool = the rest.
2. Live channel: `Θ(v)` functionals with clean pin blocks in the pool (kill-cost
   claim). `W` := live functionals; patterns `V_c := W-positions ∩ S-row(c)`.
3. Detection of any single differing position `(c*, (λ,b))`: neutralize other
   blocks by the intrinsic tautology kit (mode-independent — rides with rows in
   `S`, with probes in `Sᶜ`; unpoisonable by construction); force the pattern
   companions to 0 via live complements/decompositions, span-avoiding `λ`; the
   target slot is then satisfiable iff the position is selected.
4. Capture: `j ≥ Θ(S-mass in C×W) = Θ(T)` — **the rung-23 capture horn with the
   poison horns DELETED**: `hroom`'s `Q ≤ j+2` coupling does not exist (liveness
   comes from expansion, not from a squeeze), so the applicability threshold that
   capped flat sat3 at `Θ(m)` is gone.
5. One band at `T = εN` gives `CE ≥ Θ(N)` ⇒ `cbudget ≥ 2·live + Θ(N) = (2+c)N`.
   Rung 22's additive capacity is then the robustness/constant tool across scales
   (`Σ_i Θ(Δ_i) ≤ CE + 2k`), not the existence tool — the single-cut version may
   already suffice on this family. Both routes should be kept.

## 4. The four checks (HAL's list) — audit record

1. **No-lose probe-port dichotomy** — HOLDS in the refined form of §2: port
   positions outside `S` are probe entrances; positions inside `S` are either
   priced pattern bits (data company) or kill-cost purchases capped by expansion.
   The naive 1:1-leak version is FALSE and was discarded (dual-rail counterexample:
   fully-dead company leaks only emptiness).
2. **Pinless diversity** — holds in the honest sense: SIGN-FREE and redundantly
   pinned. There are no sign columns to poison; "total sign poisoning" is not a
   move that exists against this family. Forcing still uses pool blocks, but no
   `o(N)` purchase kills it.
3. **Expander coupling** — the expander's role is kill-cost amplification
   (closed dead sets are huge), which is the single-cut fix; cross-scale
   freshness is supplied independently by rung 22. Ramanujan optimizes `d` vs
   expansion constants only.
4. **Hardness + upper bound** — singleton selectors (`λ = e_w`) embed arbitrary
   sparse 3-CNF verbatim, so `sat3X` is NP-hard-shaped exactly as flat sat3;
   honest upper bound remains brute force `2^v · poly(N) = 2^{Θ(√N)}`.
   Cheap-trick audit: (i) purely-affine subfamilies (unit slots) are XOR-SAT =
   polynomial — harmless, hardness lives in the OR structure; (ii) the affine
   literals give Gaussian-elimination power to algorithms — no known route to
   subexponential SAT from it, but this is the check to keep open; (iii) the
   function is still `∃`-SAT — no input-side assignment to route (the audit
   mistake of the flat-sat3 §4 episode is not repeated).

## 5. Open items before any Lean (the honest gate)

1. **The kill-cost lemma** (§2) — precise statement and proof: "every
   decomposition-closed dead set `D ⊆ Λ` with fewer than `ζv` dead singletons
   satisfies `cost(D) ≥ c·d·m·|D|`", via vertex/edge expansion of `G`. This is
   the load-bearing new mathematics; everything else is engine-shaped.
2. **The forcing-consistency lemma**: pin families can be chosen linearly
   independent, covering any `≤ k₀` live targets' values, span-avoiding any one
   designated functional (needed for step-3 detection). Should be routine linear
   algebra + greedy over `G`, but must be written.
3. **The eval layer** (future Lean rungs 24+): the multi-block kit/eval machinery
   rebuilt over affine literals — the `∃ a ∈ F₂^v` with a forced independent
   family evaluates by coset analysis. Mechanical but sizable; the 21-rung
   playbook applies (staged lemmas, pressure-test before build).
4. **The engine's f-generic re-instantiation**: root shape, essential variables,
   balanced cuts, exit machinery for `sat3X` (mostly generic already; `sat3X`
   root-shape and essential-variable lemmas are the sat3-specific mirrors).
5. **Adversary red-team round**: the checks above were run by the designer; a
   fresh pass should specifically attack (a) the span-avoidance requirement at
   high pattern width, (b) mixed live/dead pattern company at extreme mass
   concentrations, (c) whether `S` can sit disproportionately on `Λ`-pair
   positions to distort the live-set structure cheaply.

## 6. Honest scope

This is a design, not a result. If the kill-cost lemma survives, the target is
`cbudget(sat3X) ≥ (2+c)N` in the restricted CGate model — a restricted-model
constant-factor lower bound for an NP-hard-shaped explicit family, NOT a
superlinear bound, NOT `P ≠ NP`. The observer-captures-P and NP-escape bridges
(roadmap steps 4–5) are untouched. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# KILL-COST AUDIT (task 3b): the three layers, run to the end

## Layer 1 — dead-closure, algebraically (ANSWERED)

The right closure is **affine-span closure of the pinnable literal set**, not graph
closure: let `V ⊆ Λ×F₂` be the directly pinnable literals (a free selector position
at enough pool blocks/∧-rows). Forcible literals
`F := {(μ,c) : ∃ independent {(λᵢ,bᵢ)} ⊆ V, μ = Σλᵢ, c = Σbᵢ}`. The graph enters
only through Λ's sparsity: PIN-RICH := {λ : both values in V}; if PIN-RICH spans
F₂^v, everything is forcible. Killing r dimensions of span(PIN-RICH) requires a
half-killed literal set X with dead-dimension vertex set A (|A| ≥ r) satisfying
`X ⊇ {e_w : w ∈ A} ∪ E(A, Aᶜ)`.

## Layer 2 — the expansion alternative (PROVED, sketch)

Spectral expansion gives `e(A, Aᶜ) ≥ (d − λ₂ − o(1))·|A|` for `|A| ≤ v/2`, so
`|X| ≥ (1 + d − λ₂)·|A|` — **no bulk discount**; and `|A| > v/2` costs
`Θ(m·v) = Θ(N)` outright. Per-literal direct-kill cost `≥ (9/4)m` S-bits. This is
the lemma as targeted, and it is TRUE.

## Layer 3 — red-team verdict: the lemma is true but INSUFFICIENT

**The parity-locked refuge (attack (b), generalized) breaks the cash-out.** The
adversary buys a small dead sector (r = Θ(εv/d) dimensions, cost Θ(ε·N)) and hosts
ALL of its balanced mass on ∨-slot positions of dead-sector functionals, killing
exactly the complements of the hosted literals. Inside the refuge, suppression is
impossible and the ∃-witness's free directions wash out all content beyond the
per-slot emptiness bit (Θ(m) total). The accounting is UNFIXABLE by parameters:
hosting capacity and kill cost are both counted in selector-positions-per-functional
(Θ(m) each), and

    capacity/cost = (3(1+d) + (9/4)(1+d−λ₂)) / ((9/4)(1+d−λ₂)) ∈ [2.6, 4.3]
    (d = 8..128, Ramanujan; alive-side alone ≥ 1.4 for all d)

— always ≥ 1, so the refuge is always affordable. Repair attempts audited and
CLOSED: R-fold selector repetition (scales both sides); ∧-blocks/unit-clause pins
(adversary hosts at ∨-blocks only); always-on affine isolation rows with no-lose
coefficients (real, but per-pair forcing routes through the port CONSTANTS —
`Θ(v)` bits — and hash-indirection is pigeonhole-bottlenecked at `2^{Θ(v)}`,
pricing only Θ(v) of Θ(T) hosted mass).

**The structural conclusion:** for ∃-witness families with witness size `Θ(√N)`
read through coset probes (pins = affine slices), the dead-sector refuge is
GENERIC: content whose functionals lie entirely in the witness's unforced
directions is maximization-washed, and every port that could reach it is
information-bottlenecked by the witness size. **The `Θ(v)` per-cut cap is a
property of ∃-semantics + witness size, not of flat sat3's encoding.** sat3X as
an ∃-family does NOT reach `(2+c)N`.

## Surviving directions (honest ranking)

1. **Parity semantics — `sat3X⊕` := parity of #satisfying assignments.** The ⊕
   over the free coset SUMS instead of maximizing: dead-direction content stays
   visible pointwise. This is the only audited route that dodges the wash-out
   mechanism itself. Cost: the family is ⊕P-shaped; NP-relevance via
   Valiant–Vazirani-style randomized reduction only — check 4 is weakened and the
   roadmap's step-5 story must be reworked if this route is taken. The kill-cost
   lemma (layer 2) remains load-bearing here — forcing/liveness is still how the
   probe steers the coset it sums over.
2. **Witness-size escalation** (`v = Θ(N/polylog)` hidden state): the refuge
   costs `Θ(r·d·m)` per dimension with `m` blocks each `Θ(v)` wide — geometry
   changes entirely; unexplored, may break the engine's band calculus.
3. **Accept the ∃-cap as fundamental** and move the amplification to a different
   layer (function composition rather than cut composition) — outside the
   current engine.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# sat3X⊕ AUDIT (task 3c): parity defeats the refuge — mechanism exact

## Framing (per the agreed roadmap)

`sat3X⊕ N x := (#{a ∈ F₂^v : instance(x) satisfied by a}) mod 2` — same layout as
sat3X (blocks, slots, affine expander literals, tautology kit; the contradiction
selector `(0,1)` is REMOVED from the encoding, see attack 2). Target: restricted
lower bound for an explicit parity/#P-shaped family. NP bridge deferred/conditional
(Valiant–Vazirani-style isolation). Not P ≠ NP.

## The parity computation (why the eraser becomes the signal)

With other blocks kit-neutralized (factor ≡ 1 — parity-neutral) and pins `P` as
unit-clause factors, the whole count collapses to an affine solution count:

    F = (2^{v−|P|} − Z) mod 2 = Z mod 2   (|P| < v),
    Z := #{a : pins hold ∧ ALL selected literals of block c* FALSE}
       = 0 or 2^{v − rank(joint system)}.

Under ∃, free witness directions were the eraser (maximization washes content).
Under ⊕, free directions force `Z` EVEN, i.e. `F = 0` — and the target literal's
arrival flips the count to odd exactly when it completes the rank:

**Parity rank-completion lemma (statement-stable; numerically verified 243/243
after correction).** If the functionals of `P ∪ T` are jointly independent with
`|P ∪ T| = v − 1`, and `λ*` is independent of them, then
`F(P, T) = 0` and `F(P, T ∪ {(λ*, b)}) = 1` — **for both values of `b`.**
Value-independence kills the parity-lock: the refuge's whole mechanism (killing
complements so values can't be steered) is irrelevant, because detection never
steers a value — the target literal itself supplies the missing rank.

## The refuge, re-run under ⊕ — IT FAILS

Adversary buys dead sector `A` (`r_d` dims), hosts all mass on dead-functional
positions. Detection of a hosted position at data block `c*`: pins span the live
directions (kill-cost lemma — the scout file's lemmas are load-bearing here,
exactly as predicted); the SCAFFOLD (dead-direction singletons at `c*`) completes
`v − 1` dimensions, missing only a direction the target hits. Scaffold positions
are a genuine no-lose: outside `S` the probe supplies them; inside `S` the row
supplies them as constants — and by value-independence the constants' VALUES no
longer matter, closing the loophole that killed the isolation-row repair in the
∃-audit. `F` flips on the target: hosted dead-company mass is priced.

## New cancellation attacks found (the second half of the audit)

1. **Dependent hosting (REAL — found numerically: 24/53 failures of the naive
   lemma).** Hosting both values of one functional, tautology selectors, or
   span-trapped literals makes the all-false system inconsistent: `Z = 0` on both
   sides of a pair — undetectable. DISPOSITION: the independence discipline. Rows
   price `V_c` := an independent transversal of the hosted positions; positions
   per functional per block = 6 and Λ's circuits are cycle-shaped, so
   `rank ≥ mass/12` — a constant-factor loss, then 243/243 detection.
2. **Contradiction-selector positions** `(0,1)`: never satisfiable, never
   detectable — `Θ(m)` dead loss. DISPOSITION: removed from the encoding (also
   repairs essential-variables for the `2N` baseline).
3. **Kit under parity**: tautology factor ≡ 1 is parity-neutral ✓; kit positions
   remain mode-independent/no-lose ✓ (unchanged from the ∃-analysis).
4. **Pin sabotage**: unchanged — pins are still needed to span the LIVE
   directions, so the kill-cost/expansion lemmas (layer 2, scout file) carry over
   verbatim. The dead sector stays `O(εv/d)`-dimensional; the scaffold covers it.

## Engine consequences (the paper cash-out for sat3X⊕)

The flat-sat3 case tree COLLAPSES: no sign columns exist, so no squeeze, no
dichotomy, no poison horns. What remains: Markov block/column selection (rung 23,
generic), kill-cost liveness (scout lemmas + expander instantiation), independence
transversal (matroid, factor ≤ 12), rank-completion detection (above), and the
generic capacity (`cut_row_capacity` is f-generic; rung-22 additivity for
robustness). Chain: `j ≥ Θ(S-mass at C-blocks)/const = Θ(T)` at any moderate band
⇒ `CE = Θ(N)` ⇒ `cbudget(sat3X⊕) ≥ 2·live + Θ(N) = (2+c)N`.

## Gate before Lean (round 2 of red-team, then the scout)

- Generalize the rank-completion lemma off the exact-`(v−1)` form (rank-based,
  with consistency-by-extension) — statement work, low risk.
- Red-team round 2: adversarial MIXES of dependent+independent hosting against
  the transversal discipline; interaction of scaffold constants with multi-pair
  tuple families (value-independence should make this vacuous — verify);
  hardness audit for the ⊕-family (parsimonious 3-CNF embedding gives
  ⊕P-hardness; check no affine-counting collapse — `Z` computations are per-probe
  linear algebra, but the FUNCTION quantifies over all instances).
- Then the Lean scout: the rank-completion lemma over `ZMod 2` (elementary linear
  algebra + counting — very formalizable), and the `F = Z mod 2` reduction.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# TASK 5: the parity rank-completion lemma — frozen statement + second red-team

## 1. The general paper statement (rank-general, consistency by extension)

Let `Sys` be affine literals over `F₂^v` (pins with asserted values, scaffold and
block content with complemented values), `W := {a : Sys holds}` its solution set,
`λ*` a functional, `b` a value. Then:

- **(Counting)** `W` is empty or a coset of `ker(Sys) := span(functionals)^⊥`;
  `|W| = 2^{v − rank}` when consistent. `|W|` is ODD iff `Sys` is consistent and
  `rank = v`.
- **(Consistency by extension)** If the functionals of `Sys` are linearly
  independent, `Sys` is consistent for every RHS; in general, extend any
  independent subsystem — full-rank extensions are always consistent.
- **(Flip, general form)** If `Sys` is consistent with `rank = v − r` (`r ≥ 1`
  free directions) and `λ*` is NONCONSTANT on `ker(Sys)` (equivalently
  `λ* ∉ span(functionals)`), then the two `λ*`-slices of `W` are equinumerous
  (`= 2^{v−rank−1}` each). Hence: count(`Sys`) is even, and
  count(`Sys ∧ ⟨λ*,a⟩ = b`) is odd **iff `r = 1`** — the flip 0 → 1 happens
  exactly when `λ*` removes the LAST free direction, for BOTH values of `b`.
- **(Transversal discipline — design-side, not a hypothesis)** In the drag, rows
  SELECT which hosted positions vary; the adversary controls only which positions
  are in `S`. Rows select an independent transversal (rank ≥ mass/12) and hold
  all other hosted positions constant-OFF — dependent hosting never enters any
  instantiated system. The lemma's independence hypotheses are therefore
  satisfiable by construction, per pair, with pins+scaffold completing
  `T ∖ {λ*}` to rank `v − 1` while avoiding `λ*` (possible exactly by
  transversal independence).

## 2. Second red-team (four questions, answered)

**(a) Dependent+independent mixes vs the transversal.** Defeated structurally:
selection is ours. The only quantitative question is the matroid bound — rank of
any hosted multiset ≥ (#distinct functionals)/2 (Λ's circuits are cycles) and
positions-per-functional-per-block = 6 (after removing `(0,1)`), so priced ≥
mass/12 per block, worst case, mix-independent. Remark: even tautology positions
are priceable with full-rank pins (`F` flips 1 vs 0 there), so the only true dead
class was the removed contradiction selector.

**(b) Mass concentration hiding the transversal.** Saturating blocks caps the
per-block transversal at rank ≤ v while hosting up to `Θ(d·v)` per block: a
`Θ(d)` constant loss, no more — priced ≥ `Θ(T/d)` = `Θ(N)` for constant `d`.
Tradeoff noted: small `d` improves this constant but weakens expansion in the
kill-cost lemma; `d ∈ [8,16]` is the working range.

**(c) Hardness.** Singleton selectors embed 3-CNF PARSIMONIOUSLY (same witness
set over the same `a ∈ F₂^v`), so `sat3X⊕` ⊇ ⊕3SAT — ⊕P-hard-shaped;
polynomial-size circuits for the family would be a ⊕P ⊆ P/poly-strength event.

**(d) Cheap upper-bound quirks.** Unit-clause (purely affine) instances are
poly-time (Gaussian) — harmless, hardness lives in the OR-width. Per-probe `Z`
computations are linear algebra, but the FUNCTION ranges over all instances;
inclusion–exclusion expansions are exponential; no collapse found. Honest upper
bound stays brute force `2^v·poly = 2^{Θ(√N)}`. Watched corner: parity-specific
algebraic algorithms (e.g. ⊕2SAT-style special cases) — none apply at general
width.

## 3. Lean scout target (next file)

The kernel-form statements (hypotheses-first — no rank machinery, duality stays
on paper): (i) SLICE: a constraint-preserving direction `w` with `⟨l,w⟩ = 1`
makes the two `l`-slices of any solution set equinumerous; (ii) EVEN: hence any
surviving free direction forces an even count; (iii) ODD: a unique solution
gives count 1; (iv) FLIP: solutions `= {a₀, a₀+w}` with `⟨l*,w⟩ = 1` give
count even, sliced count odd, for both slice values.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE 28c COUNTING ROUND: menus dissolve, the architecture corrects, the expander's site is exact

## 1. The neutralization menus DISSOLVE (no residual risk)

The taut dichotomy settles every block: if a block's tautology position is row-side,
the rows set it ON — permanent kit, never dead, never pinnable; if probe-side, the
probe sets it when the block is unused and clears it when pinning — fully flexible.
The reserve is sized to the per-pair pin demand and pinned in EVERY pair (no unused
reserve blocks), with surplus reserve blocks DUPLICATING needed pins (same literal at
two blocks — trivially consistent).  No menu-consistency problem exists.  Taut-burial
by the adversary (`Θ(m)` bits) only converts blocks to permanent kit — it shrinks the
pin supply, which is the liveness counting below, and nothing else.

## 2. Architecture correction (two wrong turns found and fixed)

- WRONG (fear): cutting the witness space to a pair needs `v−1` unit-clause pins
  (`> m` blocks — impossible).  WRONG (hope): the target-block scaffold alone carries
  the rank (no pins at all).  The scaffold CANNOT cover the tuple coordinates: a
  count-conditioned scaffold literal and a priced tuple literal on the same
  coordinate demand contradictory values in the all-false system — both `Z`-sets
  empty, no detection.
- CORRECT: the rank splits.  PINS (clause-forced, at reserve blocks) cover exactly
  the target block's TUPLE coordinates, forcing the COMPLEMENTS of its priced
  literals — consistent by design (the forced value is `a₀`'s coordinate) and
  `w`-kernel automatically.  SCAFFOLD (count-conditioned, no-lose at the target
  block: any position class works, whichever side of the cut) covers the remaining
  coordinates.  Pin demand = per-block priced width ≤ reserve size — feasible, and
  `|V| = Θ(m²) = Θ(N)`-compatible.

## 3. The expander's load-bearing site, exactly: pin liveness

Killing the forcibility of one coordinate-value `(j,c)` unprices its data positions.
- WITHOUT decompositions (singletons-only codebook): kill cost = reserve burial
  `R·m/2`; capacity unlocked = data positions `R·m/2`.  **Ratio exactly 1 — a
  knife-edge; `R`-fold redundancy scales both sides (the ∃-audit's old finding
  recurs); the construction FAILS.**
- WITH expander decompositions (indirect forcing `e_j = edge(j,j') + e_{j'}`;
  deadness closed under decomposition — the scout file's `closed_dead_alternative`
  verbatim): kill cost `≥ (1 + c_d·d)·R·m/2` while capacity stays `R·m/2` (edge
  positions retain their DIRECT pin route — killing a coordinate does not unprice
  its edges).  Ratio `1 + c_d·d`.
- With the Markov data/reserve designation made AFTER seeing `S` (data := heaviest
  blocks, so kill-bits ≤ half of `|S|`):

      priced ≥ |S| · (ratio − 1)/(2·ratio) ≥ 0.36·|S|   (d = 8, Ramanujan),

  i.e. `Θ(T)` priced mass at every balanced cut.  Numerically: 0.365 (d=8),
  0.446 (d=16), 0.477 (d=32).

## 4. Company-independence under ⊕ (why the refuge does not recur)

Under ∃, content hosted in dead company was washed entirely.  Under ⊕ with the
two-point machinery, hosted content is priced as long as its OWN complement-forcing
lives — the company is irrelevant (the shared/scaffold part cancels in the
comparison).  The adversary must kill each coordinate-value separately, at the
expander-amplified price.

## 5. Status

The `(2+c)N` chain for `sat3X⊕` now has: all detection/capacity/supply theorems
frozen in Lean (task 5, rungs 24–28c), and the counting closed ON PAPER with
explicit constants, conditional on exactly one large deferred formalization — an
explicit `d`-regular spectral expander in Lean (the scout lemmas consume it as a
hypothesis).  Remaining mechanical: the per-target supply assembly over the
singleton+edge codebook, `|V| = Θ(T)` via `markov_select`, and rung 29's
root-shape/essential-variable mirrors + the `cbudget` conversion.  Honest claim
when done: a restricted lower bound `cbudget(sat3X⊕) ≥ (2+c)N` for an explicit
⊕P-shaped family, conditional on the expander instantiation until that is built.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE EXPANDER FRAMING (agreed): canonical Ramanujan, certified interface

The division of labor between the paper story and the Lean skeleton:

- **The intended instantiation is Ramanujan** — the flagship construction stays
  Ramanujan/Tseitin-flavoured, in continuity with the program's lineage, and the
  counting-round constants were computed against `λ₂ ≤ 2√(d−1)`.
- **The Lean interface accepts any certified expander** — the scout file's
  `Expander (nbr) (c)` predicate (edge boundary `≥ c·|A|` for `2|A| ≤ v`) is the
  ONLY thing the upper layers consume; no theorem above it depends on spectral
  detail.  The two named liveness classes (`hlive`, `hTautProbe`) and the
  kill-accounting fraction are all downstream of that one predicate.
- **Ramanujan is the canonical discharge of the interface** — but any explicit
  `d`-regular graph with certified edge expansion `c·d > 1` validates the whole
  chain (priced fraction `(ratio−1)/(2·ratio) > 0` with `ratio = 1 + c·d`), so a
  simpler certified expander (explicit small-parameter check, Margulis/zig-zag,
  or a probabilistic-existence argument over a finite verification) can land the
  skeleton first, with the Ramanujan discharge upgrading constants later.

Status of the checklist against this framing: root shape CLOSED (generic +
parity instantiation, unconditional); drag-side codebook glue = bookkeeping;
expander = the interface discharge above.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.

---

# THE DISCHARGE DESIGN (rung E-ladder): scaffold-covered companions, and where expansion actually stood

Full paper pass over the interface discharge before Lean, per standing discipline.
Outcome: one load-bearing simplification found and red-teamed, one honest correction
to the counting round's framing of the expander's role.

## E.1 The scaffold-companion simplification (red-teamed, adopted)

The counting round's edge route forced `e_j` indirectly as
`e_j = edge(j,j'') + e_{j''}` and required the companion `j''` to have live forcing
of its own — hence deadness closed under decomposition, hence the boundary-counting
of `closed_dead_alternative`, hence SPECTRAL EXPANSION as the load-bearing input.

The simplification: choose the companion OUTSIDE `K ∪ {j*}`.  Then the companion is
scaffold-covered — the failure-forced literal `(e_{j''}, 1)` already pins
`a j'' = 0` in the two-point system — and the edge pin `(e_j + e_{j''}, b_j + 1)`
alone forces `a j = b_j + 1`.  The companion needs NO pin, NO liveness, and may
itself be killed.  Audit against the supply algebra (now `route_supply`, PROVED):
- `a₀`-consistency: `dotp (e_j + e_{j''}) a₀ = a₀ j + a₀ j'' = (b_j+1) + 0` ✓.
- `w`-kernel: `j ≠ j*` (priced), `j'' ≠ j*` (by choice) ✓.
- pair identity: routes + scaffold-failure force `a` on `K` and on the complement,
  leaving exactly the `j*` direction free — two solutions ✓ (`route_supply`).
- probe machinery: a pin is still ONE codebook index at one reserve block —
  `probeOn`/`rowOf` unchanged ✓.

Consequence for the kill-accounting: to keep a priced coordinate `j` dead the
adversary must bury, per usable reserve block, the direct selector columns AND the
edge-selector columns of ALL `d` edges at `j` — companions inside the killed set
still work.  Killing a set `A` costs its incident-edge-column mass
`|A| + e_inc(A) ≥ (1 + d/2)·|A|` on ANY `d`-regular graph (equality only when `A`
is a union of components; strict on a connected graph).  **No spectral expansion is
required for the ratio: `1 + d/2 > 1` is generic.**

## E.2 Where the designer's freedom is spent (the independent-set step)

Per-block priced width must be `Θ(v)` for `|V| = Θ(m²) = Θ(N)`, so `K` is LARGE and
companions must avoid `K`.  The designer prices, within the surviving columns of a
data block, a set `K` that is INDEPENDENT in the route graph — then every priced
`j` has all `d` companions outside `K` (choose any not equal to `j*`; `d ≥ 2`
suffices).  Any graph has, inside every subset `U`, an independent subset of size
`≥ |U|/(d+1)` (greedy) — a GENERIC fact, no expansion.  This costs a factor
`d+1` in the priced fraction, which the `1 + d/2` ratio absorbs: the fraction
stays a positive constant, which is all `(2+c)N` needs.

## E.3 The honest correction to the framing

The certified interface (`Expander (nbr) (c)`, canonical Ramanujan) remains VALID —
any certified expander still discharges everything.  But the load-bearing property
is weaker than expansion: `d`-regularity + connectivity + the generic greedy
independent-set bound.  The canonical discharge can therefore be an explicit
CIRCULANT (`j ↦ j ± 1, …, j ± d/2 (mod v)`) — certifiable in Lean by elementary
counting, no spectral theory, no Mathlib gap.  Ramanujan remains the flagship
STORY for constants (its expansion strictly improves the priced fraction via
`closed_dead_alternative` if one later restores companion-liveness routes), but it
is no longer on the critical path.  This supersedes "the expander's load-bearing
site" (§3 of the counting round): that analysis was correct FOR ITS route design;
the route design changed.

## E.4 The discharge ladder (frozen)

- **E1 — route supply** (`ComputationalDepthNFrameParityRouteSupply.lean`, PROVED):
  `route_supply` generalizes `singleton_supply` to route assignments (direct or
  edge with off-`K∪{j*}` companion); `direct_routes_are_routes` checks the
  specialization.  All linear slots of the 28c pair machinery re-supplied.
- **E2 — route re-threading**: mirror 28e/28g with `route_supply` in place of
  `singleton_supply`; the drag hypotheses `hpinCode`/`hpinCover` generalize from
  singleton-complement shape to route shape.  Mechanical mirror.
- **E3 — extended codebook**: `xstdL v = (2+d)·v + 1` — tautology, singleton
  columns, and edge columns for the explicit circulant; enumeration reads,
  injectivity, disjointness (the `stdCode` pattern).
- **E4 — the graph layer**: circulant `nbr`, `d`-regularity, symmetry, and the
  generic greedy independent-set-in-any-subset bound.  Elementary; replaces the
  spectral long-pole.
- **E5 — the kill-accounting assembly**: at any balanced cut of the extended-
  codebook parity family — Markov designation (heaviest blocks = data), survivor
  columns, independent `K` within survivors, route selection, reserve transversal —
  producing the E2 drag package with `|V| ≥ frac·|S| − O(m)`.  The big rung; all
  counting, no new algebra.
- **E6 — headline re-assembly**: essentials at `xstdCode` (`2·m·(2+d)·v ~ 2N`) +
  the E5 drag at a heavy band via the generic wire cut ⇒ `cbudget ≥ (2+c)N`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
