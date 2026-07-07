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

## E.5 Framing RATIFIED (HAL): circulant on the critical path

The trade is confirmed: the proof interface never needed spectral optimality, only
enough certified expansion/incident-edge mass to clear the constant — with
scaffold-covered companions giving ratio `≥ 1 + d/2`, spectral machinery is overkill
for landing the theorem.  The hierarchy:

- **Critical Lean path**: explicit circulant + elementary counting (E3–E5).
- **Paper narrative**: Ramanujan is the canonical/high-quality instantiation; the
  proof accepts any certified expander.
- **Upgrade path**: Ramanujan discharge later if worth it (constants/continuity).

## E.6 E2 status: DONE (route re-threading)

- `route_supply` extended with the singleton `w`-kernels (exposed in the conclusion
  because the existential `w` is opaque downstream — the 28e thread's `hwE` slot
  consumes them).
- **E2a** (`ComputationalDepthNFrameParityRouteThread.lean`, PROVED):
  `parity_pair_dist_route` — the route-general mirror of 28e.  Rung 28c was already
  pin-literal-generic (pins enter only through `litHolds a (code (pinIdx c))`), so
  the re-thread touches exactly the two pin-layout slots.
- **E2b** (`ComputationalDepthNFrameParityRouteAssembly.lean`, PROVED):
  `parity_route_pair` + `parity_route_drag` (same `rowOf`/probe/reads, per-target
  route assignments `rF`) + `parity_route_drag_direct` (the all-direct
  instantiation reproduces `parity_assembled_drag`'s exact hypothesis shape — the
  generalization is strict, nothing regressed).

Next: E3 extended codebook with edge columns.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.

---

# E5 PAPER ROUND: two accounting errors found — the counting round's closure claim is SUPERSEDED

Red-team of the kill-accounting before Lean, per standing discipline.  Outcome: the
"counting CLOSED on paper" claim (28c counting round, §§1,3) does NOT survive; two
genuine gaps, one with a verified fix, one requiring a design decision.  Named
honestly; nothing below is certified closed until re-derived.

## Finding (a): the taut-burial hole (§1's "nothing else" is WRONG) — FIX VERIFIED

The counting round dismissed taut-burial as "converts blocks to permanent kit,
shrinks the pin supply, and nothing else".  FALSE for data capacity: the frozen
machinery (28g `rowOf` kit-blanket + `hTautProbe`) makes a block with row-side
tautology unable to host TARGETS — one S-bit at the taut column kills the block's
whole data capacity (`~L` bits) — AND multi-difference absorption (`hnt` across
pairs differing at several blocks) requires an always-true literal in every hosting
block's selection, which only a selected tautology provides.  Dead-hosting at
taut-buried blocks costs `X + X/(L−1)` for `X` dead bits — ratio → 1, the drag dies
at every band.

**The fix (verified at the algebra level): the TAUT-PAIR ABSORBER.**  For any
coordinate `j`, the two singleton columns `(e_j,0),(e_j,1)` jointly selected are an
always-true absorber (`a j = 0 ∨ a j = 1`).  Whichever side of the cut each column
falls, its OWNER sets it (row sets its half, probe sets the complement half) — the
absorber is UNKILLABLE per pair; the adversary must control both halves of ALL `v`
pairs at a block (cost `2v`) to force the row-policy dilemma.  Consequences:
- the target block's row-side absorber half enters the target system as one more
  failure-forced row — consistent iff the supply's off-`K∪{j*}` values generalize
  from `0` to a designer vector `z` (`a₀ := … else z j`); the edge-route pin value
  becomes `bval j + 1 + z j''`.  This is `route_supply_z` (E5-prep, Lean below).
- `hTautProbe` leaves the critical path; the taut column becomes a convenience.
- kill-cost of a block's absorber = `2v` against hosting capacity `(2+2dd)v`:
  ratio `1+dd > 1` for SPREAD mass.  ✓

## Finding (b): the FULL-BLOCK CONCENTRATION WALL — OPEN, design decision required

The `1+dd` ratio only prices spread mass.  The adversary can CONCENTRATE: fully
stuff `|S|/L` blocks (every column of the block in `S`).  A fully-stuffed block's
absorber is dead (the `2v` kill-bits are part of the stuffing), so cross-block
product families cannot host differences there, and the tuple drag prices NOTHING
of that mass.  Per-block sub-drags cap at `|V_β| ≤ j` each (non-additive).  This is
the flat-sat3 concentration battleground recurring at the parity family: the
counting round's §3 never priced it.

**Candidate resolution (designed, NOT yet audited): the TWO-CHANNEL DICHOTOMY.**
Concentration is exactly the ALIGNED case (rung 18's alignment law: minimal
circuits' cuts respect block boundaries up to `CE+1`), and the annulus machinery
(rung 22) was built for aligned mass: nested chains price per-block families at
their own scales, `log|Y| ≤ CE + k + 1` — `m/2` full blocks each carrying a
`2^{Θ(L)}` same-block two-point family (same-block multi-difference IS handled by
the 28c supply) would give `CE = Θ(N)`.  Spread mass falls to the absorber tuple
drag at ratio `1+dd`.  The QUANTITATIVE split (per-block thresholds, chain
existence through aligned blocks at the right scales, cross-channel additivity of
the two prices against ONE ledger) is the open design work — it is the honest
remaining distance to `(2+c)N`, and it is NOT mechanical.

## Consequences for the ladder

- E5-prep (SAFE under every variant, Lean now): `route_supply_z` (the `z`-general
  supply) and the WEIGHTED greedy bound (mass-weighted independent selection, for
  the global coordinate pool `P*` that row-side company/absorber choices need).
- E5 proper (kill-accounting) is BLOCKED on the finding-(b) design round.
- The honest current headline remains: `2N` baseline (unconditional, EssStd) +
  `Ω(√N)`-strength drags; `(2+c)N` requires closing (b).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# E5′ PAPER ROUND: the concentration–spread dichotomy — one channel proved, the other bottlenecked

Full paper pass on the two-channel dichotomy, per standing discipline (math before Lean),
working through the four checks the task named.  Outcome, stated honestly: the SPREAD
channel is real and gives `Θ(N)`; the CONCENTRATION channel is **witness-dimension
bottlenecked at `Θ(v) = O(√N)`** and CANNOT give `Θ(N)`.  The dichotomy therefore does NOT
close `(2+c)N` by itself — it REDUCES `(2+c)N` to a spread-forcing (anti-alignment)
statement for minimal parity circuits, which is unresolved and, by analogy with the flat
family's alignment law (rung 18), is the hard direction.  No false closure is claimed.

## Check 1: the full-block threshold, precisely

At a balanced cut `S` (from `parity_balanced_cut`, `T ≤ |S| ≤ 2T−2`, width `j ≤ CE+1`),
for each block `c'` let `A_{c'} = |{i : xbit c' i ∈ S}|` be its row-side (S-side) mass, out
of `L = xstdL v dd` columns.  A block is **full** iff `A_{c'} = L` (every column row-side)
— equivalently its tautology column is row-side, so `hTautProbe` FAILS for it: the probe
cannot zero its tautology, so it cannot be a tuple-drag TARGET.  Let
`Full = {c' : A_{c'} = L}`, `spread(S) = ∑_{c' ∉ Full} A_{c'}`, `conc(S) = ∑_{c' ∈ Full} L`.
Then `spread(S) + conc(S) = |S|`.  Threshold: fix `θ = 1/2`; either `spread ≥ |S|/2`
(SPREAD regime) or `conc ≥ |S|/2` (CONCENTRATED regime).

## Check 4 first (common ledger): both channels charge coneExcess

Both channels bound the SAME quantity `CE = coneExcess c (root)`, through the SAME
`connectivity_fanout` ledger `2·|ESS| + (drag) ≤ length + 1`.  The spread channel builds a
tuple family `V` with `|V| ≤ j ≤ CE+1` (`parity_route_drag`/`parity_xstd_drag`).  The
concentration channel builds a chain family `Y` with `log|Y| ≤ CE + k + 1`
(`parity_chain_capacity_excess`, PROVED this rung).  Both are lower bounds on `CE`, both feed
the ONE headline.  There is no double-counting BETWEEN channels because we invoke exactly
ONE of them per band (whichever regime holds); we never add a spread price and a
concentration price at the same band.  ✓ (This resolves the "compatible quantities in the
same ledger" check — trivially, because we never sum across channels.)

## Check 2: chain existence through concentrated blocks — HOLDS

`balanced_chain_exists` (rung 22, generic) supplies a nested chain `ws_0 ⊑ … ⊑ ws_k` at ANY
prescribed increasing band profile `T_0 < … < T_k ≤ (varsOf root).card`.  To capture `g`
full blocks one-per-scale, set `T_i = T_0 + i·L` (each step admits one fresh full block's
`L` columns); feasible whenever `g·L ≤ (varsOf root).card ≤ N`, i.e. `g ≤ m`.  So a chain
threading up to `k = g` concentrated blocks exists.  ✓  (The INNERMOST-differing-scale
trick makes the family well-defined: for a pair differing at scale-set `D`, detect at
`i = min D` — outer differences are erased by the fixed completion `x` on `varsOf(ws_i)ᶜ`,
inner blocks agree, so only block `β_i` differs.  This resolves multi-scale cancellation.)

## Check 3: do per-block prices ADD through rung 22? — NO, they are WITNESS-CAPPED

This is the check that fails, and it is the crux.  For block `β_i` to host `b_i` detectable
two-point bits at scale `i`, the parity value must respond to `β_i`'s toggle against the
fixed surroundings.  The parity value is `#{a ∈ F₂^v : instSat a} mod 2`.  Detection at
`β_i` requires the combined affine system (β_i target + reserve pins + the INNER data blocks
`β_0..β_{i-1}` at their agreed values) to be consistent and rank-changing — `parity_flip`'s
hypotheses.  But:

- **the witness space is `F₂^v`, dimension `v`**, shared by ALL blocks;
- a detectable bit at `β_i` consumes a rank direction of that shared space (the target
  literal must complete the rank — `parity_flip` is exactly rank-completion);
- distinct detectable bits across the chain must complete DISTINCT rank directions (else
  they are not independently detectable — their toggles' parity effects collide);
- there are at most `v` independent rank directions.

Hence `∑_i b_i ≤ v`.  Combined with `∑_i b_i = log|Y| ≤ CE + k + 1` (the chain ledger),
the concentration channel yields `CE ≥ log|Y| − k − 1`, but `log|Y| ≤ v`, so it yields
NOTHING beyond `CE ≥ v − k − 1` — and with `k = Θ(m)` scales this is `≤ v = Θ(√N)`.  The
per-block prices do NOT add past the witness dimension; rung 22's additive EXIT ledger is
real, but the FAMILY it can host is capped by `v`, not by the exit budget.

**This is the same `√N` witness bottleneck that capped the flat family** — it is a property
of the `⊕#SAT`-over-`F₂^v` semantics with `v = Θ(√N)`, not of the encoding.  Concentration
lets the adversary force ALL detection through this bottleneck.

## The honest reduction

`(2+c)N` for `sat3X⊕` (standard parameters `v = Θ(√N)`) now rests on EXACTLY ONE unproved
statement:

  **(SPREAD-FORCING)** every minimal circuit for the parity family has, at some band
  `T = Θ(N)`, a balanced cut with `spread(S) ≥ c·N` — i.e. concentration is NOT forced.

If (SPREAD-FORCING) holds, the absorber tuple drag (E1–E4 + the taut-pair absorber) prices
`spread(S) = Θ(N)` and `(2+c)N` follows.  If concentration is forced (as rung 18's
alignment law forces for the flat family — cuts respect block boundaries, i.e. blocks are
whole-in-or-whole-out, i.e. FULL or empty), then the drag is capped at `Θ(v) = O(√N)` and
`(2+c)N` FAILS for this family.

The default expectation, by analogy with rung 18, is that concentration IS forced — the
alignment law says minimal circuits' cuts align to block boundaries, which is exactly
concentration.  So the honest status is: **`(2+c)N` for `sat3X⊕` is BLOCKED at the same
`√N` witness bottleneck; parity detectability defeats the ∃-refuge (real progress, rungs
24–29) but does NOT enlarge the witness space, and the witness space is the true cap.**

## What would actually break `√N`

To exceed `Θ(√N)` the family needs witness dimension `v = ω(√N)` while keeping `m·L = N`
and the family genuinely `⊕#SAT`-hard.  With `N = m·v·dd`, `v = ω(√N)` forces `m·dd =
o(√N)`, i.e. `o(√N)` clauses — too few for `⊕#SAT`-hardness at that `v` (a `v`-variable
`⊕#SAT` instance needs `Ω(v)` clauses to be hard, and `Ω(v) = ω(√N)` clauses need `m = ω(√N)`,
contradiction).  So NO single-witness-space parity family in this framework escapes `√N`.
The escape, if any, needs MULTIPLE independent witness spaces (a product/tensor family) so
that concentration into few blocks still spans `ω(√N)` independent rank directions — a
genuinely different construction (Route F, not yet designed).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ROUTE F: the multi-witness tensor family — designed, assessed, and its true limit

Design of the multi-witness escape from the E5′ `√N` witness cap, worked on paper per
standing discipline.  Outcome, stated honestly: the tensor family BEATS the crude
witness-rank cap (its detectable rank is genuinely `Θ(N)`, not `√N`), but it does NOT
convert to `(2+c)N` — it reduces to the same spread-forcing statement, plus a decomposition
hazard.  The genuine escape lies elsewhere (cheap-literal encoding).  No false closure.

## F.1 The root cause of `√N`, made crisp

For the presence-bit encoding, a block is a clause over `F₂^v`; specifying which affine
literals it contains costs `L = Θ(v)` input bits (one presence bit per candidate literal),
and `⊕#SAT`-hardness needs `m = Ω(v)` clauses.  Hence `N = m·L = Ω(v²)`, i.e.
**`v ≤ √N` is FORCED** — the witness dimension cannot exceed `√N` in this encoding.  The
E5′ detection cap `= v` is therefore `≤ √N`.  This is the whole bottleneck in one line.

## F.2 The tensor construction

Split the `m` blocks into `g` GROUPS, each a single-witness parity over its OWN `F₂^{v'}`
witness space (disjoint across groups), and combine by XOR:

    tensorParity BB = ⊕_γ parityFamily(BB γ) = (Σ_γ Z_γ) mod 2.

Parameters: `v' = √{N'}`, `N' = N/g` per group; `g` groups; total witness `g·v'`.  The
LOCALIZATION lemma (`tensor_detect_localizes`, PROVED): a change confined to group `γ*`
flips the tensor iff it flips group `γ*`'s parity — disjoint witness spaces, so NO
cross-group over-determination.  Total detectable rank `= Σ_γ v' = g·√{N/g} = √{gN}`.
With `g = N^{1−2α}`, `v' = N^α`: detectable rank `= N^{1−α}` → `N` as `α → 0`.  **The crude
witness-rank cap is beaten: the tensor exposes `N^{1−ε}` independent detectable directions,
not `√N`.**  This is real and is the point of the construction.

## F.3 Why it still does NOT give `(2+c)N` — three independent walls

1. **Annulus ledger death (concentration channel).**  To harvest the `Θ(N)` directions
   across a nested chain, the annulus charges `+1` per scale (`log|Y| ≤ CE + k + 1`).  At
   concentration each fresh block hosts `O(1)` witness-capped directions, so `k = Θ(rank)`
   scales are needed and the `+k` charge CANCELS the harvest: `CE ≥ rank − k ≈ 0`.  This is
   encoding-independent — it killed the single family (E5′) and kills the tensor identically.
   The annulus only pays when detection is `ω(1)` PER SCALE, which concentration forbids.

2. **No new single-cut capacity (spread channel).**  The single-cut tuple drag already
   prices `Θ(N)` positions across ALL blocks (hence all groups) at one balanced cut — for
   ANY family.  The localization lemma shows each priced position detects within ONE group;
   there is no cross-group amplification at a single cut.  So the tensor adds nothing the
   spread channel did not already have; and the spread channel needs SPREAD-FORCING
   (unproved, likely false by the rung-18 alignment analogy).

3. **Decomposition hazard (the modularity = cheapness identity).**  Blocks of group `γ` read
   disjoint inputs, so `cbudget(tensor) ≤ Σ_γ cbudget(bγ) + cbudget(XORtree)`.  If the
   per-group families are near-baseline-easy (`cbudget(bγ) = 2N' + o(N')`), then
   `cbudget(tensor) = 2N + o(N)` — `(2+c)N` is FALSE for the tensor.  The very independence
   that removes over-determination (wall-free detection) is EXACTLY a group-local circuit
   decomposition.  Independence and cheapness are the same coin.

The reconciliation of walls 1/2 (rank is `Θ(N)`) with wall 3 (maybe cheap): the method's
detectable RANK being `Θ(N)` does not mean the method can PROVE `cbudget ≥ 2N + Θ(N)` — it
must BUILD a surviving detectable family at ONE cut (spread) or `ω(1)`-per-scale (annulus),
and both are blocked.  Rank is necessary, not sufficient.

## F.4 The honest verdict and the actual frontier

Route F is a genuine sharpening: it PROVES the obstruction is NOT witness-rank (tensor fixes
that) but the **single-cut-spread vs per-scale-annulus ledger tension**, gated by
**spread-forcing**.  `(2+c)N` for the tensor family ⟺ spread-forcing for the tensor family —
the same wall as the single family, now isolated from the witness-rank red herring.

The one encoding that would raise `v` past `√N` is **cheap-literal (index) encoding**: a
block selects `O(1)` literals by their `O(log v)`-bit INDICES from a fixed menu, so
`L = O(log v)`, `N = Θ(v·log v)`, `v = Θ(N/log N) = Ω(N^{1−o(1)})`.  Then witness dimension
≈ `N` and the E5′ cap is `≈ N`.  BUT index-encoding makes the block content a NONLINEAR
function of the input bits, breaking the presence-bit `decodeBlock`/tuple-drag detection
entirely.  A detection method compatible with index-encoding is a genuinely new instrument —
the real Route-G frontier, undesigned.

Frozen Lean (`ComputationalDepthNFrameTensorFamily.lean`, clean axioms): the tensor family
value, `groupCount_eq_parityFamily`, `tensorParity_single_diff`, and `tensor_detect_localizes`
— the structural core, true and reusable for any multi-witness successor.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ROUTE G: index-encoding detection — the super-√N regime and its hard barrier

Design of the index-encoding detection method, worked on paper per discipline.  Outcome,
honest: index-encoding raises the detectable witness dimension from `√N` to `N/log N`
(a genuine super-`√N` improvement, the first sub-linear-error regime), via a detection
PRIMITIVE that survives the encoding's nonlinearity; but it is CAPPED at `N/log N` by a
fixed-menu barrier, so constant `c` in `(2+c)N` stays out of reach — and that cap is a
genuine METHOD BARRIER for affine `⊕#SAT` families, not a construction defect.

## G.1 The encoding

Fix a rich menu `menu : (block, slot, index) → Lit v` as a FAMILY PARAMETER (free, like the
codebook), with `M = poly(v)` entries spanning `F₂^v`.  Each block has `w = O(1)` slots; slot
`s` holds an INDEX `∈ [M]` encoded in `⌈log M⌉ = O(log v)` input bits; the block's clause is
`{menu(idx_1), …, menu(idx_w)}`.  A block costs `O(log v)` input bits, so `N = m·w·log M`, and
with `m = Θ(v)` (hardness) the witness dimension is `v = Θ(N / log N) = N^{1−o(1)}`.  The
menu being a parameter (not input) is what buys the rich `v`-dim span at `log v` input cost.

## G.2 Why the presence-bit detection breaks, and what replaces it

Toggling one index bit performs a MENU-JUMP `menu(idx) → menu(idx ⊕ e_t)` — nonlinear in the
input (the resulting literal depends on the OTHER index bits of the slot).  The presence-bit
`xbit`/`decodeBlock`/`rowOf` machinery (toggle position `p` ⟺ toggle literal `code(i)`) is
gone: there is no per-position literal.

FALSE START (linear menu): make `menu(idx).func = λ_0 + Σ_t idx_t·g_t` so toggles are linear
shifts `+g_t`.  Then `O(log v)` generators `g_t` span only `O(log v)` functional dimensions,
collapsing the witness space to `O(log v)` — the same bottleneck.  A LINEAR menu cannot span
`F₂^v` with `O(log v)` index bits.  So the menu MUST be nonlinear; detection must handle it.

THE PRIMITIVE (proved, `ComputationalDepthNFrameIndexDetect.lean`): pin the witness to a LINE
`{a₀, a₀+u}` (the two-point set, as in the parity drag).  Then for ANY literal `ℓ`,

    twoPointCount ℓ a₀ u := [ℓ holds at a₀] + [ℓ holds at a₀+u]  (in ZMod 2)  =  dotp ℓ.1 u.

The two-point PARITY of a literal equals its FUNCTIONAL dotted with the pin-direction —
VALUE-INDEPENDENT (`ℓ.2` and `a₀` drop out).  Hence an index toggle `idx → idx'` is detectable
(under pin `u`) iff `dotp (menu(idx)).1 u ≠ dotp (menu(idx')).1 u` — a pure functional-
separation test on the menu, INDEPENDENT of demanded values and base points
(`twoPoint_detect`, `menu_toggle_detect`).  This is the detection method Route G needed: it
reads the nonlinear menu through the LINEAR functional it selects, which is exactly the
quantity the line-pin exposes.

## G.3 The improvement — super-√N

- Spread channel: at one balanced cut, price `Θ(v) = Θ(N/log N)` index bits, each detected by
  the primitive with a per-target line-pin `u`; a generic `u` separates ~half the menu
  toggles, so a constant fraction is priced → `|V| = Θ(N/log N)`, `CE ≥ Θ(N/log N)` (under
  spread-forcing, as always).
- Concentration channel: a block now carries `O(log v)` index bits selecting from a `v`-dim
  menu — it is INFORMATION-DENSE, hosting up to `Θ(log v)` independent detected directions per
  block (vs `O(1)` for a presence block).  This finally beats the annulus `+1`-per-scale
  charge: `k` scales × `Θ(log v)` bits/scale = `Θ(k log v)` detected vs `+k` charged, so
  `CE ≥ Θ(k log v) − k = Θ(k log v)`.  Harvesting the full witness cap `v` needs `k = v/log v`
  scales, giving `CE ≥ v − v/log v = Θ(v) = Θ(N/log N)`.  **The concentration bottleneck is
  raised from `√N` to `N/log N` — index-density is what the annulus ledger rewards.**

Either channel yields `CE = Θ(N/log N)`, i.e. `cbudget ≥ 2N + Θ(N/log N) = (2 + Θ(1/log N))N`.

## G.4 The hard barrier — why constant `c` is out of reach

The detectable rank is `≤ v` (all detection is `dotp (functional) u`, functionals in `F₂^v`).
The witness dimension obeys, in ANY fixed-menu affine encoding:

    N = m·w·log M,   m ≥ v (hardness),   M ≥ v (menu spans F₂^v)   ⟹   N ≥ v·log v,
    hence  v = O(N / log N).

So `CE = O(v) = O(N/log N)` and `cbudget ≤ 2N + O(N/log N) = (2 + o(1))N` by this method.
**`(2+c)N` with CONSTANT `c` is UNREACHABLE for affine `⊕#SAT` families under N-frame
(witness-rank) detection.**  The `log v` factor is irreducible: cheaper indices (`o(log v)`
bits) cannot address a `v`-spanning menu; a smaller menu cannot span `F₂^v`; a non-spanning
menu collapses the witness space.  This is the honest ceiling of the entire affine-parity
program: it reaches `(2 + o(1))N`, never `(2 + Ω(1))N`.

## G.5 The frontier beyond the barrier

Constant `c` requires detection NOT bounded by an affine witness-rank — i.e. a family whose
sensitivity is not `dotp (functional) u`.  Candidates (all undesigned): a NON-affine literal
menu (e.g. degree-2 / quadratic constraints, where the two-point primitive gives a quadratic
form, not a linear functional, and the "rank" is the quadratic-form rank up to `v²` — but
description cost of a quadratic form is `v²` bits, re-forcing the barrier one power up unless
the quadratic menu is also index-encoded); or a detection instrument that reads MULTIPLE line-
pins per position (a `(v−t)`-flat instead of a line), whose two-point parity is a degree-`t`
object — trading witness-rank for a higher-degree cap at higher description cost.  Each trades
the same way; the meta-barrier is that DESCRIPTION COST and DETECTION RANK scale together, and
`N = (rank) × (bits per unit rank)` with bits-per-unit `≥ log(rank)`.  Breaking `(2+Ω(1))N`
needs a family where detection rank is `Θ(N)` at `O(1)` description-bits per rank-unit — which
no affine or bounded-degree menu provides.

Frozen Lean (`ComputationalDepthNFrameIndexDetect.lean`, clean axioms): `twoPointCount`,
`twoPointCount_eq_dotp` (the primitive), `twoPoint_detect`, `menu_toggle_detect` — the index-
encoding detection core, true and reusable.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ROUTE H: constant-description-rank detection — the non-affine attempt

Direct attack on the Route-G frontier question: *a detection architecture with `Θ(N)`
independent detectable rank at `O(1)` description bits per rank-unit.*  Worked on paper per
discipline.  Outcome, honest: quadratic (degree-2) detection PROVABLY defeats the
witness-collision that capped affine detection at `v` — its directions live in a `Θ(v²)`-dim
space and do not collide until `N` — but it pays a NEW cost (base-point dependence) that
breaks the value-independence the rung 24–29 drag relied on.  So Route H converts the
question from "is there enough rank" (answered: YES, quadratic gives it) to "can a drag
harvest it under the base-point cross-term and the concentration attack" (OPEN).

## H.1 Why affine collides and quadratic does not

Affine detection is `dotp (functional) u` (§G): the detection direction of a literal is its
functional, an element of the `v`-dim dual `(F₂^v)^*`.  Any `v+1` functionals are linearly
dependent — the directions COLLIDE at `v`, capping rank at `v = O(N/log N)`.  This is the
whole affine ceiling.

Quadratic detection lives in the space of quadratic forms, dimension `Θ(v²)`.  The
two-point primitive (proved, `ComputationalDepthNFrameQuadDetect.lean`):

    quadMonoCount i j t a₀ u  =  a₀_i·u_j + u_i·a₀_j + u_i·u_j.

The `u_i·u_j` term is a genuine degree-2 direction, and `quad_directions_distinct` proves
distinct pairs `{i,j}` give distinct directions.  There are `Θ(v²) ≫ N` of them, all
linearly independent — **collision is deferred past `N`, so detection rank is capped only by
the input count `N`, not by `v`.**  This is exactly the "`Θ(N)` rank at `O(1)` bits/unit"
the question asked for: an index-encoded quadratic menu costs `O(log v)` bits per literal
(same as affine) but accesses `Θ(v²)` non-colliding directions, so the `N ≥ v·log v` coupling
no longer forces `rank ≤ v` — rank can reach `N`.

**Answer to the god-move question:** the family that gives rank without paying `log(rank)` per
unit is a QUADRATIC (or higher-degree) affine-form menu.  Degree `k` gives a `Θ(v^k)`-dim
detection space at the SAME `O(log v)` description cost, decoupling rank from the witness
dimension.  Rank is no longer the bottleneck.

## H.2 The new cost — base-point dependence (why it is not automatic)

The affine primitive was VALUE- and BASE-POINT-independent: `twoPointCount = dotp ℓ.1 u`,
with `ℓ.2` and `a₀` absent.  That independence is what made the two-point rank-completion
machinery work — `parity_two_point`'s `heven drops out`, `parity_flip`'s value-independence.

The quadratic primitive is NOT base-point-independent: the cross-term `a₀_i·u_j + u_i·a₀_j`
depends on `a₀`.  At the origin `a₀ = 0` it vanishes (`quadMonoCount_origin`:
`quadMonoCount i j t 0 u = u_i·u_j`, clean), but the drag's witness line `{a₀, a₀+u}` is
pinned by the OTHER blocks (reserve pins), which generally force `a₀ ≠ 0`.  So the clean
direction is available only when the drag can pin the witness THROUGH the origin — a new
constraint the affine drag never had.

## H.3 What remains (the undischarged Route-H work)

1. **A drag around the origin.**  Rebuild the rung 24–29 pipeline for quadratic literals with
   the witness line pinned through `a₀ = 0` (or with the cross-term controlled/cancelled by a
   companion structure, analogous to the scaffold-covered companions of E1).  The two-point
   comparison must now track the `u_i·u_j` term; `parity_two_point` needs a quadratic analog.
2. **Hardness of quadratic `⊕#SAT`.**  `⊕#SAT` over quadratic clauses is `⊕P`-complete
   (quadratic forms over `F₂` already encode general `⊕#SAT`), so the baseline `2N` and the
   family's genuine hardness are in hand — but the explicit family must be pinned down.
3. **THE concentration/alignment attack — still the gatekeeper.**  Even with `Θ(N)` rank
   available, the drag must survive the adversary's cut alignment (the wall that capped every
   prior route).  Quadratic detection changes the local-rank calculus: a concentrated block
   now hosts `Θ((log v)²)` quadratic directions (pairs of its index bits) rather than
   `Θ(log v)` affine ones — a further boost to the annulus per-scale harvest — but whether it
   defeats concentration or merely raises the exponent is the open quantitative question.  My
   honest expectation: degree `k` pushes the reliable bound to `Θ(N · (log v)^{k-1} / log v)`-
   shape, i.e. it keeps IMPROVING the constant-error term with degree but each fixed degree is
   a fixed poly-log gain — reaching `(2+c)N` with constant `c` would need degree `k = ω(1)`
   (super-constant), whose description cost `O(k log v)` per literal re-enters the coupling.
   This is the meta-barrier's next form and is NOT yet resolved either way.

## H.4 Honest status

Route H answers the rank question affirmatively — quadratic/higher-degree detection gives
`Θ(N)` non-colliding rank at `O(log v)` description cost, defeating the witness-collision cap
that ceilinged the affine program.  It does NOT yet yield `(2+c)N`: the base-point
cross-term demands a new origin-pinned drag, and the concentration attack must still be beaten
at the new degree.  The proved primitives (`quadMonoCount_eq`, `quadMonoCount_origin`,
`quad_directions_distinct`) are the tool; the drag and its concentration analysis are the
next rungs.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ROUTE H CONCENTRATION GATE: attacked — the drag ceilings at N/log N (Route G confirmed)

Rigorous attack on the sole open gate of the quadratic drag: at a real balanced cut, can the
priced mass |V| be Θ(N)?  Worked on paper, then the load-bearing cap frozen in Lean
(`ComputationalDepthNFrameQuadConcentration.lean`).  Honest outcome: NO — the drag is capped
at |V| ≤ m = N/L ≤ N/log N, confirming the Route G ceiling `(2 + o(1))N` from the drag side.

## The two caps, and which one binds

Route H established that the SINGLE-CUT DETECTION RANK is Θ(N) for quadratic literals (the
witness-rank cap that held affine at √N is gone — `quadMonoCount`'s `Θ(v²)` non-colliding
directions).  But detection rank is NOT the binding constraint for the drag.  The binding
constraint is the PER-CUT BLOCK COUNT:

- Each priced block must STRADDLE the cut: its quadratic monomial is row-side (`hVS`), its
  tautology and scaffold are probe-side (`hTautProbe`/`hlive`/`hScaf`).  A block whole-in-S has
  its tautology in S, so it cannot be a target; a block whole-in-Sᶜ carries no row-side priced
  position.  So every priced block straddles.
- The drag is built ONE priced position per block (`hVone`), so |V| = #priced blocks ≤ #blocks.

**`priced_card_le_blocks` (PROVED): |V| ≤ m.**  The map `q ↦ q.1` is injective on `V`.
**`priced_card_le_ratio` (PROVED): L·|V| ≤ N**, i.e. |V| ≤ N/L.

## Why this caps `cbudget` at `(2 + o(1))N`

The drag gives |V| ≤ jj ≤ coneExcess + 1, so it proves `coneExcess ≥ |V| − 1`.  But
`|V| ≤ m = N/L`, and a block addressing a literal menu that spans `F₂^v` needs
`L ≥ ⌈log(menu size)⌉ = Ω(log v)` selector bits (Route G's addressing cost — a `v`-spanning
menu has `≥ v` entries, `≥ log v` index bits, and the presence-bit encoding needs `≥ v`
positions outright).  Either way `L = Ω(log v)`, so

    |V| ≤ N / L ≤ N / log v = O(N / log N),   hence   coneExcess = O(N / log N),

and `cbudget ≤ 2·|ESS| + coneExcess ≤ 2N + O(N/log N) = (2 + o(1))N` by the drag method.

## The honest resolution

Route H's removal of the witness-rank cap is REAL but does not help the drag, because the
per-cut priced mass is bounded by the block count `m`, not the per-block detection rank.  The
block count `m = N/L` is itself capped by `L ≥ log v` — the SAME addressing barrier that
ceilings Route G.  So the multi-difference quadratic drag, fully discharged
(`gParity_quad_drag`), proves at most `coneExcess = O(N/log N)`: it reaches
`(2 + Θ(1/log N))N`, never `(2 + Ω(1))N`.  Constant `c` is out of reach for the drag method.

To exceed the ceiling the family would need `m = Θ(N)` blocks (`L = O(1)` selector bits per
block) with each block STILL individually detectable — impossible, because `O(1)` bits cannot
address a `v`-spanning menu, and a non-spanning menu collapses the witness space (§G.4).  The
concentration/spread-forcing question (does the drag ACHIEVE `Θ(N/log N)` or less?) is the
residual, but the CEILING `N/log N` is now proved.  The affine → tensor → index → quadratic
program is confirmed to ceiling at `(2 + o(1))N`; `(2 + Ω(1))N` needs a detection mechanism
whose priced mass per cut is not block-count bounded — which no single-witness affine or
bounded-degree family provides.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# BEYOND THE BLOCK-COUNT CAP: the flat quadratic form (detection not one-bit-per-block)

Design of a family whose detection is NOT block-organized, breaking the `|V| ≤ m` cap that
ceilings every block-menu family at `(2 + o(1))N`.  Worked on paper, detection identity frozen
in Lean (`ComputationalDepthNFrameQuadForm.lean`).

## The construction

    qform A x = ∑_{i,j} A_{ij}·x_i·x_j   over `F₂`,   x ∈ F₂^N,

with `A` the adjacency matrix of an expander (or random sparse graph) on the `N` input bits.
ONE input bit per vertex — NO blocks, NO clauses, NO literal menu, so no `Ω(log v)` addressing
cost and no block count `m` to bound the priced mass.

## Why detection is Θ(N)-dimensional and block-free

The polarization (`qform_shift`, PROVED): `qform A (x+δ) = qform A x + bilinSym A x δ + qform A δ`,
where `bilinSym A x δ = ∑ A_{ij}(x_iδ_j + δ_ix_j)` is the symmetric bilinear form of `A + Aᵀ`.
A direction `δ` is DETECTABLE (`qform_detect_dir`, PROVED) iff its bilinear functional
`x ↦ bilinSym A x δ` is nonzero — i.e. iff `δ` is NOT in the kernel of `A + Aᵀ`.  So the
detectable directions are the ROW SPACE of `A + Aᵀ`, of `F₂`-dimension `= rank_{F₂}(A + Aᵀ)`.

Now the cut.  For a balanced cut `(S, Sᶜ)`, restrict to `δ` supported on `S` and vary the
`Sᶜ`-completion: two `S`-rows `y, y'` are distinguished iff `(y − y')` has nonzero bilinear
functional against the `Sᶜ`-part, i.e. iff `(y−y')^T (A_{S,Sᶜ}) ≠ 0`.  So the number of
distinguishable `S`-rows is `2^{rank_{F₂}(A_{S,Sᶜ})}` — the cut rank is the `F₂`-RANK OF THE
CROSS-BLOCK `A_{S,Sᶜ}`.  For a good expander this rank is `Θ(N)` (a sparse `≈` full-rank
bipartite matrix), distributed over ALL `N` inputs — NOT `≤ m` block targets.

Hence `cut_row_capacity` gives `coneExcess ≥ rank_{F₂}(A_{S,Sᶜ}) − 1 = Θ(N)`, and with
`|ESS| = N` (every vertex of degree `≥ 1` is essential), `cbudget ≥ 2N + Θ(N) = (2+c)N`.  The
one-bit-per-block cap is broken: the priced mass is bounded by the cross-block RANK `Θ(N)`,
not the block count.

## The two honest caveats (why this is a step, not the summit)

1. **`qform` is EASY.**  A quadratic form is computable in `O(#edges) = O(N)` gates.  So the
   drag proving `cbudget ≥ (2+c)N` for `qform` is a valid lower bound for an EASY function —
   it DEMONSTRATES the N-frame drag method exceeds the block-count cap, but it is not a
   hard-function separation.  For P vs NP one needs cut-rank rigidity AND super-linear hardness
   in ONE family.  A quadratic form cannot be hard; a genuinely hard family with `Θ(N)`
   every-cut `F₂`-rank is the open target.
2. **Every-cut `F₂`-rank rigidity is explicit-hard.**  `rank_{F₂}(A_{S,Sᶜ}) = Θ(N)` at EVERY
   balanced cut is a rigidity-type condition: random sparse `A` satisfies it whp, but an
   EXPLICIT such `A` is the matrix-rigidity frontier.  (A spectral expander is NOT automatically
   enough — the expander mixing lemma controls the REAL spectrum, while `F₂`-rank of sub-blocks
   is a different, subtler quantity.)

## The sharpened frontier

The block-count cap is now understood as a consequence of BLOCK-MENU structure (detection
organized by menu-addressing units).  Flat detection (`qform`) removes it, at the cost of
hardness.  The genuine `(2 + Ω(1))N`-for-a-hard-function target is now precise: a family that
is (a) FLAT (detection = a `Θ(N)`-rank bilinear/higher form, no menu), (b) CUT-RIGID (that rank
survives every balanced cut), and (c) HARD (super-linear cbudget).  `qform` has (a)+(b) modulo
explicit rigidity, and fails (c); block-menu #SAT families have (c) and fail (a).  No known
explicit family has all three — that intersection is the honest remaining problem, and it is a
rigidity × hardness question, not another drag variant.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.

---

# PINNING DOWN EXPLICIT CUT-RIGID A: a design correction + the honest barrier

Attempt to pin down the explicit `A` for `qform`.  Working the polarization by hand caught a
design bug and located the barrier precisely; both frozen in Lean
(`ComputationalDepthNFrameCutRigid.lean`).

## The correction (a real bug in the flat-form design)

The polarization is `bilinSym A x δ = xᵀ(A + Aᵀ)δ` (`bilinSym_eq`, PROVED).  So for a
SYMMETRIC `A` — an undirected graph adjacency, which is what "expander adjacency" meant —
`A + Aᵀ = 2A = 0` over `F₂`, hence `bilinSym A ≡ 0` (`bilinSym_symm_zero`, PROVED): the
quadratic form of a symmetric `F₂` matrix is LINEAR (its diagonal), and detection is
identically zero.  The naive "expander-adjacency `A`" is DEGENERATE.

Fix: `A` must be an ORIENTATION — the strict upper triangle of a graph `M`, so
`qform A x = ∑_{i<j, M_{ij}=1} x_i x_j`.  Then `A + Aᵀ = M` (the undirected adjacency), the
polarization is `xᵀ M δ`, and the cut-rank of `qform A` across `(S, Sᶜ)` is
`rank_{F₂}(M_{S,Sᶜ})`.  So the cut-rigidity requirement lands on the UNDIRECTED graph `M`:
`rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` at every balanced cut.

## Why the explicit `A` cannot be honestly pinned down

The corrected target is: an explicit undirected graph `M` with `rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` at
EVERY balanced cut `(S, Sᶜ)`.  This is the `F₂`-rank version of matrix rigidity / high
rank-width-at-every-balanced-cut.  Honest status of the candidates:

- **Random / ε-biased `M`**: works whp / by the pseudorandom-rank property, but is not a
  PROVEN explicit every-cut bound.  ε-biased sets are explicit, and an ε-biased `M` is the best
  concrete candidate, but proving `rank_{F₂}(M_{S,Sᶜ}) ≥ cN` for ALL balanced `S` is exactly
  the rigidity-style statement that is not known for any explicit `M`.
- **Spectral expanders do NOT suffice.**  The expander mixing lemma bounds the REAL top
  singular value of `M_{S,Sᶜ}` (`≈ d|S||Sᶜ|/N`, a near-rank-1 REAL approximation) — it says
  nothing about the `F₂`-rank of the sub-block.  Extreme case: the cycle `C_N` (a sparse
  expander) has interval cuts of `F₂`-rank `2`.  So spectral pseudorandomness is the wrong
  handle.
- **Algebraic constructions** (Paley, projective-plane incidence, Cayley graphs) have known
  FULL-matrix `F₂`-ranks (Hamada-type formulas), but their sub-block ranks over `F₂` at every
  balanced cut are not controlled by any known theorem.

So: the reduction is EXACT and the target PRECISE (explicit every-balanced-cut `F₂`-rigid `M`),
but that target is an open explicit-rigidity problem.  I cannot pin down an explicit `A` with a
proof, and neither can the field at `Θ(N)` strength.  The honest deliverable is the correction
(orientation, `cut-rank = rank_{F₂}(M_{S,Sᶜ})`) and the precise open statement; the instantiation
awaits an explicit rigid `M`.

## The consolidated frontier (all routes)

`(2 + Ω(1))N` for a hard function needs FLAT + CUT-RIGID + HARD in one family.  The pieces:
`qform` gives FLAT + (rigid modulo explicit `M`) but not HARD; block-menu `⊕#SAT` gives HARD but
not FLAT (block-count-capped at `N/log N`).  The two open sub-targets are now sharp: (a) an
explicit every-balanced-cut `F₂`-rigid `M` (this section — rigidity frontier), and (b) a flat
family that is also hard (form-hardness frontier).  Both are recognized hard problems, not drag
variants.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ε-BIASED M FOR CUT-RIGIDITY: honest outcome — the wrong certificate (union-bound barrier)

Attempt to prove an explicit ε-biased `M` gives a weak every-cut `F₂`-rank bound.  Detection
bridge frozen in Lean (`ComputationalDepthNFrameEpsBias.lean`); the ε-biased bound itself worked
on paper with an HONEST negative outcome.

## The detection bridge (proved)

`bilinSym_units` (PROVED): `bilinSym A (e_a) (e_b) = A_{ab} + A_{ba}` = the `(a,b)` entry of
`M = A + Aᵀ`.  So the detection matrix of `qform A` is EXACTLY `M`; the cut-rank across
`(S, Sᶜ)` is `rank_{F₂}(M_{S,Sᶜ})`, and an induced cross-matching of size `r` gives `r`
independent detectable directions (`bilinSym_edge` is the atom).  The reduction to `M`-rigidity
is now exact and Lean-anchored.

## The ε-biased bound: it does NOT hold provably (and why)

- **Random `M` works.**  `Pr[corank ≥ t]` at a fixed cut `≈ 2^{-t²}`; union over `≤ 2^N` cuts
  needs `t > √N`, so a random `M` has `rank_{F₂}(M_{S,Sᶜ}) ≥ N/2 − O(√N) = Θ(N)` at EVERY
  balanced cut whp.  Target achievable, non-explicitly.
- **ε-biased FAILS.**  ε-biasedness controls linear tests (`|Pr[all zero] − 2^{-r}| < ε`).  The
  first-moment kernel bound is `E[#t-dim kernels] ≤ 1 + ε·2^{tN/2}`, so forcing corank `< t` at
  one cut needs `ε < 2^{-tN/2}`, and with the union over `2^N` cuts, `ε ≤ 2^{-Θ(N^{1.5})}` —
  seed `Θ(N^{1.5})`, no better than random.  A small-bias set (`ε = 1/poly`, seed `O(log N)`)
  does NOT survive.  ε-biasedness is a "few linear tests" tool; the every-cut kernel analysis
  has `2^{Θ(N)}` events.  **The union bound over exponentially many cuts is the barrier, and
  ε-biasedness cannot pay for it.**

## Honest verdict

ε-biased `M` does not provably give a weak every-cut bound — not because the bound is false
(random has it) but because the ε-biased CERTIFICATE (per-linear-test bias) is the wrong
certificate for an every-cut, exponentially-many-events property.  The gap between "random
works" and "ε-biased fails" IS the explicit-rigidity barrier, now sharply located at the
union-bound-over-cuts step.  A provable explicit every-cut bound needs a NON-per-cut certificate
(an algebraic every-cut induced-matching guarantee) — the open problem.  This closes the
ε-biased sub-question honestly: it is the wrong tool.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE INDUCED-MATCHING ROUTE: explicit cut-rigidity via expanders (sub-target (a) RESOLVED)

The ε-biased attempt failed on the union-bound-over-cuts barrier.  The induced-matching route
BYPASSES it, and it WORKS — correcting the earlier "spectral expanders don't suffice."  Core
frozen in Lean (`ComputationalDepthNFrameInducedMatch.lean`).

## The chain (explicit, no union bound)

    d-regular edge-expander M (explicit, Ramanujan), edge expansion h > 0
  ⟹ every balanced cut has ≥ h·N/2 crossing edges                           [expansion — a DETERMINISTIC every-cut guarantee]
  ⟹ a matching of size ≥ h·N/(2(2d−1))                                      [greedy: each edge kills ≤ 2d−1]
  ⟹ an INDUCED matching of size r ≥ Θ(N/d²)                                 [greedy: each edge blocks ≤ 2d others]
  ⟹ M_{S,Sᶜ} has an r×r IDENTITY submatrix ⟹ rank_{F₂}(M_{S,Sᶜ}) ≥ r = Θ(N)  [linear algebra]

The crucial point: edge expansion is a "for every cut" guarantee that is PROVEN for explicit
expanders (via the spectral gap / Cheeger) — NO union bound over cuts.  The ε-biased approach
died on the union bound; the induced-matching approach never invokes one.

## The correction

The earlier claim "spectral expanders do not suffice" was about the spectral-RANK approach
(bounding `F₂`-rank via the real spectrum — which genuinely fails).  The COMBINATORIAL route
— edge expansion → matching → induced matching → identity submatrix → `F₂`-rank — is different
and WORKS.  A cycle has low-rank interval cuts because it is NOT an edge-expander (`h → 0`); a
constant-degree edge-expander has `rank_{F₂}(M_{S,Sᶜ}) = Θ(N)` at every balanced cut.

## What is proved (Lean) and what is cited (paper)

- **Lean (this file), clean axioms**: `induced_matching_distinct` — an induced matching
  (identity detection matrix `bilinSym A (e_{t k})(e_{s l}) = [k=l]`, which by `bilinSym_units`
  IS the identity submatrix of `M`) gives `2^r` pairwise-distinguished tuple rows under
  completions.  So the induced matching yields cut-rank `≥ r` via `cut_row_capacity`.  Plus the
  bilinearity infrastructure (`bilinSym_add_right`/`_sum_right`/`_zero_*`).
- **Cited (standard graph theory)**: edge expansion → matching → induced matching (greedy).

## Honest status: sub-target (a) RESOLVED; (b) unchanged

Explicit cut-rigid `M` is DONE: a constant-degree Ramanujan graph, provably `Θ(N)` `F₂`-rank at
every balanced cut, giving `cbudget(qform) ≥ (2+c)N` for the flat quadratic form over that
expander — the drag method now provably EXCEEDS the block-count cap on an EXPLICIT family.  The
remaining caveat is sub-target (b), UNCHANGED: `qform` is EASY (`O(dN)` gates), so this is a
`(2+c)N` lower bound for an easy function — a demonstration, not a hard-function separation.
`(2 + Ω(1))N` for a HARD function still needs cut-rigidity AND super-linear hardness in one flat
family; the rigidity half is now explicit, the hardness half remains open.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# SUB-TARGET (b): FLAT + HARD — the drag is a linear method (ceiling at 3N)

Attacking sub-target (b) — a flat family that is also super-linearly HARD — forced a precise
look at what the drag can prove, and the honest finding is a ceiling on the METHOD.  Frozen in
Lean (`ComputationalDepthNFrameDragCeiling.lean`).

## The ceiling

The drag proves `cbudget ≥ 2·|ESS| + coneExcess`, and it lower-bounds `coneExcess` ONLY via cut
capacity: `cut_row_capacity` gives `|Y| ≤ 2^{coneExcess+1}` for a distinguished row family
`Y ⊆ {0,1}^N`, so the certificate is `coneExcess ≥ log₂|Y| − 1`.  But `|Y| ≤ 2^N`
(`rowFamily_card_le`, PROVED — there are only `2^N` possible rows), so `log₂|Y| ≤ N`.  With
`|ESS| ≤ N`, the drag-provable bound is `2·|ESS| + coneExcess ≤ 2N + N = 3N`
(`drag_linear_ceiling`, PROVED).  **The N-frame drag is structurally a linear (`≤ 3N`)
lower-bound method.**

## Why "flat + super-linearly-hard" is out of the drag's reach

A flat family gives the MAXIMAL drag result: cut-rank `Θ(N)` ⟹ `coneExcess ≥ Θ(N)` ⟹
`cbudget ≥ (2+c)N`.  Making the function HARDER cannot help, because the drag would need a
certificate for `coneExcess = ω(N)`, and cut capacity structurally cannot supply one: a
distinguished row family cannot exceed `2^N` members, so `log₂|Y| ≤ N` no matter how hard the
function.  So the hardness of the function is INVISIBLE to the drag beyond `O(N)` — flat + hard
is doubly obstructed (flat/low-degree tends to be easy AND the drag can't exploit hardness).

## Honest verdict and the forward direction

This is a ceiling on the TECHNIQUE (cut capacity for `coneExcess`), not on circuit complexity.
The drag's actual product — an explicit `(2+c)N` for the flat cut-rigid family (`qform` over a
Ramanujan graph, sub-target (a)) — is a genuine LINEAR circuit lower bound; the live question
there is whether `c` competes with gate-elimination (`~3.1N`).  Going SUPER-linear (the P-vs-NP
direction) needs a certificate for `coneExcess` that is NOT single-cut capacity — a
recursion / self-improvement / amplification escaping the one `log₂|Y| ≤ N` bound (the annulus
does not: it also gives `log₂|Y| ≤ coneExcess + k`, and `log₂|Y| ≤ N` still caps it).  That
different mechanism is the honest next target for super-linear; the drag itself has been pushed
to its structural ceiling.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# CONEEXCESS AMPLIFICATION: the recursion that escapes log|Y| ≤ N

Design of a coneExcess amplification escaping the single-cut `log|Y| ≤ N` ceiling.  The
arithmetic (the escape is real) is frozen in Lean (`ComputationalDepthNFrameConeAmplify.lean`);
the recursion for an explicit family is the honest open target, precisely located.

## The mechanism: recursion, not a bigger cut

A single cut caps at `log|Y| ≤ N`.  A RECURSION sums many small certificates across scales:

    coneExcess(f_{2N}) ≥ 2·coneExcess(f_N) + c·N     ⟹     coneExcess(f_N) ≥ c·N·log₂N.

`coneExcess_amplify` (PROVED): `2·T k + c·2^{k+1} ≤ T(k+1)` ⟹ `c·(k·2^k) ≤ T k` — the recurrence
solves to `Θ(N log N)` (`N = 2^k`).  `amplify_exceeds_linear` (PROVED): with `c ≥ 1`, `T` exceeds
EVERY linear bound `b·N`, so it breaks the `3N` drag ceiling.  **The crucial point**: each level's
`+c·N` term is certified by a cut of size `c·N ≤ (level's input count)` — NO single cut ever
exceeds `log|Y| ≤ (level)`.  The recursion never violates the per-cut bound at any scale; it
ACCUMULATES `log N` sub-`N` certificates.  That is exactly how one escapes the ceiling without
breaking it.

## The candidate family: recursive rigid mixing

    f_{2N}(x) = g_N( f_N(x₁), f_N(x₂) )   on disjoint inputs x₁, x₂,

with `g_N` a CUT-RIGID mixing (a `qform`-over-Ramanujan on the `2·(#outputs)` intermediate wires,
resolved explicit in the induced-matching file) forcing `+c·N` fresh `coneExcess`, and the two
`f_N` sub-cones DISJOINT so their `coneExcess` adds.  Structurally this yields the recursion.

## The open step (precisely located) and the barrier

The recursion inequality requires a MINIMAL circuit for `f_{2N}` to (i) contain two disjoint
sub-cones each of `coneExcess ≥ coneExcess(f_N)`, and (ii) pay a fresh `+c·N` for the mixing — it
CANNOT share or avoid the sub-instances.  Minimal circuits need NOT respect the recursive
definition, so proving no-avoidance is the crux — and it IS the general super-linear circuit lower
bound problem (open).  The specific barrier: linear-size superconcentrators exist, so pure
CONNECTIVITY between sub-instances is achievable in linear size — the recursion cannot rest on
connectivity; it must force fresh `coneExcess` via the RIGIDITY of `g_N` at every scale (which the
induced-matching file makes explicit per level).  So the missing ingredient is a proof that
rigid mixing at each scale cannot be amortized/shared across the recursion — a scale-composition
rigidity statement.

## Honest status

The amplification's ARITHMETIC is proved sound: the recursion escapes `log|Y| ≤ N` and reaches
`Θ(N log N)`, past the `3N` ceiling.  The recursion itself, for an explicit `f`, is the
open target — equivalent to general super-linear circuit lower bounds, with the honest missing
ingredient named (scale-composition rigidity, beyond the linear-superconcentrator barrier).  This
is the sharpest reduction the arc reaches: super-linear ⟺ prove the rigid-mixing recursion holds
under scale composition.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE BASE CASE: two disjoint rigidities add (detection level) — and the Uhlig gap

Proving the base case of the recursion (two disjoint rigid sub-cones ⟹ coneExcess adds).
Detection-level direct sum frozen in Lean (`ComputationalDepthNFrameDirectSum.lean`); the
cone-level lift is located precisely at the Uhlig barrier.

## What is proved (detection level)

- `bilinSym_cross_zero` (PROVED): coordinates in different blocks do not cross-detect
  (`A_{ab}+A_{ba} = 0 ⟹ bilinSym A (e_a)(e_b) = 0`).  Two disjoint copies give a block-diagonal
  `A`, hence no cross-detection.
- `combined_detection_identity` (PROVED, THE DETECTION DIRECT SUM): two induced matchings on
  disjoint blocks (block-internal identities, cross-detection zero) combine to a SINGLE induced
  matching over `Fin r₁ ⊕ Fin r₂` with identity detection.  With `induced_matching_distinct`, the
  two rigidities give `2^{r₁+r₂}` distinguished rows — cut-rank adds, `rank(F) ≥ r₁ + r₂`.

So two disjoint rigidities DO add — at the detection/rigidity level, provably, no interference.

## The gap: detection-level add is LINEAR; the recursion needs the CONE-level (Uhlig) direct sum

The detection-level direct sum gives `rank(F) ≥ r₁ + r₂ ≤ (#inputs of F)` — a LINEAR bound, via
cut capacity, squarely in the `log|Y| ≤ N` regime.  The recursion needs `coneExcess(f_{2N}) ≥
2·coneExcess(f_N)` with `coneExcess(f_N)` SUPER-LINEAR (by induction) — and cut capacity cannot
reach it (`≤ 2N < 2·coneExcess(f_N)`).  It requires the two `f_N` sub-CONES of a MINIMAL circuit
to be DISJOINT — the DIRECT SUM problem for `coneExcess`.

That is OPEN, and guarded: **Uhlig's mass-production theorem** shows the direct sum for circuit
SIZE is FALSE in general — some functions compute many copies in `(1+o(1))×` the single-copy cost,
by sharing a universal part.  So cone disjointness cannot be assumed; the detection-level base
case (proved) does NOT lift to the cone level without a proof that the specific rigid `g` admits
NO mass-production sharing — a DIRECT-SUM-HARDNESS statement for an explicit function, itself open.

## Honest status — the boundary of the arc, precisely located

The base case is TRUE and proved where provable — the detection/rigidity direct sum (disjoint
rigidities add, no interference).  The remaining gap is exactly ONE named statement: the
CONE-level direct sum for the explicit rigid `g` (its two disjoint copies have disjoint minimal
sub-cones), i.e. `g` is direct-sum-hard / admits no Uhlig mass production.  This is the honest
boundary: everything up to and including the detection-level direct sum is proved and clean; the
one step past it (cone-level direct sum) is open, equivalent to direct-sum-hardness, guarded by
Uhlig.  The full chain to super-linear is now: [proved] rigidity via expanders + detection direct
sum ⟹ [open, Uhlig] cone-level direct sum ⟹ [proved arithmetic] recursion unrolls to Θ(N log N).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# UHLIG CHECK: does the rigid g admit mass production?  NO — wrong complexity regime

Checked whether the explicit rigid `g` (expander quadratic form) admits Uhlig mass production.
Outcome: NO, and it CORRECTS the previous step's "guarded by Uhlig" claim.  Frozen in Lean
(`ComputationalDepthNFrameUhligCheck.lean`).

## The regime check

Uhlig's mass production: computing `f` on `m` inputs costs `≤ (1+o(1))·2^n/n` (the Lupanov
worst-case bound).  A SAVINGS over `m·C(f)` ONLY when `C(f)` is near the max `2^n/n` — a
near-maximally-hard function whose expensive universal table amortizes across copies.  For EASY
`f` with `C(f) ≪ 2^n/n`, the Uhlig construction costs `~2^n/n ≫ m·C(f)` — USELESS.

`g = qform A` (sparse expander form) has `C(g) = O(dN)` — LINEAR, exponentially far from `2^N/N`.
Recursive `f_N = g(f_{N/2}, f_{N/2})` has `C(f_N) = O(N log N)` — QUASI-linear.  Neither is in
the exponential regime where Uhlig applies.  **So `g` does NOT admit Uhlig mass production.**

## Correction to the previous step

The base-case file said the cone-level direct sum is "guarded by the Uhlig barrier."  That was
imprecise: Uhlig guards the direct sum for near-maximally-hard functions; `g`/`f_N` are easy, so
Uhlig does not bind here.  The specific obstruction cited does NOT apply.

## The algebraic evidence (Lean)

- `qform_additive_disjoint` (PROVED): non-cross-detecting inputs (`bilinSym A x y = 0`, i.e. two
  disjoint copies under block-diagonal `A`) satisfy `qform A (x+y) = qform A x + qform A y` — the
  copies decompose ADDITIVELY, disjoint monomial supports, no algebraic interaction, no shared
  universal part to amortize.
- `bilinSym_add_left` + `qform_additive_pair` (PROVED): the `k`-copy version — pairwise
  non-cross-detecting inputs are additively independent under `qform`.

## Honest status — barrier removed, but direct sum still open (weaker reason)

Removing the Uhlig barrier is a real (if modest) correction — the specific obstruction does NOT
apply to our easy `g`.  But it does NOT resolve the cone-level direct sum.  The direct sum for
circuit `coneExcess` is OPEN in general (even for easy functions) because a minimal circuit could
share via NON-table mechanisms (algebraic cancellation, bilinear tricks).  `qform_additive_disjoint`
shows no ALGEBRAIC interaction (disjoint monomials) — EVIDENCE the copies are independent, but not
a proof that a minimal circuit cannot share via cancellation.  Updated status: the cone-level
direct sum for `g` is OPEN but NOT Uhlig-blocked; what remains is the general direct-sum problem
for a quasi-linear function with additively-independent copies — no known obstruction, no known
proof.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# RULING OUT THE CANCELLATION ROUTE FOR qform (base case)

Can two disjoint copies of `g = qform A` be computed with `< 2·C(g)` gates via `F₂` cancellation
(linear mixing so cross-terms cancel)?  For the base case (`qform`): NO — via an invariant
cancellation cannot touch.  Additive-rank witness frozen in Lean
(`ComputationalDepthNFrameCancellation.lean`).

## Why cancellation can't help

`F₂` cancellation IS a linear change of variables.  The detection matrix `M = A + Aᵀ` is a
FUNCTION invariant (`bilinSym A (e_a)(e_b) = M_{ab}`), fixed by `qform`, unchanged by any circuit
linear mixing.  Two facts bind every circuit:
  (1) `rank_{F₂}(M)` is invariant under invertible change of variables — cancellation cannot lower it.
  (2) `rank_{F₂}(M)` is ADDITIVE under direct sum: `rank(M₁ ⊕ M₂) = rank(M₁) + rank(M₂)`.
By Mirwald–Schnorr (multiplicative complexity of a quadratic form over `F₂` is `≥ rank(M)/2`), the
AND-gate count for the direct sum is `≥ (rank M₁ + rank M₂)/2` = the sum of the per-copy bounds.
No linear mixing saves products.  Cancellation ruled out for `qform`.

## The additive-rank witness (Lean)

- `direct_sum_distinct` (PROVED): two induced matchings on disjoint blocks (block-internal
  identity, zero cross-detection = block-diagonal `M`) combine to a pairwise-distinguished family
  over `Fin (r₁+r₂)`.  So the direct sum carries an `(r₁+r₂)`-identity submatrix of `M`,
  `rank(M₁ ⊕ M₂) ≥ r₁ + r₂` — a FUNCTION property holding for EVERY circuit, immune to
  cancellation.  (Reindexes `combined_detection_identity` over `finSumFinEquiv` and applies
  `induced_matching_distinct`.)

## Honest status — base case resolved; super-linear lift untouched

For `qform` the rank bound is (up to constants) TIGHT — `coneExcess(qform) = Θ(N) = Θ(rank)` — so
the additive, cancellation-invariant rank forces `coneExcess(qform^{(2)}) = 2·Θ(N)`: the base-case
direct sum HOLDS and cancellation is RULED OUT.  This does NOT lift to the recursive `f_N`, whose
`coneExcess` is SUPER-linear and exceeds its rank; there the rank bound is not tight, so
cancellation in COMBINING sub-results is not ruled out by rank.  So the cancellation route is
CLOSED for the base case (`qform`), and the ONLY remaining gap is the super-linear lift
(`coneExcess(f_{2N}) ≥ 2·coneExcess(f_N)` where the doubled quantity exceeds the rank).
Mirwald–Schnorr cited, not re-formalized; the additive-rank witness is proved.

## Updated full chain to super-linear

[PROVED] rigidity via expanders + detection direct sum + `qform` cancellation-ruled-out (base
case) ⟹ [OPEN, super-linear only] cone-level direct sum for the RECURSIVE `f_N` (coneExcess >
rank, so neither cut capacity nor the rank/Mirwald–Schnorr bound reaches it) ⟹ [PROVED arithmetic]
recursion unrolls to Θ(N log N).  The gap has narrowed to exactly the regime `coneExcess > rank` —
the super-linear lift.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE SEARCH FOR A NON-RANK CERTIFICATE FOR coneExcess — the two failure modes

Three barriers (cut capacity, Mirwald–Schnorr, Uhlig) all reach exactly `rank ≤ N`.  Searched for
a non-rank certificate for `coneExcess` that could reach super-linear.  Honest result: none found
(this IS the general super-linear problem), but the search PRODUCED a precise characterization of
why.  Frozen in Lean (`ComputationalDepthNFrameNonRankCert.lean`).

## Reframing: there is NO certificate for coneExcess in isolation

Every function has a FORMULA (fan-out-1 circuit), and a formula has `coneExcess = 0`.  So NO
function forces `coneExcess > 0` — there is no lower bound on `coneExcess` per se.  The drag's
`coneExcess ≥ cut-rank` binds only SMALL (shared) circuits, not every circuit.  The real object is
the length↔coneExcess TRADEOFF: `length ≥ 2|ESS| + coneExcess`.  A certificate must lower-bound
`coneExcess` OR give a length bound in the LOW-fanout regime — exactly where formula (non-rank)
bounds live.

## The two failure modes

- RANK route (cut capacity): `coneExcess ≥ cut-rank ≤ log₂|Y| ≤ N` (`rowFamily_card_le`).  Fails
  by the INPUT-DIMENSION cap: capped at `N`, linear.
- FORMULA route (Nechiporuk): a formula LB `F` (e.g. `N²/log N`) transfers to circuits ONLY through
  the unfolding loss `formulaSize ≤ length·2^{coneExcess}` (excess fan-out `E` unfolds to a formula
  of size `≤ length·2^E`).  So it yields `length ≥ F/2^{coneExcess}`, which COLLAPSES:
  - `formula_cert_collapse` (PROVED): at `coneExcess = ⌈log₂ F⌉`, `F/2^{coneExcess} ≤ 1` — the
    formula certificate gives nothing once fan-out reaches `log₂ F`.
  - `formula_cert_ceiling` (PROVED): the best guaranteed `max(coneExcess, F/2^{coneExcess})` over
    the circuit designer's fan-out choice is `≤ ⌈log₂ F⌉` — so the formula route certifies at most
    `length ≥ log₂ F`, LOGARITHMIC, even from a super-linear formula bound.

## Honest verdict

No non-rank certificate reaching super-linear was found — none is known; this is the general
super-linear circuit lower bound problem.  What the search produced is a precise characterization
of WHY: the two available non-rank routes fail in ORTHOGONAL ways —
  • RANK route: capped at input dimension `N` (a super-linear certificate must measure something
    NOT bounded by `N`);
  • FORMULA route: degrades as `2^{-coneExcess}`, collapses at `log₂ F` (must NOT lose under fan-out).
A working certificate must dodge BOTH — uncapped by input dimension AND stable under fan-out.
Every known technique has exactly ONE of these two failure modes; that orthogonality is a
structural reason the problem is open.  This file freezes the formula-route collapse; the rank cap
is `rowFamily_card_le`.  This is the honest floor of the arc: the super-linear step requires a
certificate outside both known families, and the two failure modes now name precisely what it must
avoid.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# SCOPING THE IRREDUCIBLE-DEMAND CERTIFICATE — coherent, dodges both, one new crux

The non-rank search left exactly one shape past BOTH failure modes (input-`N` cap, `2^{-coneExcess}`
fan-out decay): a certificate measuring IRREDUCIBLE DEMAND — how many times a value must be present
across the computation.  Scoped it: defined the object, VERIFIED both dodges in Lean, located the
single new obstruction.  Frozen in `ComputationalDepthNFrameDemandCert.lean`.

## The object

A demand structure for `f`: a family `{(Vᵢ, Dᵢ)}` where any circuit must make `Vᵢ` present at every
site in `Dᵢ`.  A value demanded `K = |Dᵢ|` times forces ROUTE (fan-out `K−1`, charged to
`coneExcess`) or RECOMPUTE (`K−1` extra copies at unit cost `c ≥ 1`, charged to `length`).  Both
land in `length ≥ 2|ESS| + coneExcess`.  Certificate: `length ≥ 2|ESS| + Σᵢ(Kᵢ−1)` when demands
are IRREDUCIBLE.

## The two dodges, VERIFIED

- `recompute_charge` (PROVED): `d ≤ d·c` for `c ≥ 1` — recomputing never beats routing's `d = K−1`
  charge.  So a demand costs `≥ K−1` under EITHER strategy: the charge does NOT decay under fan-out
  (dodges the formula route's `2^{-coneExcess}` collapse).
- `demand_no_strategy_beats_total` (PROVED): for any route/recompute mix, `Σ(Kᵢ−1) ≤ Σ chargeᵢ` —
  no strategy beats the total demand.
- `demand_uncapped` (PROVED): the demand total exceeds every `N` and every `T` — unlike `rank ≤ N`,
  demand is NOT bounded by the input dimension (dodges the rank route's `N` cap).
- `demand_certificate` (PROVED): given irreducibility (`hcharge`) and the ledger, `2|ESS| + Σdᵢ ≤
  length` — the demand total transfers to a `length` lower bound that can be super-linear.

## The one new obstruction — irreducibility under SHARING (= rigidity)

The dodges hold, so the SHAPE is sound.  But demand replaces the two orthogonal failure modes with
ONE non-automatic requirement: IRREDUCIBILITY.  Demand is reducible by SHARING INTERMEDIATE VALUES
(compute partial combinations once, reuse) — exactly what makes linear-size superconcentrators and
`O(N log N)` linear circuits possible.  For the linear case (`x ↦ Mx`), irreducible demand IS the
linear-circuit complexity of `M`, and proving it super-linear is Valiant's matrix-RIGIDITY program
(open).  So the demand certificate does NOT evade the open problem — it RELOCATES it: from "beat two
orthogonal failure modes" to "prove one demand structure is irreducible under sharing."

## Honest status

The certificate is coherent and provably dodges both known failure modes (verified).  Its
irreducibility hypothesis is the open crux, coinciding with rigidity for the linear case — I did
NOT prove irreducibility for any explicit `f` (that is the open problem).  What the scoping
delivers: the demand certificate is the unique shape past both failure modes, and its single
remaining requirement is now named and connected to rigidity — a concrete (open) target.
Route/recompute floor, no-strategy-beats-total aggregate, uncapping, and the assembled certificate
are proved; irreducibility is the hypothesis.

## Arc map (frozen, honest)

drag caps at 3N (rank ≤ N) → recursion escapes (arithmetic proved) → base case: detection direct
sum proved, Uhlig doesn't bind (g easy), cancellation ruled out for qform → super-linear needs a
non-rank coneExcess certificate → the two failure modes (rank `N`-cap; formula `2^{-coneExcess}`
collapse) → the demand certificate dodges both, relocating the open problem to irreducibility =
rigidity.  Everything at/below the rank frontier is proved; the super-linear step is one named,
open, rigidity-equivalent requirement.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
