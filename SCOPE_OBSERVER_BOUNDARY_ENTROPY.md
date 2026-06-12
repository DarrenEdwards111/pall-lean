# Observer boundary entropy — a mathematical note

A reframing of the Route-F obstruction as **observer interface complexity** ("thermodynamic boundary of an
observer"), per the meta-complexity / branching-holography idea.  The aim: turn the metaphor into a concrete
complexity invariant, state the central conjecture precisely, and position it against known theory.

**Status.** The *invariant* and its basic laws are formalized and proved
(`ComputationalDepthObserverBoundary.lean`).  The *thermodynamic / spacetime-hypercube* language is
intuition, flagged as such.  The *central conjecture* is open and equal in strength to `P ≠ NP`; nothing
here proves it.

---

## 1. The invariant (rigorous)

For a deterministic machine and a cut, define the **observer boundary entropy**

  `B(M, cut) = log₂ |crossing sequences at the cut| ≤ C · log₂ A`

(`A` = size of the head/state alphabet, `C` = number of crossings).  An "observer" reading the computation
across the cut can retain only this much interface information.

**Proved (from the Route-F crossing-sequence bound `rank ≤ A^C`):**
* `log₂ rank ≤ B` (`rank_le_two_pow_boundaryEntropy`): boundary entropy upper-bounds the log of the SPDP /
  communication rank an observer can resolve.
* `B = O(log n) ⇒ rank = poly(n)` (`lowBoundary_poly_rank`): a low-boundary observer sees polynomial rank.

So this is a real quantity with real laws, **not** metaphor.

## 2. The P-observer / NP-observer picture

* **P-observer** — bounded boundary entropy `B = O(log n)`.  Sees the computation through low-rank,
  few-lane, few-crossing summaries (Route F: polynomial profiles).  By §1, resolves only `poly(n)` profiles.
* **NP-observer** — a *branching* boundary: it may expose all witness branches of the Boolean hypercube
  `{0,1}^n` at once.  Its witness boundary is `Ω(n)` (exponentially many faces/sectors).
* **Separation question** — can a P-boundary observer *compress* the NP branching boundary without losing
  decisive witness information?

This is exactly the Route-F question in new clothes: the P-side must force every SAT-decider into
low-boundary geometry.

## 3. Boundary *reuse* is the crux (this is what Route F exposed)

The decisive lesson from the formalized arc: the obstruction is **boundary reuse, not boundary size**.
`SpreadObstruction` proved that a small-space ("small-boundary") observer can *recycle* a tiny interface
`Θ(T)` times — generating large *temporal* crossing entropy from a small *spatial* boundary (the shuttle).
So the right invariant is **crossing entropy** (boundary × reuse), and "P-observer" must mean *low total
crossing entropy*, which a small-space machine can violate.

  P-style observer  :=  total crossing entropy `B = O(log n)`  (boundary size × reuse both controlled).

## 4. The central conjecture (open, `P ≠ NP`-strength)

> **Observer-boundary conjecture.**  For NP-complete families (e.g. SAT), *every* faithful deterministic
> observer has super-logarithmic total crossing entropy: `B = ω(log n)`.

By §1–§3 this is **equivalent** to the Route-F open lemma — the `T/log n` space (= spread) lower bound for
SAT — hence to an explicit super-polynomial circuit lower bound, hence `P`-vs-`NP`-strength.  Renaming does
not prove it; the value is a possibly-more-tractable *language* for the same obstruction.

## 5. Positioning against known theory (what tools might transfer)

| Framework | Relation to observer boundary entropy |
|---|---|
| **Communication complexity** | `B` at a cut *is* a (one-way, deterministic) communication measure; `log rank ≤ B` is the rank↔communication link.  Lower bounds on `B` = communication lower bounds — but here the *partition is chosen by the machine*, the hard part. |
| **Branching programs** | A width-`w` BP has boundary `log w` per layer; `B` is the layered interface entropy.  Known BP lower bounds (`Nečiporuk`, time–space for BPs) are the closest existing tools — and cap at `n²/log n`, below what is needed. |
| **Time–space tradeoffs** | `B = ω(log n)` for all poly time ⟺ SAT needs space `≥ T/log n`.  Known SAT tradeoffs (FLVV / Williams: time `≥ n^{1.8}` for sub-poly space) are far weaker — they bound time given space, not space given time. |
| **Proof complexity** | Crossing sequences ≈ the "memory" of a refutation across a cut; boundary entropy ≈ space measures in proof systems, where strong lower bounds *are* known — a candidate source of technique. |
| **Holographic algorithms / matchgates** | "Branch boundary as a sector/face" is the holographic intuition; matchgate tensor contractions are low-boundary computations.  Suggests the P-observer = bounded-treewidth / low-rank tensor contraction. |
| **Meta-complexity / MCSP** | `B` is a description-length-flavored measure of *the observer's view*.  "P = phenomena admitting low-boundary observers; NP = locally-checkable branching geometry" frames P-vs-NP as: does every locally-checkable branching geometry admit a low-boundary observer? — a clean meta-complexity statement, but still open. |

## 6. Honest assessment

* **Useful**: yes, as *language*.  It unifies Route F's crossing bound, the small-space obstruction,
  communication/BP/proof-space lower bounds, and the holographic "boundary/sector" picture under one
  invariant — and that invariant has proved laws (§1).
* **Not a shortcut**: the central conjecture (§4) is the same open problem.  The thermodynamic/spacetime
  dressing is intuition; the content is crossing/communication/space lower bounds for SAT, all open at the
  required strength.
* **Most promising transfer**: §5's *proof-complexity space* and *branching-program* rows — those are the
  regimes where super-logarithmic boundary/space lower bounds are actually proved (for restricted models).
  The honest research question is whether any of those techniques can be made to apply to a *machine-chosen*
  partition / a faithful observer of an arbitrary SAT-decider, which is exactly where all of them currently
  stop.

**Bottom line.** The observer-boundary-entropy framing is a legitimate, formally-anchored reframing of the
exact obstruction Route F exposed.  It may suggest importing proof-complexity-space or branching-program
techniques.  It does not, by itself, prove anything new — the central conjecture is `P ≠ NP` in a new
language — and this note says so plainly.

---

## 7. Option C delivered — a PROVED positive proof-space observer lower bound (Tseitin)

§5's proof-complexity row is now a **theorem**, not a suggestion.  The proof-space observer of a refutation
holds, at each step, a configuration of clauses; its boundary is the largest configuration ever held — the
**total space** (`configSize` = literal occurrences).  This is the faithful proof-space instance of the
invariant.  We prove it is super-constant for expander-Tseitin.

* `ComputationalDepthResolutionSpace.lean` — the standard **blackboard / configuration** proof-space model
  (`start` / `download` / `infer` / `erase`), `configSize`, `Blackboard.totalSpace`, and the abstract
  **total-space band theorem** `totalSpace_ge_of_medium_wide`: run on the configuration sequence, the first
  config whose max clause-measure reaches `t` holds a *freshly inferred* medium-measure clause (parents both
  `< t`), hence wide by the medium→wide link, hence the config's total space `≥ W`.  Clean axioms.
* `ComputationalDepthExpanderTseitinSpace.lean` — `tseitin_totalSpace_lower_bound`: every blackboard
  refutation of the expander-Tseitin axioms has total space `≥ c·t` (`t ≤ |V|/4`).  Reuses the *already
  proved* `measure_resolvent_le`, `width_ge_of_medium`, `root_bound`.  **No** Atserias–Dalmau space–width
  inequality and **no** locking lemma assumed.  Clean axioms.
* `ComputationalDepthTseitinSpaceObserver.lean` — the observer restatement
  (`tseitin_proofSpace_observer_lower_bound`), the concrete `Kₙ` family
  (`completeGraph_tseitin_space_lower_bound`: boundary `≥ ⌊n/4⌋ = Θ(|V|)`, super-logarithmic), and
  `tseitin_proofSpace_observer_unbounded`: for every `K` there is an instance forcing boundary `≥ K`.  So
  this observer boundary is provably **not** `O(1)` — exactly the separation-from-constant that the fixed-cut
  EQUALITY bound (§A) could not achieve.

**The contrast that matters.**  This is a genuine, unconditional, super-constant observer-boundary lower
bound — in the *restricted* resolution proof-space observer.  It is the honest instance of the principle in
the regime where such bounds are provable.  It is **not** the general machine-decomposition observer of an
arbitrary SAT-decider (the central conjecture §4, still open, `= CookLevinFrontierHyp`).  What §5 predicted
("most promising transfer: proof-complexity space") is now realized as Lean mathematics, with the boundary
between "provable here" and "open there" drawn precisely.

---

## 8. The branching abstraction and the continuation bridge (Option B, realized + anchored)

Option C is anchored; Option B is now the geometric abstraction *over* it, with its central implication
finally **proved** rather than assumed.

* `ComputationalDepthBranchingObserver.lean` — `BranchingObserver` (boundary entropy + `view` into
  `Fin (2^entropy)`); `many_nonmergeable_sectors_force_boundary`: `K` non-mergeable sectors ⇒ entropy
  `≥ log₂ K` (the holographic principle, generalizing `foolingSet_forces_boundary`).  Hierarchy: fixed-cut
  ✅insufficient · proof-space ✅ (Option C) · branching ✅ · general open.  Plus `Nonmergeable.card_le` and
  the forced-merging contrapositive `not_nonmergeable_of_card_gt`.
* `ComputationalDepthHypercubeWitnessObserver.lean` — a concrete SAT instance (`φ = x₀`) through the
  abstraction, exhibiting **both regimes** on the same witness hypercube: a faithful transcript observer is
  forced to boundary `≥ n` (`witnesses_force_boundary`, `transcript_realizes_bound`), while a lossy
  single-coordinate projection observer **merges** the witnesses (`projection_merges`) — the
  non-mergeability hypothesis is genuinely non-trivial, and easy instances escape it.
* `ComputationalDepthContinuationObserver.lean` — **the continuation bridge** (the heart of Option B): a
  `Faithful` observer (boundary state determines behavior on *every* continuation) over a `Separated` set (a
  communication fooling set) keeps it non-mergeable — `faithful_separated_nonmergeable`.  So
  `faithful_separated_forces_boundary` **derives** the boundary bound from *correctness over continuations*,
  not from an assumed hypothesis.  Instantiated on EQUALITY (`equality_continuation_forces_boundary`): every
  faithful observer of the `prefix|suffix` split has boundary `≥ n`.

**The wall, now at exactly one quantifier.**  The faithfulness→boundary implication is a theorem; EQUALITY
shows a fixed-decomposition super-log bound is real *and still insufficient* (EQUALITY is `O(n)`-size under
another split).  All that remains open is the **minimum over admissible decompositions** for a hard family —
i.e. `≥ ω(log n)` boundary under *every* faithful split, which is `CookLevinFrontierHyp` / the central
conjecture §4.  Nothing here asserts it; the contribution is that everything *up to* that one quantifier is
now proved.

* `ComputationalDepthDecompositionGap.lean` — makes the insufficiency a **theorem**: a finite-memory
  streaming (`StreamObserver`) decider computes EQUALITY with boundary `1`, while the single-cut faithful
  observer needs `≥ n` (`equality_decomposition_gap`).  So a single decomposition's bound does not
  lower-bound the minimum — "the machine chooses the decomposition", proved.
* `ComputationalDepthMinBoundaryRealized.lean` — the `min`-over-decompositions quantifier is **achieved** in
  the resolution proof-space class: `minProofSpaceBoundary` (`sInf` over all refutations) is `≥ c·t` for
  expander-Tseitin (`tseitin_minProofSpaceBoundary_ge`).  The hard quantifier is provable where the class is
  restricted; open for general machines.

---

## 9. Calibration: rederiving the AC⁰[p] (Razborov–Smolensky) lower bound through the invariant

The test of whether the observer-boundary method crosses from proof complexity into **circuit complexity**:
can it rederive a known circuit lower bound?  `ComputationalDepthObserverAC0pCalibration.lean` shows **yes**,
and it is a rederivation, not a relabel — the dimension-counting heart of Razborov–Smolensky
(`Layer4.dim_bound_general`) *is* the observer-boundary principle in linear-algebra form:

| observer notion | RS / linear-algebra notion |
|---|---|
| boundary entropy | feature-space dimension `Module.finrank K (feature)` |
| non-mergeable behaviors | linearly independent functions — full space on `G` has dimension `|G|` |
| faithful observer | feature `= ⊤` (expresses every behavior on `G`) |
| low-boundary observer | `AC⁰[p]` low-degree surrogate: dimension `≤ #monomials` |

* `DimObserver.faithful_boundary` — a faithful observer has boundary `≥ |domain|` (the linear fooling
  principle, the exact analogue of `many_nonmergeable_sectors_force_boundary`).
* `ac0pObserver`, `ac0pObserver_boundary_le` — the `AC⁰[p]` observer; boundary `≤ #monomials`.
* `ac0p_lowBoundary_not_faithful` — **the RS obstruction, rederived**: an `AC⁰[p]` observer with monomial
  capacity `< |G|` cannot express every behavior on `G` (proved via `dim_bound_general`).  Since the `MOD_q`
  indicators *are* faithful (`sqfSpan_eq_top`), `MOD_q ∉ AC⁰[p]`.

**Significance.**  The same boundary/non-mergeability invariant that bounds Tseitin proof-space now drives the
AC⁰[p] degree lower bound — the method is validated on a rung where the truth is known.  It does not reprove
the full circuit-level capstone (`Layer4.mod_q_indicators_false`, proved separately — the approximate-agreement
and band-margin bookkeeping live there); it isolates and recasts the *dimension obstruction* that is the
lower bound's engine.  AC⁰[p] is restricted; the general rung (`P` vs `NP`) stays open.

---

## 10. Calibration 2: rederiving the Nečiporuk formula `n²/log n` lower bound

A second circuit/formula calibration (`ComputationalDepthObserverNeciporukCalibration.lean`).  Nečiporuk's
method *is* the observer invariant applied per block of a variable partition:

| observer notion | Nečiporuk notion |
|---|---|
| behaviors on a block | residual subfunctions `blockResiduals S F` |
| non-mergeable / fooling set | outside-settings whose restrictions differ (`card_blockResiduals_ge_of_pairwise`) |
| boundary on block `S` | `log₂ |blockResiduals S F|` (`formulaBlockBoundary`) |
| total observer boundary | `∑` over the partition (`formulaTotalBoundary`) |
| low-boundary observer | a small `B₂` formula: total boundary `≤ 4·litCount + #blocks` |

* `separated_forces_blockBoundary` — the per-block fooling principle: pairwise-separated outside-settings
  force `formulaBlockBoundary ≥ log₂ |family|`.  This is *exactly* `ContinuationObserver`'s
  `faithful_separated_forces_boundary` / `many_nonmergeable_sectors_force_boundary`, per block.
* `formulaTotalBoundary_le_size` — total boundary `≤ 4·litCount + #blocks`: a small formula is a
  low-total-boundary observer (the Nečiporuk summation `neciporuk_formula_lower_bound_opt`, recast).
* `hardF_blockBoundary_ge`, `hardF_observer_size_lower`, `hardF_observer_rate`, `hardF_observer_superlinear` —
  the hard multiplexer forces block boundary `≥ 2^b−1`, hence total boundary `≥ m·(2^b−1)`, hence size
  `≥ N²/(64b) = N²/log N` — the optimal Nečiporuk regime, rederived through the invariant.

**Two calibrations now confirm the crossing into circuit/formula complexity** (AC⁰[p] degree §9, Nečiporuk
formula size §10), each reusing the repo's proved bound and recasting its engine as the boundary invariant.
Honest ceiling: B₂ formulas, `n²/log n` — restricted, not super-polynomial, not `P` vs `NP`.  The general
machine-decomposition rung (the `min`-over-all-decompositions quantifier) remains the open frontier.

---

## 11. Calibration 3 (communication) and a structured class where the `min` is super-logarithmic

* `ComputationalDepthObserverRectangleCalibration.lean` — **third calibration**, in deterministic
  communication: the observer is a protocol = a partition into monochromatic rectangles, boundary =
  `log₂ (#rectangles)`.  The EQUALITY matrix's `n` diagonal entries are pairwise non-mergeable (no
  `1`-rectangle covers two — `diagonal_nonmergeable`), so `equality_rectangle_boundary_ge` gives boundary
  `≥ log₂ n` — the deterministic communication lower bound, rederived through the invariant.  **Three
  independent models now confirm the crossing** (degree, formula size, communication).
* `ComputationalDepthObserverBlockDecompositionMin.lean` — **the open inequality, proved in a structured
  class.**  For the multiplexer `hardF`, the `m` address-block continuation decompositions form a structured
  class; `hardF_minBlockBoundary_ge` shows **every** one forces boundary `≥ 2^b−1`, so the *minimum* over the
  class is `≥ 2^b−1` (no decomposition in the class is cheap — contrast the single-cut EQUALITY collapse).
  `minBlockBoundary_superlog` shows `2^b−1` is genuinely **super-logarithmic**: for every constant `c`, some
  family member has `minBlockBoundary > c·log₂(input size)`.

So the `min`-over-decompositions quantifier — which *collapses* for EQUALITY over arbitrary cuts — is forced
**super-logarithmic** for `hardF` over the address-block class.  This is the second regime (after resolution
proof-space §8) where the hard quantifier is genuinely proved, now with a super-logarithmic bound.

**Honest scope.**  The address-block class is structured and restricted — the `m` natural blocks of the
`hardF` layout, not *every* admissible decomposition; a general decider could cut across blocks (the freedom
`equality_decomposition_gap` exploits).  So this is the `min` over a *chosen* structured class, super-log; the
`min` over *all* decompositions for a hard family stays open (`= CookLevinFrontierHyp`).  Three calibrations
(degree, formula, communication) plus two structured `min` regimes (proof-space, address-block) — the method
is validated broadly and the open frontier is pinned to the all-decompositions quantifier.
