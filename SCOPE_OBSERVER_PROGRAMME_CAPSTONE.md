# The observer-boundary programme — capstone map

A single index over the whole observer-boundary arc: what is **proved**, what is a **proved barrier**
(honest negative), and the **one open quantifier** everything reduces to.  Every Lean result below is
`sorry`-free with clean axioms `[propext, Classical.choice, Quot.sound]` (a few `native_decide` leaves are
flagged where used).  Companion docs: `SCOPE_OBSERVER_BOUNDARY_ENTROPY.md` (§1–12, the detailed walk),
`SCOPE_ACC0_OBSERVER_FRONTIER.md`, `SCOPE_OBSERVER_ALGORITHMIC_EXPANDER.md`, `SCOPE_ROUTEF_SUMMARY.md`.

---

## Thesis

A single invariant — **observer boundary** (`log` of the number of distinguishable interface/boundary states
a deterministic observer must carry across a decomposition) — unifies proof-complexity space, circuit degree,
formula subfunctions, and communication, and proves genuine lower bounds in each *restricted* regime.  The
separation `P ≠ NP` is, in this language, exactly **one quantifier**: that an NP-complete family forces high
boundary under *every* admissible decomposition.  The programme proves the invariant's laws, rederives three
known circuit/communication lower bounds through it, proves the `min`-over-decompositions quantifier in two
structured classes, builds the algorithmic (Williams-direction) second engine, and proves precise barriers
where the easy routes stop — leaving the open quantifier exactly located and untouched.

---

## I. The invariant and its laws (proved)

* `ComputationalDepthObserverBoundary.lean` — `boundaryEntropy A C := C·(log₂A+1)`;
  `rank_le_two_pow_boundaryEntropy` (`log₂ rank ≤ B`), `lowBoundary_poly_rank` (`B=O(log n) ⇒ poly rank`).
* `ComputationalDepthObserverLowerBound.lean` — the reverse principle `observer_boundary_lower_bound` /
  `foolingSet_forces_boundary` (`K` distinguishable continuations ⇒ `B ≥ log₂K`); `equality_forces_boundary`
  (it bites).  Two-sided: `B` tracks `log₂` of the fixed-cut rank both ways.

## II. The proved rungs (lower bounds via the invariant)

| rung | file | headline theorem |
|---|---|---|
| **Tseitin proof-space** (Option C) | `ComputationalDepthResolutionSpace`, `…ExpanderTseitinSpace`, `…TseitinSpaceObserver` | `tseitin_totalSpace_lower_bound`: every blackboard refutation of expander-Tseitin has total space `≥ c·t`; `tseitin_proofSpace_observer_unbounded` |
| **branching abstraction** | `ComputationalDepthBranchingObserver` | `many_nonmergeable_sectors_force_boundary` (`K` non-mergeable ⇒ `B ≥ log₂K`) |
| **continuation bridge** (the heart) | `ComputationalDepthContinuationObserver` | `faithful_separated_forces_boundary`: *correctness over continuations* derives non-mergeability; `equality_continuation_forces_boundary` (single cut `≥ n`) |
| **hypercube witness** | `ComputationalDepthHypercubeWitnessObserver` | both regimes on one `W`: faithful forced `≥ n`; lossy projection merges |
| **`min` realized: proof-space** | `ComputationalDepthMinBoundaryRealized` | `tseitin_minProofSpaceBoundary_ge`: `min` over *all refutations* `≥ c·t` |
| **`min` realized: address-block** | `…ObserverBlockDecompositionMin`, `ComputationalDepthForcingFamilyMin` | `hardF_minBlockBoundary_ge`, `minBlockBoundary_superlog`; `hardF_subfamily_min_ge` (every subfamily) |

## III. Three calibrations — the invariant rederives known circuit/communication bounds

| model | file | rederived bound |
|---|---|---|
| **AC⁰[p] degree** (Razborov–Smolensky) | `ComputationalDepthObserverAC0pCalibration` | `ac0p_lowBoundary_not_faithful` — `dim_bound_general` *is* the boundary principle; `MOD_q ∉ AC⁰[p]` |
| **Nečiporuk formula** `n²/log n` | `ComputationalDepthObserverNeciporukCalibration` | `separated_forces_blockBoundary` + `formulaTotalBoundary_le_size`; `hardF_observer_rate` |
| **communication rectangles** | `ComputationalDepthObserverRectangleCalibration` | `equality_rectangle_boundary_ge` — EQUALITY diagonal fooling set ⇒ `≥ log₂ n` |

**Three independent models confirm the method crosses from proof complexity into circuit/communication
complexity.**

## IV. The unifying schema and the two structured `min` regimes

* `ComputationalDepthObserverLowerBoundSchema.lean` — `observer_resource_lower_bound`: every observer lower
  bound = (boundary lower bound from non-mergeability) + (resource↔boundary bridge).  Rederives Nečiporuk *by
  applying the schema*.  Proof-space, AC⁰[p], Nečiporuk are the three instances.
* `ComputationalDepthForcingFamilyMin.lean` — `ForcingFamily`: a decomposition class where every member is
  forced; `min` (and every subfamily's `min`) `≥` threshold.  The two `min` regimes (proof-space,
  address-block) are instances.

## V. The algorithmic second engine (Williams direction, conditional)

* `ComputationalDepthObserverAlgorithmicSchema.lean` — `dpSat_beats_bruteforce` (**proved**): a low-boundary
  decomposition ⇒ DP over `2^B` boundary states beats brute force.  Williams as explicit hypothesis.
* `ComputationalDepthObserverRestrictionDecomposition.lean` — the route-selected restriction-tree cash-out
  (**proved**): `≤ 2^(n−saving)` leaves and residual boundary `≤ saving−1` imply total work `≤ 2^(n−1) < 2^n`.
  Also proves the parity obstruction: output-only boundary stays one under every proper restriction, so the open
  contraction lemma must use a structural/fanout-aware potential rather than final-output entropy alone.
* `ComputationalDepthFanoutAwareIncidencePotential.lean` — first structural-potential stress test (**proved**):
  fixing a variable decreases live-incidence credit by exactly its live gate degree; shared-gate insertion is
  idempotent, so fanout does not duplicate charge; one wide `MOD` gate now pays one unit per fixed input.  Dense
  overlap exposes the next wall: raw credit is `#gates · #live`, exceeding the `n`-bit budget, so the surviving
  target is a separator-owned/normalized potential or an amortized high-overlap simplification lemma.
* `ComputationalDepthNormalizedSeparatorPotential.lean` — normalized ownership test (**proved and falsified as a
  complete potential**): charges each covered live variable once, hence credit `≤ #live`; monotone under restriction,
  fanout-neutral, and bounded by `n` even for complete overlap/expander incidence.  But under full coverage fixing
  `k` variables leaves credit `n−k`, so binary work is exactly `2^k·2^(n−k)=2^n`: **zero surplus**.  The next
  invariant must obtain super-unit expected simplification or avoid exploring all branches via separator
  factorization; normalization alone cannot yield fast SAT.
* `ComputationalDepthHighOverlapAmortization.lean` — high-overlap engine (**combinatorial half proved**): total
  incidence equals the sum of live variable degrees; average incidence `> d` exposes a live variable of degree `> d`;
  deleting it splits exact incidence destruction into one unit of query cost plus `degree−1` positive overlap
  surplus.  The remaining wall is semantic transfer: for `MOD`, a deleted incidence changes a residue but need not
  remove a gate or lower continuation boundary.  Required next: turn accumulated overlap surplus into actual
  gate/boundary simplification for a named class, or produce a semantically-inert high-overlap counterfamily.
* `ComputationalDepthSemanticOverlapTransferNoGo.lean` — semantic-transfer stress test (**proved**): `k` duplicate
  wide parity gates have incidence `k·#live` and positive overlap surplus, yet every gate remains nonconstant while
  one supported variable is free—so overlap surplus does not imply gate elimination.  Simultaneously all `k` gates
  compute the same residual function, hence quotient to one semantic profile.  Consequence: any surviving potential
  must measure overlap only **after semantic deduplication** of residual support/modulus/target functions; syntactic
  gate-degree surplus is unsound.
* `ComputationalDepthSemanticProfileQuotient.lean` — residual fixed-modulus semantic quotient (**proved**): gates
  are deduplicated by `(free support, shifted residue target)`; the quotient has at most `m · #distinct-supports`
  profiles, and quotient incidence is at most that quantity times `#live`.  Thus duplicate multiplicity cannot fake
  surplus, while any large post-quotient family forces many distinct residual supports.  Distinctness alone is not
  yet compression-resistant: the next target is to connect these supports to linear rank / observer-cell count and
  prove restriction-induced rank or cell collapse (or exhibit a high-rank counterfamily).
* `ComputationalDepthSemanticProfileRankTransfer.lean` — semantic quotient to parity rank bridge (**proved**): a
  residual target shift is an affine translation of the parity observer and preserves its reachable-state count.
  Consequently the residual observer has exactly `2^rank` states, and rank `≤ r` gives at most `2^r` states;
  shifted targets and profile multiplicity add no linear observer dimension.  The remaining load-bearing theorem is
  now a restriction-induced **rank/cell contraction with surplus**, or an algorithm that factors the affine state
  space without separately exploring every restriction branch.
* `ComputationalDepthRankContractionAccounting.lean` — exact rank/branch accounting (**proved**): querying `q` bits
  and independently enumerating a residual rank-`r` observer costs exactly `2^(q+r)`.  It beats an initial rank-`R`
  state space iff `q+r<R`; rank loss equal to query cost gives exact zero surplus, and smaller loss cannot help.
  Therefore the next class theorem must prove super-unit rank/cell contraction on sufficient Kraft weight, or abandon
  independent branch exploration and establish reusable cross-branch factorization.
* `ComputationalDepthParityRankRestrictionNoGo.lean` — parity rank-contraction obstruction (**proved**): deleting
  `q` input-column generators reduces their span rank by at most `q`.  Combined with exact accounting, independently
  exploring all restriction branches costs at least the original parity observer state space, so super-unit rank loss
  is impossible for restrictions that merely delete parity columns.  The parity branch of the algorithmic route must
  therefore use **cross-branch reuse/separator factorization** (or nonlinear upper-layer collapse), not independent
  rank-state enumeration.
* `ComputationalDepthCrossBranchAffineFactorization.lean` — affine branch quotient (**proved**): all residual shifts
  from `q` queried parity columns are the deduplicated subset-sum family, of cardinality at most `2^q`; every semantic
  or coset classifier likewise yields at most `2^q` residual classes.  A strict reduction is proved whenever two
  distinct reachable shifts collide under the classifier.  Hence factorization is not automatic: the new decisive
  lemma must force sufficiently many affine-class collisions (or give a sublinear batched algorithm even when the
  classes remain distinct).
* `ComputationalDepthCrossBranchCosetCollision.lean` — kept-span coset criterion (**proved**): two queried-branch
  shifts define the same residual parity class exactly when their difference lies in the span of the kept columns.
  In particular, any nonzero queried column already in the kept span makes the zero and singleton branches collide,
  giving strict reuse.  Thus the separator target becomes quantitative: find query blocks with large dependence
  modulo the kept span, so the quotient rank (not raw query count) pays for the branch family.
* `ComputationalDepthCrossBranchQuotientRank.lean` — exact quotient-rank bound (**proved**): projected queried
  columns span a quotient space of rank `d ≤ q`; every residual branch coset lies in that span, hence the full branch
  family has at most `2^d` classes rather than `2^q`.  The remaining structural dichotomy is now exact: force
  `d<q` (preferably a quantitative deficit) for some useful separator block, or confront independent projected-column
  families where the quotient rank saturates and affine collision reuse gives no saving.
* `ComputationalDepthObserverAlgorithmicExpanderSchema.lean` — `expander_observer_williams_schema`: wires
  engine 2 (expander amplification, hypothesis) → engine 1 (DP, proved) → engine 3 (Williams, hypothesis).
* `…LowBoundaryFromStreaming`, `…LowBoundaryFromCrossings` — engine 1 **discharged** by *proved* low-boundary
  decompositions: the streaming EQUALITY decider (`B=1`) and the Route-F oblivious-wide TM (`B=O(log n)`).
* `ComputationalDepthTwoSidedBoundaryWitness.lean` — `equality_two_sided`: one function fires *both* engines
  (high single-cut boundary **and** low streaming boundary) — the engines are complementary, in opposite
  boundary directions.

---

## Vb. The structured-`min` regime, fully developed (the Lagrangian's least-action quadrant)

A route-selector (`SCOPE_NFRAME_OBSERVER_LAGRANGIAN.md`) scores attacks by an *action* built from the real
N-Frame Lagrangian `S_NF` (kinetic = graph Laplacian, parity, barrier): all-decompositions SAT and ACC⁰ are
high-action (the open quantifier / the proved barrier); **structured forcing families are least-action**.  Its
three least-action moves are now all built and machine-checked.

**New forcing families** (the generic engine `every_refutation_totalSpace_ge` / `proofSpaceMin_ge_of_band` is
*generic* over `(μ, subadditivity, axiom-bound, width-link)`; Tseitin/PHP are instances):

* `ComputationalDepthTseitinCompleteForcing.lean` — `tseitin_complete_min_space`: **fully discharged** —
  `Kₙ`-Tseitin proof-space `min ≥ t` (`4t ≤ n`), **no named input** (`completeGraph_hasExpansion` is proved,
  the dense graph needs no expander construction).  The fully-closed member of the forcing-family lattice.
* PHP proof-space — reduced to **one** named input through six proved layers:
  `ComputationalDepthPHPProofSpaceForcing.lean` (instance, subadditivity proved) →
  `…PHPWidthLink.lean` (`phpWidthLink` ⇒ flip lemma: injection + measure assembly proved) →
  `…GraphPHPExpansion.lean` (three flip cores: pigeonhole, flip mechanism, free-hole-from-unique-neighbour) →
  `…MatchingMeasure.lean` (the matching-based measure: subadditivity + unsatisfiability proved) →
  `…MatchingRootBound.lean` (root bound; unconditional for complete-bipartite) →
  `…BipartiteHallMatching.lean` (`exists_placement_of_hall`: matchability via Mathlib Hall).  Residual: a
  **unique-neighbour bipartite expander** (`n < m`) — a deep lossless-expander construction, named not faked.

**Expander amplification** (`−𝐀`): `ComputationalDepthForcingFamilyAmplify.lean` — `ForcingFamily.prod`:
tensoring forcing families **amplifies the threshold additively** (`prod_threshold_le_min`); `hardF_prod_amplified`
gives `min ≥ 2·(2^b−1)` for two copies, `k·(2^b−1)` for `k`.

**Structured low-boundary → engine 1** (third route-3 move): besides streaming and Route-F crossings,
`ComputationalDepthBPLowBoundaryEngine.lean` — a bounded-width **branching program** (`LayeredBP`) gives a
`LowBoundaryInstance` of boundary `log₂ w` (`LayeredBP.dp_beats_bruteforce`); `parityBP` (width 2) fires
engine 1 for `n ≥ 4`.  Two-sided: width-2 PARITY BP is *low* boundary (engine 1) yet PARITY is *high* in AC⁰.

**Net:** the least-action quadrant is comprehensively built — a fully-closed forcing family (`Kₙ`-Tseitin), a
reduced-to-one-named-input family (PHP), subfamily robustness, tensor amplification, and three distinct
structured low-boundary sources feeding engine 1.  All `sorry`-free; every hard input named, not faked.  The
open all-decompositions quantifier (§VII) is untouched — everything *up to* it in the structured regime is
proved.

---

## VI. The barriers (proved honest negatives)

* **Fixed-cut insufficiency** — `ComputationalDepthDecompositionGap.lean`, `equality_decomposition_gap`:
  EQUALITY's single-cut boundary is `≥ n` but its streaming boundary is `1`.  A single decomposition's lower
  bound does **not** lower-bound the `min` — "the machine chooses the decomposition", proved.
* **Exact enriched-modular fails** — `ComputationalDepthEnrichedModularBoundary.lean`: the exact `∑`-over-moduli
  boundary is high for a single cross-modulus gate (`enrichedBoundary_two_moduli_obstruction`); approximation
  is mandatory.
* **ACC⁰ joint construction blocked** — `ComputationalDepthApproxEnrichedBoundary.lean` (approximate single-field
  bridge proved; `mixedCircuit_not_isAC0p_left/right`), `ComputationalDepthJointModularBarrier.lean`
  (`no_fixed_family_joint_bridge`): **the very theorem that powers the AC⁰[p] calibration
  (`mod_q_indicators_false`) is the barrier to the ACC⁰ joint construction.**  This is why ACC⁰ resists the
  polynomial method (and why Williams needed an algorithmic route).
* **The conditional ACC⁰ target** — `ComputationalDepthObserverACC0Frontier.lean`,
  `acc0_separation_of_boundary`: states *exactly* what a separation would need, with the two open ingredients
  as explicit hypotheses.

---

## VII. The one open quantifier

Everything reduces to a single statement, open and `P`-vs-`NP`-strength:

> **For an NP-complete family, the boundary is high under *every* admissible decomposition**
> (`min` over all decompositions `= ω(log n)`)  —  i.e. `CookLevinFrontierHyp`.

* The lower-bound engine proves it for *restricted* decomposition classes (proof-space, address blocks) and
  *fixed* cuts (insufficient).
* The algorithm engine needs the *opposite* (a low-boundary decomposition) and so cannot supply it; the
  Williams bridge that would convert a fast algorithm into a lower bound is the deep open input.
* The all-decompositions quantifier is precisely the gap the decomposition gap (§VI) shows cannot be closed by
  any single decomposition.

**Nothing in the programme closes it.**  `NP ⊄ AC⁰[p]` is rederived (known); `NP ⊄ ACC⁰`, `NEXP ⊄ ACC⁰`
(except via the assumed Williams hypothesis), and `P ≠ NP` are open.

---

## Honest bottom line

The observer-boundary invariant is a **legitimate, formally-anchored unifier**: it has proved laws, it
rederives three genuine circuit/communication lower bounds, it proves the `min`-over-decompositions quantifier
in structured classes, and it carries a working conditional algorithmic engine.  Guided by an N-Frame
Lagrangian route-selector, the **structured-`min` regime (the least-action quadrant) is now comprehensively
developed** (§Vb): a fully-closed forcing family (`Kₙ`-Tseitin, no named input), a reduced-to-one-named-input
family (PHP, six proved layers + a named unique-neighbour expander), tensor amplification of the threshold,
and three distinct structured low-boundary sources feeding the algorithmic engine.  The invariant also
**locates the open problem with full precision** — one quantifier — and proves, rather than hand-waves, the
barriers that stop the easy routes (fixed-cut insufficiency, exact-enrichment failure, the ACC⁰
joint-construction block).

What it does **not** do is move that open quantifier: `P ≠ NP` and `NP ⊄ ACC⁰` remain open, and every further
step toward them is genuine new mathematics (a high-boundary-under-*all*-decompositions theorem for SAT, an
explicit unique-neighbour expander for PHP, the ACC⁰ joint approximant, or Williams diagonalization), **not
Lean assembly**.  The structured-regime construction is essentially complete; the next genuine progress needs
a new idea on one of those fronts.  The value delivered is a precise, honest, machine-checked map of the
terrain right up to that line — with every hard input named, not faked.
