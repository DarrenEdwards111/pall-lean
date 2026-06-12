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
* `ComputationalDepthObserverAlgorithmicExpanderSchema.lean` — `expander_observer_williams_schema`: wires
  engine 2 (expander amplification, hypothesis) → engine 1 (DP, proved) → engine 3 (Williams, hypothesis).
* `…LowBoundaryFromStreaming`, `…LowBoundaryFromCrossings` — engine 1 **discharged** by *proved* low-boundary
  decompositions: the streaming EQUALITY decider (`B=1`) and the Route-F oblivious-wide TM (`B=O(log n)`).
* `ComputationalDepthTwoSidedBoundaryWitness.lean` — `equality_two_sided`: one function fires *both* engines
  (high single-cut boundary **and** low streaming boundary) — the engines are complementary, in opposite
  boundary directions.

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
in two structured classes, and it carries a working conditional algorithmic engine.  It also **locates the
open problem with full precision** — one quantifier — and proves, rather than hand-waves, the barriers that
stop the easy routes (fixed-cut insufficiency, exact-enrichment failure, the ACC⁰ joint-construction block).
What it does **not** do is move that open quantifier: `P ≠ NP` and `NP ⊄ ACC⁰` remain open, and every further
step toward them is genuine new mathematics (a high-boundary-under-all-decompositions theorem, or Williams
diagonalization), not Lean assembly.  The value delivered is a precise, honest, machine-checked map of the
terrain right up to that line.
