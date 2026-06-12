# Paper architecture: Observer‑Boundary Debt and the Decision‑Holonomy Frontier of P vs NP

A revised, defensible architecture for the whole observer‑boundary / dynamical‑debt programme.  It states
exactly **what is proved**, **what is blocked** (proved barriers), and **what the true frontier is** — and
positions the contribution honestly: a fully‑formalized restricted lower‑bound theory plus a precise
**reduction of `P ≠ NP` to one named statement (decision‑holonomy)**, with barriers proving why the framework
caps where it does.  **It is not a proof of `P ≠ NP`.**

All cited results are Lean 4 / Mathlib, `sorry`‑free, axioms `[propext, Classical.choice, Quot.sound]` (a few
pure‑`Nat`/`decide` lemmas use a subset).  Branch `razborov-recoverRho-wip`.

---

## Proposed title & abstract

**Title.** *Observer‑Boundary Debt: a formalized dynamical lower‑bound theory, and the decision‑holonomy
frontier of P vs NP.*

**Abstract.** We formalize an observer‑boundary invariant and a *dynamical* distinguishability‑debt theory: a
decider carries debt (merged must‑separate continuations), correctness requires clearing it, and clearing
costs time‑integrated boundary action.  We prove (i) the conservation accounting; (ii) genuine *restricted*
lower bounds — expander‑Tseitin proof‑space, boundary–time tradeoffs, and a full decomposition ladder
(read‑set, `F₂`‑linear, bounded‑locality, holonomy/curvature) discharged from graph expansion; (iii)
calibrations re‑deriving Razborov–Smolensky (AC⁰[p]), Nečiporuk, and communication bounds through the
invariant.  We then prove a battery of **barriers** delimiting the method: the mechanism is empty above
boundary `≈ n` (a realized brute‑force escape), poly *time* does not bound boundary, and the hard instances
are *proof*‑hard but *decision*‑easy (Gaussian elimination).  Finally we reduce `P ≠ NP` to a single named
statement, **decision‑holonomy**, prove it equivalent in strength to the separation, and prove the gap theorem
showing why the debt machinery (an *action/space* bound) cannot reach it.  The frontier is thus located
exactly, with two honest research forks identified.

---

## Part I — The invariant and the dynamical debt theory (PROVED)

* **§2 Observer‑boundary invariant.** `boundaryEntropy`; the fooling‑set principle (`K` non‑mergeable sectors ⇒
  boundary `≥ log₂ K`).  Files: `…ObserverBoundary/LowerBound`, `…BranchingObserver`,
  `…ContinuationObserver` (`Faithful` + `Separated` ⇒ `Nonmergeable`).
* **§3 Dynamical debt accounting.** `debtCount`; conservation `debt_conservation_varying`, `merge_pay`,
  `correct_needs_action`; mechanism `foolingSet_forces_debt` (`debt ≥ K − 2^B`).  Files: `…BoundaryDebt`,
  `…ObserverTimeDebt`, `…FoolingDebt`.  *This is the core engine.*

## Part II — Restricted lower bounds (PROVED)

* **§4.1 Proof‑space.** `tseitin_totalSpace_lower_bound` / `tseitin_complete_min_space`: expander‑Tseitin
  blackboard refutations have total space `≥ c·t`, reusing the width kernel
  (`combination_support_card_ge_of_expansion`).  No Atserias–Dalmau, no locking lemma.
* **§4.2 Boundary–time tradeoffs.** `bounded_boundary_tradeoff` (`|P| ≤ (T+1)·2^B`), `average_boundary_tradeoff`
  (spikes allowed), `burst_boundary_time_lower_bound` (locality `r`), with explicit `2^n` witness
  (`hypercube_lowBoundary_requires_superpoly_time`) and a switch‑cost lower bound.  Files: `…BoundedBoundaryDebt`,
  `…AverageBoundaryDebt`, `…BurstBoundaryDebt`, `…ExpanderFoolingInstance`, `…SwitchCostLowerBound`.
* **§4.3 The decomposition ladder (residual non‑collapse).** Each class proved to force `2^{Ω(n)} − 2^B` debt
  from expansion: read‑set (`expander_residual_forces_debt`), `F₂`‑linear (`expander_linear_decomposition_
  noncollapse`, via `finrank_map_ker_ge`), bounded‑locality/junta (`expander_bounded_locality_noncollapse`, via
  `debtCount_mono`), holonomy/curvature (`parity_loop_holonomy`) and many‑loop amplification
  (`expander_manyloop_holonomy`).  Unifying fact: each is *effective boundary `< r` ⇒ debt*.  Plus the
  bottleneck (`adaptive_bottleneck_exists`).
* **§4.4 Calibrations (re‑derive known bounds through the invariant).** AC⁰[p] = Razborov–Smolensky dimension
  (`mod_q_indicators_false`); Nečiporuk `n²/log n`; deterministic communication rectangles.  Files:
  `…ObserverAC0pCalibration`, `…NeciporukCalibration`, `…RectangleCalibration`, unified by
  `observer_resource_lower_bound`.

## Part III — Barriers (PROVED negative results — the paper's honesty backbone)

* **§5.1 The `B < r` ceiling.** `hypercube_brute_force_escape`: a full‑boundary view resolves the `2^n` geometry
  with **zero debt**.  `tradeoff_vacuous_of_high_initial_boundary`.  The fooling‑debt mechanism is *empty* for
  boundary `≥ r ≈ n`.  File: `…DebtFrameworkBarrier`.
* **§5.2 Decomposition gap.** `equality_decomposition_gap`: EQUALITY needs boundary `n` at one cut but `1`
  streaming — a single fixed cut is provably insufficient; the `min` over decompositions can collapse.
* **§5.3 ACC⁰ joint‑construction block.** `JointModularBarrier`; exact enriched‑modular fails
  (`mod_q_indicators_false` *is* the barrier) — approximation mandatory.
* **§5.4 Time → boundary obstruction.** `action_unbounded_by_time` + `hard_instance_has_correct_high_boundary_
  decider`: poly *time* yields **no** boundary/action bound; "P‑time ⇒ cheap observer" is *false*, not merely
  open.  Positive companion: `subcritical_of_lowspace` (the bridge holds *given a space bound*).  File:
  `…TimeBoundaryPrinciple`.
* **§5.5 Proof‑hard ≠ decision‑hard.** `tseitin_unsat_of_odd_charge`: expander‑Tseitin — proof‑hard with the
  `2^{Ω(n)}` fooling set — is **decision‑easy**, its UNSAT side decided by a single parity bit (`∑ charge`).
  File: `…TseitinDecisionEasy`.
* **§5.6 The candidate‑gadget filter battery.** A nonlinear gadget is filtered by: non‑affine (step 1, escapes),
  shared‑variable richness (step 3, AND transitivity restricts), AC⁰[p]/low‑degree (step 4, degree‑2
  linearizes), ACC⁰/mixed‑moduli (step 5, modulus‑agnostic).  A MOD₃ candidate passes 1 & 3 but is `F₃`‑additive;
  **every explicit `AND`/`XOR`/`MOD_q` gadget lies in ACC⁰**, so the battery, completed, is an *ACC⁰‑membership
  detector*.  Files: `…NonlinearCSPPilot/Richness/ANDOnly/ACCStress/ModularStress`, `…ModularCandidate`.

## Part IV — The reduction: `P ≠ NP` ≡ decision‑holonomy (PROVED reduction; statement NAMED/open)

* **§6.1 Equivalent forms of the open core.** `hdebt` (every correct SAT trajectory has super‑log debt;
  `…SATActionConjecture`), `AdaptiveResidualNonCollapse` (every cheap adaptive decomposition keeps `2^{Ω(n)}`
  residual outcomes; `…AdaptiveResidualNonCollapse`), `DecisionHolonomyHyp` (decision time `≥` super‑poly;
  `…DecisionHolonomy`), and the **dimension‑gap** form `DimensionGapHard` (`d_res(SAT) − d_obs ≥ Ω(n)` for every
  poly observer; `…ObserverDimensionGap`).  All `= CookLevinFrontierHyp = P ≠ NP`.  The dimension‑gap file also
  proves the geometric core `dimension_gap_forces_debt` / `positive_gap_forces_debt`: a low‑`d_obs` observer of
  a high‑`d_res` residual carries debt `≥ 2^{d_res} − 2^{d_obs}` (the dimensional mismatch *is* the debt) — the
  provable half; the `min`‑over‑observers target is the open half.
* **§6.2 The reduction & the gap.** `decisionHolonomy_implies_not_poly` (decision‑holonomy ⇒ `∉ P`);
  `distinguishability_debt_not_time_lower_bound` (an *action* bound gives *no* decision‑time bound — the gap).
* **§6.1′ Observer‑invariance of the debt** (`…DebtGaugeInvariance`).  The N‑frame‑Lagrangian route needs the
  action/debt to be gauge‑invariant.  `debtCount_relabel_invariant` (a *lossless* frame change — injective
  relabel `σ` — preserves debt exactly) + `debtCount_le_of_frameChange` (with `debtCount_mono`: any coarser
  frame has `≥` debt) prove **no gauge transformation lowers the debt** — only *refining* (spending boundary)
  can.  This meets HAL's requirements (1) concrete/checkable and (2) representation‑invariant.  It does **not**
  meet (3): refining is not a gauge change but a genuine resource increase, and a high‑boundary observer can
  zero the debt (`hypercube_brute_force_escape`) at *time*‑cheap cost (`action_unbounded_by_time`).  So the
  gauge‑invariant debt is still a *space* measure; invariance alone doesn't bound *time* — the wall is
  unchanged.
* **§6.2′ The full proof plan, assembled and diagnosed** (`…DimensionGapSeparation`).  `dimension_gap_separation`
  assembles Steps 3–6 as a *proved conditional*: an all‑observer action lower bound `hgap` (Steps 3+4) + a
  time→action bridge `hbridge` (Step 5) + `poly < super‑poly` ⇒ no poly‑time correct SAT observer (the
  separation).  **Diagnosis (proved):** `step5_naive_bridge_false` shows Step 5's naive form ("poly‑time ⇒ low
  action") is *false*, not just open — a poly‑time observer may use high boundary, making action `∑ 2^{B_τ}`
  exponential (`action_unbounded_by_time`).  The repair ("cannot service *decision‑relevant* gap debt") is
  decision‑holonomy = `P ≠ NP`.  So the plan is a valid implication with Steps 1–4 real and Step 5 provably the
  wall (naive form false, repaired form = the separation).
* **§6.3 The Williams route.** `time_space_law` / `time_space_tradeoff_curve` (poly time ⇒ `Ω(n)` space — a
  restricted TS bound); `dp_speedup`, `williams_route`, `noncollapse_via_williams`; `margin_le_of_correct`
  (deliverable speedup margin `= n − r`).  Deep inputs **named**: the Williams diagonalisation and a
  decision‑hard family.  Files: `…TimeSpaceWilliamsBridge`, `…ObserverAlgorithmicSchema`, `…SpeedupMargin`.

* **§6.3′ The raveling wedge — the surviving non‑circular program** (`…RavelWedge`).  Replaces the false global
  Step 5 ("poly‑time ⇒ low action", `step5_naive_bridge_false`) with two *separately* provable premises:
  `ravel_wedge` composes `raveling` (low‑action observer ⇒ factors through a constrained separator class `K`)
  and `noSeparator` (`K` has no SAT separator) into "no low‑action observer decides SAT."  This is the structure
  of *every* known lower bound (fix restricted `K`, show the hard function ∉ `K`), and the corpus already
  realizes `noSeparator` for concrete `K`: the calibrations (AC⁰[p]/Nečiporuk/communication) and the ladder
  (linear/read‑set/bounded‑locality).  **Catch:** to reach `SAT ∉ P`, `K` must capture all of `P`, and then
  `noSeparator` for that `K` *is* `P ≠ NP`.  So the wedge relocates the difficulty into the size of `K` —
  provable for every `K` we can beat, exactly the separation for any `K` large enough.  Non‑circular
  architecture; the open content is one inequality (`noSeparator` for `P`‑capturing `K`).
* **§6.3″ The ravelable class, instantiated at its ceiling** (`…RavelableClass`).  `K = {effective dimension
  `d_obs < r`}`.  `boundedBoundary_no_separator` proves `noSeparator` for it (a `B < r` observer of a
  dimension‑`r` residual has positive debt); `expander_no_boundedBoundary_separator` discharges it for the
  expander residual (`r = |ι| = Ω(n)`) — it is *non‑ravelable*.  The raveling half is the bottleneck
  (`adaptive_bottleneck_exists`).  **Structural ceiling:** `d_obs < r` is the *maximal* `K` the debt mechanism
  beats — every beatable `K` (linear/read‑set/locality/holonomy) is a sub‑class; at `d_obs ≥ r` a zero‑debt
  separator exists (`hypercube_brute_force_escape`).  Extending past it needs the Williams cash‑out (§6.3),
  guarded by natural proofs / relativization / algebrization.

## Part V — The frontier (the two honest research forks)

The least‑action path (N‑Frame Lagrangian) is built out; the residual is one of:

1. **SAT time–space tradeoff.** Force a poly‑time SAT decider into sub‑`n` boundary using NP‑complete
   structure — strengthening §5.4's restricted TS bound past the `B < r` cap.  Cannot follow from time alone.
   *Positioning (`…ObserverTISP`):* `ObserverTISP P F T B` (bounded‑boundary observer decides within time `T`,
   boundary `B`); `not_observerTISP_of_large_fooling` (`(T+1)·2^B < |P| ⇒ ∉ ObserverTISP`) and
   `hypercube_not_observerTISP` give the bounded‑boundary analogue of `SAT ∉ TISP(…)` — super‑poly‑time‑strong
   for `o(n)` boundary, *but* in the observer model on a decision‑easy instance.  The classical line (Lipton–
   Viglas → Fortnow–Van Melkebeek → Williams) proves `SAT ∉ TISP(n^{2cos(π/7)−ε}, n^{o(1)})` for *general*
   machines, *barriered* at that exponent (Buss–Williams).  The two are non‑comparable and both far from
   `P ≠ NP` (ours super‑poly‑but‑restricted; theirs `n^{1.8}`‑but‑general‑and‑barriered).
2. **Williams / ACC⁰ algorithmic bridge.** A fast SAT algorithm with the right margin ⇒ separation, via the
   named diagonalisation — needs a *decision‑hard* family (the proof‑hard ones are decision‑easy, §5.5).

Either equals **decision‑holonomy** = `P ≠ NP`; the candidate‑gadget game (§5.6) converges on the open ACC⁰
frontier.

* **§5.7 Reduction‑preservation, made precise** (`…ReductionPreservesFooling`).  The "NP‑complete reductions
  preserve holonomy debt" route splits cleanly: `reduction_preserves_fooling` / `reduction_transfers_debt` prove
  a *decomposition‑respecting* reduction (hypothesis `hred`) carries a fooling set to a fooling set, so
  distinguishability‑debt transfers up (`target debt ≥ |P| − 2^B`).  **Two named gaps:** (1) `hred` is
  non‑trivial — general reductions may scramble the decomposition; (2) this transfers *distinguishability/proof*
  debt, which by §5.5 coexists with decision‑easiness (Tseitin).  Decision‑debt transfer = decision‑holonomy =
  `P ≠ NP`.  A genuinely decision‑hard base (3SAT/Label‑Cover) is a better *candidate* (no Gaussian shortcut),
  but its hardness is `P ≠ NP`‑conditional, so the route *relocates* the open core, it does not close it.

---

## Honest status (one paragraph for the paper)

The contribution is a **complete, formalized, dynamical observer‑boundary lower‑bound theory**: a conserved
debt accounting, genuine restricted lower bounds discharged from expansion, three classical bounds re‑derived
through the invariant, and a battery of proved barriers that delimit the method precisely.  Its terminus is a
**sharp reduction**: `P ≠ NP` is equivalent to *decision‑holonomy*, and the gap theorem shows the machinery
bounds *action/space*, not *decision time*.  The work proves a real space/proof‑complexity lower bound, locates
the P‑vs‑NP frontier to the bit, and — by its own barriers — proves it is **not** a near‑proof of the
separation.

## Appendix — file index

~30 `…ComputationalDepth*.lean` files (PathB), plus scope notes: `SCOPE_OBSERVER_BOUNDARY_ENTROPY.md`,
`SCOPE_OBSERVER_TIME_DEBT.md`, `SCOPE_OBSERVER_PROGRAMME_CAPSTONE.md`, `SCOPE_NFRAME_OBSERVER_LAGRANGIAN.md`,
and the integrated map `CAPSTONE_OBSERVER_DEBT_TO_DECISION_HOLONOMY.md`.
