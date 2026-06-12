# Capstone: from observer-time debt to decision-holonomy

A single-page map of the dynamical God-Move arc — what is **proved**, what is **named (open)**, and the one
honest conclusion: the programme is a fully-formalized **space / proof-complexity lower bound**, and the gap to
`P ≠ NP` is named exactly as **decision-holonomy**, which is *equivalent in strength to the separation itself*.

All files below are `sorry`-free with axioms `[propext, Classical.choice, Quot.sound]` (a few pure-`Nat`
lemmas use only `[propext, Quot.sound]`).  Branch `razborov-recoverRho-wip`.

---

## 0. The one-paragraph story

An observer deciding SAT carries **distinguishability debt**: must-separate continuation pairs it has merged.
A correct observer must clear its debt, and clearing costs **boundary action** `∑_τ 2^{B_τ}`.  We proved this
accounting in full and closed every escape route *in the bounded-boundary regime*.  But the mechanism
**provably caps at boundary `B < r ≈ n`** (the brute-force escape is real), and a poly-*time* decider may use
poly *space* (`B ≥ n`) above the cap.  Worse, the debt measures *distinguishability* (proof complexity), which
a decision algorithm can bypass (Gaussian elimination decides Tseitin without servicing its debt).  So the
missing theorem is **decision-holonomy**: an invariant lower-bounding decision *time* for an NP-complete family.
We prove the reduction (decision-holonomy ⇒ `P ≠ NP`) and the gap (existing debt cannot supply it), which
together show decision-holonomy **is** the separation.

---

## 1. The debt accounting — PROVED

| theorem | file | content |
|---|---|---|
| `merge_pay`, `debt_conservation_varying` | `…BoundaryDebt`, `…ObserverTimeDebt` | conservation: `S_obs ≥` initial debt, even with time-varying boundary |
| `correct_needs_action`, `bounded_action_fails` | `…ObserverTimeDebt` | correct ⇒ action ≥ debt; bounded action ⇒ errs |
| `foolingSet_forces_debt` | `…FoolingDebt` | a size-`K` fooling set at boundary `B` forces debt `≥ K − 2^B` |
| `no_low_action_of_high_debt` | `…SATActionConjecture` | reduction: conjecture ⇐ `hdebt`; **`hdebt` = `P ≠ NP`, named** |

## 2. Every escape closed — in the bounded-boundary regime — PROVED

| escape | closed by | file |
|---|---|---|
| hide boundary over time | conservation | `…ObserverTimeDebt` |
| bounded boundary throughout | `bounded_boundary_tradeoff` (`|P| ≤ (T+1)·2^B`) | `…BoundedBoundaryDebt` |
| distribute as spikes (bounded total action) | `average_boundary_tradeoff` (`|P| ≤ 2^{B₀}+∑2^{B_τ}`) | `…AverageBoundaryDebt` |
| instant spike (locality `r`) | `burst_boundary_time_lower_bound` (`|P| ≤ (T+1)·2^{B₀+rT}`) | `…BurstBoundaryDebt` |
| change decomposition adaptively | `adaptive_total_action` (decomposition-agnostic) | `…AdaptiveTrajectory` |
| flatten via switch cost | `adaptive_boundary_tradeoff` (`|P| ≤ 2^{B₀}+∑2^{B_τ}+∑SwitchCost_τ`) | `…AdaptiveTrajectoryDebt` |
| explicit `2^n` witness geometry | `hypercube_lowBoundary_requires_superpoly_time` | `…ExpanderFoolingInstance` |
| switch-cost lower bound | `hypercube_lowBoundary_switchCost_superpoly` (`∑SwitchCost ≥ 2^n−(T+1)2^b`) | `…SwitchCostLowerBound` |

## 3. The decomposition ladder (residual non-collapse) — PROVED, all reduce to "effective boundary `< r` ⇒ debt"

| class | theorem | file |
|---|---|---|
| read-set (vertex-parity) | `expander_residual_forces_debt` | `…ExpanderResidualSurjective` |
| `F₂`-linear / affine | `expander_linear_decomposition_noncollapse` (`finrank_map_ker_ge`) | `…AdaptiveResidualNonCollapse` |
| bounded-locality / junta / branching-program | `expander_bounded_locality_noncollapse` (`debtCount_mono`) | `…BoundedLocalityNonCollapse` |
| holonomy / curvature (loop twist) | `parity_loop_holonomy`, `holonomy_forces_debt_card` | `…BoundaryHolonomy` |
| many-loop amplification (subspace flatten) | `expander_manyloop_holonomy` | `…ExpanderHolonomyAmplification` |
| bottleneck (cheap trajectory ⇒ cheap step) | `adaptive_bottleneck_exists`, `cheap_trajectory_has_residual_debt_bottleneck` | `…AdaptiveBottleneck` |

Discharged from the **expansion already in the width kernel** (`combination_support_card_ge_of_expansion`,
`exists_combination_ne_zero_of_expansion`).  Each is the *same* fact — a decomposition of effective boundary
`< r` forces debt — computed by a different structural lens (rank, support, periodicity, curvature).

## 4. The ceiling — PROVED as a theorem

| theorem | file | content |
|---|---|---|
| `hypercube_brute_force_escape` | `…DebtFrameworkBarrier` | a full-boundary (`B = n`) view resolves the `2^n` geometry with **zero debt** |
| `tradeoff_vacuous_of_high_initial_boundary` | `…DebtFrameworkBarrier` | `|P| ≤ 2^{B₀}` ⇒ the bound is content-free |

**The fooling-debt mechanism is empty for `B ≥ r ≈ n`.**  Not a gap in the formalization — a proved property.

## 5. The real gap: time → boundary, and the Williams route — PROVED (reduction) + NAMED (deep inputs)

| theorem | file | role |
|---|---|---|
| `time_space_law`, `time_space_tradeoff_curve` | `…TimeSpaceWilliamsBridge` | poly time ⇒ space `Ω(n)` (restricted TS lower bound) |
| `boundary_le_of_spaceBound`, `action_le_of_spaceBound`, `subcritical_of_lowspace` | `…TimeBoundaryPrinciple` | **positive**: a *space* bound ⇒ subcritical action ⇒ debt bites |
| `action_unbounded_by_time`, `hard_instance_has_correct_high_boundary_decider` | `…TimeBoundaryPrinciple` | **obstruction**: poly *time* alone gives no boundary bound — "P-time ⇒ cheap observer" is **false** |
| `dp_speedup`, `williams_route`, `noncollapse_via_williams` | `…TimeSpaceWilliamsBridge`, `…ObserverAlgorithmicSchema` | Williams route past the cap: cheap ⇒ fast SAT ⇒ separation (diagonalisation **named**) |
| `margin_le_of_correct`, `expander_margin_eq` | `…SpeedupMargin` | the decomposition's speedup margin is exactly `n − r = Ω(n)` (abundant) |

**Finding (proved by `…SpeedupMargin` + Gaussian elimination):** the margin is super-abundant, but only because
the proof-hard instance (Tseitin = `F₂` linear system) is **decision-easy**.  The fooling set measures
*distinguishability* (proof complexity), **not decision hardness**.

## 6. Decision-holonomy — the precise missing target — reduction & gap PROVED, target NAMED

| theorem | file | content |
|---|---|---|
| `decisionHolonomy_implies_not_poly` | `…DecisionHolonomy` | **reduction**: `decisionTime ≥` super-poly threshold ⇒ family `∉ P` ⇒ (NP-complete) `P ≠ NP` |
| `distinguishability_debt_not_time_lower_bound` | `…DecisionHolonomy` | **gap**: for any debt `D`, a `T = 1` (poly-time) trajectory has action `≥ D` — action ⇏ decision time |

> **`DecisionHolonomyHyp`** (NAMED, not proved): an invariant `ι` with `decisionTime ≥ ι`, `ι` super-poly, for
> an NP-complete SAT family.

By the reduction, `DecisionHolonomyHyp` for an NP-complete family is **equivalent in strength to `P ≠ NP`** —
the invariant *is* the separation, not a step before it.  The gap theorem proves *why* every invariant in §1–4
is insufficient: they bound **action** (capacity × time), which a high-boundary poly-time decider drives up for
free.

---

## 7. The honest conclusion

* **What is proved:** a complete, `sorry`-free dynamical boundary-action theory — conservation, mechanism,
  every bounded-boundary escape closed, the full decomposition ladder (read-set / linear / locality / curvature
  / amplification) discharged from real expansion, the ceiling proved, a restricted time–space lower bound
  (poly time ⇒ `Ω(n)` space), and the Williams plumbing.  As a lower bound on **space / proof complexity** for
  expander Tseitin, this is genuine and unconditional in its regime.

* **What is named, not faked:** `hdebt` / `AdaptiveResidualNonCollapse` / `DecisionHolonomyHyp` — three
  equivalent forms of the *same* open statement.  Each is the min-over-decompositions quantifier =
  `CookLevinFrontierHyp` = `P ≠ NP`.

* **Where the wall is, exactly:** the programme bounds **distinguishability / action / space**; `P ≠ NP` needs
  **decision time**.  The bridge between them — decision-holonomy — must either use NP-complete structure for a
  SAT time–space tradeoff (option 1) or take the Williams route (option 2: named diagonalisation + a
  decision-hard family, which the proof-hard-but-decision-easy Tseitin family is not).

* **Not one lemma away.** `distinguishability_debt_not_time_lower_bound` and
  `hard_instance_has_correct_high_boundary_decider` are theorems precisely so the arc is not mistaken for a
  near-proof of `P ≠ NP`.  Closing it requires genuinely new mathematics — a decision-time invariant for an
  NP-complete family — which this development locates exactly but does not provide.
