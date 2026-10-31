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

* **§6.4 The N‑Frame / SPDP bridge — assumption vs derivation, made explicit** (`…NFrameHypercubeConstraint`).
  Formalizes N‑Frame book1's "SPDP event horizon".  `p_ne_np_from_bridge`: `bridge` (`PObserverLowSPDP`:
  poly‑time ⇒ low SPDP rank of the decision view) `+ correct_needs_rank + sat_high` (SAT's required rank is
  super‑poly) ⇒ no poly‑time SAT decider.  `restricted_bridge_gives_separation`: with the bridge restricted to a
  structural class `K`, the conclusion restricts to `K`.  **The split this makes precise:** the *restricted*
  bridge (poly‑time `∧` in `K` ⇒ low SPDP) is provable for concrete `K` — the whole corpus is instances; the
  *global* bridge is `P ≠ NP`‑hard and false in the naïve model (poly space ⇒ high‑dimensional view), and
  book1 *asserts* it as a principle ("low SPDP rank encodes P‑reach") rather than deriving it; `sat_high` is the
  SPDP lower bound, **disproved for the diagonal `χ_φ` family** and barriered‑short‑of‑`P/poly` for the
  permanent.  So book1's `P ≠ NP` = the global bridge (an assumption equal in strength to the separation) + an
  open/false SPDP bound — faithful geometry, load‑bearing implication assumed not derived.

* **§6.4′ Restricted bridge for crossing‑sequence `K` — PROVED** (`…CrossingSequenceBridge`).  Discharges
  `restrictedBridge` (§6.4) for `K = {width‑`w` crossing‑sequence observers over `q` states}`, *non‑circularly*
  by counting.  `residual_view_card_forces_debt` (a view into finite `S` carries debt `≥ 2^r − |S|`) ⇒
  `crossingSequence_forces_debt` (view into `Fin w → Fin q` ⇒ debt `≥ 2^r − q^w`) ⇒ `crossingSequence_no_separator`
  (`q^w < 2^r` ⇒ positive debt, no separator).  A crossing‑sequence observer holds `≤ q^w` states, so it cannot
  separate a dimension‑`r` residual once `w·log₂q < r` — derived, not assumed.  **Honest scope:** this is the
  classical one‑tape/oblivious crossing‑sequence model as a debt statement; it does *not* reach all of `P` —
  `polyTime ⇒ low crossing width` is false (multi‑tape/RAM machines have unbounded crossing sequences).  So the
  crossing‑sequence restricted bridge is a theorem; the global bridge remains the wall.

* **§6.5 The strongest conditional route: observer‑Williams over a Goldreich expander CSP**
  (`…GoldreichExpanderCandidate`).  Assembles all three engines.  `GoldreichCSP`/`eval` define the family
  (`m` outputs, each the local predicate on a hyperedge); `tsaGoldreich` fixes the predicate to the verified
  `AI ≥ 2` TSA (`tsa_algebraic_immunity_ge_two`).  `goldreich_observer_williams` (no axioms): `raveling`
  (low‑action ⇒ separator in `K`) + `separatorSpeedup` (separator ⇒ fast inversion) + `goldreichHard`
  (`GoldreichHardnessHyp`: no fast inversion) ⇒ **no low‑action observer inverts the family** — a correct one
  would break the PRG.  **Honest:** `raveling`/`separatorSpeedup` are framework‑supplied; `goldreichHard` is a
  *cryptographic conjecture* (local‑PRG security), whose unconditional proof is `P ≠ NP`.  Predicate verified at
  base case (TSA, `AI ≥ 2`); higher‑arity growing‑AI is the next rung but `AI ≥ 3` is `decide`‑infeasible
  (needs structural immunity).  The cleanest conditional separation: observer geometry + Goldreich family +
  Williams cash‑out, with one conjectural input.

* **§6.6 Growing algebraic immunity — the structural lower bound `AI(Maj_n) ≥ ⌈n/2⌉`, `¬Maj` side PROVED**
  (`…MajorityAlgebraicImmunity`).  `decide` caps AI at a constant; growing AI needs a *structural* argument that
  scales with arity.  Built from its genuine core — the **`F₂` Möbius / ANF inversion**, absent from Mathlib,
  constructed here: the subset‑sum transform `anf g S = ∑_{T⊆S} g T` is its own inverse over `F₂`
  (`anf_involutive`), proved from the interval count `#{T : U⊆T⊆S} = 2^{|S|-|U|}` (even unless `U=S`,
  `card_filter_subset_between`).  From it: `low_weight_low_degree_zero` (a low‑ANF‑degree function supported only
  on high weight is `0`) ⇒ `nonzero_low_degree_hits_low_weight` (the weight‑`<t` slice is interpolating for
  degree‑`<t` `F₂` polynomials) ⇒ `negMaj_no_low_degree_annihilator` (no nonzero degree‑`<t` `g` annihilates
  `¬Maj`).  Immunity threshold `t` **grows with arity** — no `decide`.  Clean axioms, no `sorry`.  **Honest
  scope:** this is the structural `¬Maj` (low‑weight) side; the matching `Maj` (high‑weight) side follows by the
  degree‑preserving complement symmetry `Maj(x̄)=¬Maj(x)`, now **also proved** (`anf_compl_eq_superset_sum`:
  `anf(T↦g Tᶜ)U = ∑_{S⊇U} anf g S` via complement reindex + dual swap‑and‑count ⇒ `degreeLt_compl` ⇒
  `maj_high_weight_annihilator_zero`).  **`majority_algebraic_immunity_two_sided` (PROVED): the FULL two‑sided
  `AI(Maj_{2t-1}) ≥ t`** — no nonzero degree‑`<t` `g` annihilates `Maj` or `¬Maj`, threshold `t` growing with
  arity, purely structural (no `decide`), clean axioms.  The growing‑algebraic‑immunity lower bound is complete.
* **§6.6′ Optimality — the matching upper bound `AI(f) ≤ ⌈n/2⌉` for ALL `f`, PROVED** (`…MajorityAIUpperBound`).
  A dimension/pigeonhole count (not the Möbius inversion): `exists_low_degree_annihilator` (pigeonhole
  `Fintype.exists_ne_map_eq_of_card_lt` on the coefficient→evaluation map `c ↦ (T ↦ anf(cmask c)T)`, lifted by
  `cmask` + the `F₂` involution: `g := anf(cmask c₁) − anf(cmask c₂)`, `anf g = cmask c₁ − cmask c₂`) +
  `card_small_subsets_gt` (`#{S:|S|≤⌈n/2⌉} > 2^{n-1}` by complement symmetry `S↦Sᶜ` + inclusion–exclusion) ⇒
  `algebraic_immunity_le_ceil` (every `f` has a nonzero degree‑`≤⌈n/2⌉` annihilator of `f` or `¬f`).
  **`majority_AI_optimal` (PROVED): for `n=2t-1`, no degree‑`<t` annihilator (lower) AND a degree‑`≤t`
  annihilator exists (upper) ⇒ `AI(Maj_{2t-1}) = t = ⌈n/2⌉`, the OPTIMAL algebraic immunity.**  Clean axioms,
  no `sorry`.  The growing‑AI story is now complete and tight.

* **§6.7 Goldreich instantiated with the optimal Majority predicate + the exact remaining wall**
  (`…GoldreichMajorityCandidate`).  Replaces TSA (`AI=2`) with the proved‑optimal Majority
  (`AI(Maj_{2t-1})=⌈n/2⌉`).  `majPred_eq_maj` (via `maj_eq_one_iff`) rigorously ties the Bool‑input predicate to
  the proved `Maj` under the support map (no representation hand‑wave); `majGoldreich` is the instantiated family.
  `majority_defeats_low_degree_separator` (**AI ⇒ separator resistance**, the reusable tool): no nonzero
  degree‑`<t` function annihilates `Maj`/`¬Maj`, so the low‑degree‑annihilator/linearization attack provably
  fails against Majority (from `majority_AI_optimal`).  `majority_observer_williams` (no axioms): the sharpened
  **four‑step** cash‑out `low‑action ⇒ separator∈K ⇒ fast inversion ⇒ collapse ⇒ ⊥`.  `MajorityGoldreichHardness`
  bundles the exact ingredients (`raveling` provable for restricted `K`; `separatorSpeedup`,
  `fastInversionImpliesCollapse` framework/Williams‑standard) and isolates the **single open conjecture**
  `noCollapse` = `InversionHardness` (= local‑PRG security, `P ≠ NP`‑strength).  Net: the predicate is provably
  optimal and the algebraic attack provably fails — the route is reduced to exactly one named cryptographic
  statement.

* **§6.8 Restricted `InversionHardness` — proved unconditionally, by inverter class**
  (`…RestrictedInversionHardness`).  Turns the global inversion conjecture into a *theorem* for concrete classes,
  modelling a correct inverter as a separator (zero distinguishability debt against a surjective residual onto
  `Fin(2^r)`).  `no_low_degree_algebraic_inverter` (NEW, from optimal AI): for `n=2t-1` no nonzero degree‑`<t`
  function annihilates `Maj`, so the linearization/low‑degree Gröbner attack provably fails — `InversionHardness`
  for the degree‑`<t` algebraic class.  `boundedCrossing_not_correct_inverter` (from the crossing bridge): a
  width‑`w` crossing observer over `q` states is not a separator once `q^w<2^r`.
  `boundedLocality_not_correct_inverter` (from `bounded_support_forces_debt`): a `|W|`‑variable junta view is not
  a separator once `2^{|W|}<2^r`.  All unconditional, clean axioms.  **Honest scope:** exact low‑degree (an
  `AC⁰[p]`/*approximate* inverter needs the Razborov–Smolensky approximation argument — noted, not done); the
  global statement is still the wall.

* **§6.9 The `AC⁰[p]` / approximate‑inverter class — restricted `InversionHardness` via Razborov–Smolensky**
  (`…AC0pInverterHardness`).  Adds the genuinely harder *approximate* class, reusing the assembled RS chain
  (`Layer3` low‑degree `F_p` approximation `toPoly_eval_AC0p` + `Layer4` no‑approximation core
  `mod_q_indicators_false`/`mod_q_family_false` + `Layer7` family bounds `modq_not_in_nonuniform_AC0p`,
  `parity_not_in_nonuniform_AC0p`).  `IsAC0pInverter` = poly‑size constant‑depth `AC⁰[p]` family that `Computes`
  the target; `no_AC0p_inverter_modq` / `no_AC0p_inverter_parity`: the `AC⁰[p]` inverter class is provably empty
  for `MOD_q` (`q≠p`) / `PARITY` (`p` odd).  Clean axioms, no `sorry` (no `native_decide` in the chain).
  **Complementarity = the wall:** `MOD_q` resists `AC⁰[p]` but is `F_q`‑linear (algebraically trivial), while
  `Majority` resists the algebraic attack — no single proved predicate resists *all* classes at once; that
  conjunction over one family is the global `InversionHardness` (`P ≠ NP`‑strength).

* **§6.10 The unified inverter frontier — the simultaneous‑resistance wall, formal**
  (`…UnifiedInverterFrontier`).  Common carrier `F2Lang`; `ResistsLowDegree H t` (no degree‑`<t` annihilator of
  the `(2t-1)`‑slice) and `ResistsAC0p H p` (no poly‑size `AC⁰[p]` family computes `H`, via the support↔Bool
  bridge `toBoolLang`).  Witnesses: `majority_resists_lowDegree` (from `AI(Maj)=⌈n/2⌉`), `parity_resists_AC0p` /
  `modq_resists_AC0p` (from RS).  **`parity_not_resists_lowDegree` (the new complementarity theorem):** the
  `AC⁰[p]`‑resisting `parityF2` is affine (`AI≤1`) — the degree‑1 `1⊕parity` annihilates it (proved via the `F₂`
  involution `anf(T↦|T|)=δ_{|S|=1}`), so it FAILS low‑degree resistance.  Hence neither known witness satisfies
  both conjuncts; `SimultaneousAlgAC0pResistance := ∃H, ResistsLowDegree H t ∧ ResistsAC0p H p` is the named open
  wall.  Bounded‑crossing/locality are *automatic* (generic, §6.8), so the binding constraint is exactly this
  pair; extending it to all poly inverters is the global `InversionHardness` (`P ≠ NP`‑strength).  Makes "no
  single predicate resists everything" a theorem, not prose.

* **§6.11 Option A scoped — `Majority ∉ AC⁰[p]` reduced to the standard `MOD_q ≤ Majority` reduction**
  (`…MajorityAC0pScope`).  Scope finding: Majority is *not* a short corollary of the corpus — the RS
  no‑approximation core is `MOD_q`‑specific (ζ‑pairing); closing Majority needs a fresh approximate‑degree LB or
  the classical reduction `MOD_q ≤_{AC⁰} Majority` (`MOD_q ∈ TC⁰`).  Reduction route, honest: `AC0pReduction`
  (concrete `AC⁰[p]` many‑one closure, **not** a conjecture).  `majority_not_AC0p_of_reduction` (given it,
  Majority ∉ AC⁰[p], via `modq_not_in_nonuniform_AC0p`); `majority_resists_AC0p_of_reduction` (discharges the
  unified‑frontier open cell); **`majority_witnesses_simultaneous_of_reduction`** — `majorityF2` then satisfies
  BOTH binding resistances ⇒ `SimultaneousAlgAC0pResistance`.  The binding wall collapses onto a single predicate
  *modulo a known reduction* (remaining cost = build the padded‑threshold circuit, `padInputs`/`padTrue`
  supplied).  Qualitatively unlike `P ≠ NP`: this conditional is formalization labour, not a breakthrough.

* **§6.12 `MOD_q ≤ Majority` reduction COMPLETE ⇒ `Majority ∉ AC⁰[p]` UNCONDITIONAL**
  (`…ModqReducesMajority`).  Discharges the `AC0pReduction` hypothesis of §6.11 by formalizing the full classical
  reduction circuit: `thresholdCirc m k Maj := padInputs (selector m k) Maj` computes `[#ones≥k]` (Majority of a
  padded `2m+1`‑input assignment); `modqCirc = ⋁_{k≡0(q)}([#ones≥k]∧¬[#ones≥k+1])` computes `MOD_q`.  Proved:
  `modqCirc_eval` (correctness), `modqCirc_isAC0p`, `modqCirc_depth_le` (constant depth), and the polynomial size
  bound `modqCirc_subcircuits_card_le` — the last needing a **from‑scratch `IsPolyBounded` closure**
  (`ipb_const/linear/add/mul/comp_affine`).  `reductionFamily` packages it; `modq_AC0pReduction` is the reduction.
  Hence **`majority_not_in_AC0p` (unconditional `Majority ∉ AC⁰[p]`)** and **`majority_simultaneous_resistance`**:
  `majorityF2` unconditionally satisfies BOTH binding resistances (low‑degree ∧ `AC⁰[p]`) ⇒
  `SimultaneousAlgAC0pResistance` realized on a **single predicate, no remaining hypothesis**.  Clean axioms, no
  `sorry`.  The unified binding wall is now an unconditional single‑predicate theorem.

* **§6.13 Option C — the Goldreich / local‑PRG route, the constructive terminus** (`…GoldreichMajorityPRG`).
  Assembles the concrete `goldreichMaj` = Goldreich local function with the optimal‑AI Majority predicate (`n`
  inputs, `m` outputs, each `Maj_d` of an expander‑hyperedge `d`‑subset).  Proved: `goldreich_eval_local`
  (locality — each output depends only on its edge's inputs), `majPred_const_true`/`_false` (non‑degeneracy),
  `goldreichMaj_no_lowAction_inverter` (the conditional separation via observer‑Williams).  **Honest wall:**
  `GoldreichMajHard` (no poly‑time inverter) is the local‑PRG / one‑way‑function assumption — `P ≠ NP`‑strength
  (OWF ⇒ `P ≠ NP`), so it cannot be discharged by any construction and is NOT.  Established restricted security:
  the family provably resists low‑degree algebraic (`majority_defeats_low_degree_separator`), `AC⁰[p]`
  (unconditional `majority_not_in_AC0p`), and bounded‑crossing/locality (debt bridges).  Each restricted class is
  a theorem; their union over *all* poly inverters is `GoldreichMajHard` = the open problem.  The right
  primitive, provably hard against every formalized restricted attack, with the single remaining hypothesis being
  exactly `P ≠ NP`.  No further construction reduces it.

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
   *Built faithfully (`…WilliamsCashout`):* `williams_cashout` is the genuine three‑part structure
   `(speedup: smallCircuits ⇒ fastSat) + (hierarchy: fastSat ⇒ collapse) + (noCollapse)` ⇒ `¬ smallCircuits` —
   the lower bound from *contradiction*, not boundary‑bounding, so it passes the `d_obs < r` ceiling.
   `cashout_with_margin` makes the threshold explicit.  **The framework supplies the algorithmic half:** a
   low‑boundary observer is a structured fast‑SAT algorithm (`dpSat_beats_bruteforce`) with savings `n − r =
   Ω(n)` (`margin_le_of_correct`) — *more* than the `n^{ω(1)}` the hierarchy needs, so unlike the boundary
   routes the **margin is not the blocker**.  `noCollapse` (the nondeterministic time hierarchy) is real and
   provable.  **Two open inputs remain:** (i) a *decision‑hard* family whose cheap separator compresses
   witnesses (Tseitin is decision‑easy, so its fast algorithm triggers no collapse — correctly, it's in `P`);
   (ii) the **NEXP→NP descent** (Williams gives `NEXP ⊄ ACC⁰`; the polynomial‑level hierarchy is far weaker).
   These are the field's frontier (natural proofs / relativization / algebrization), not Lean gaps.
   *Observer‑centric hybrid (`…ObserverWilliams`):* `observer_centric_williams` composes the two engines as one
   theorem — `(raveling: low‑action ⇒ separator in K) + (separatorSpeedup) + (hierarchy) + (noCollapse)` ⇒ no
   low‑action SAT observer.  N‑frame supplies the geometry (raveling, provable for restricted K); Williams
   supplies the engine (hierarchy, the teeth).
   *Decision‑hard family, base case (`…GoldreichPredicate`):* the gadget lab's failure was algebraic immunity
   1.  `tsa_algebraic_immunity_ge_two` verifies (`decide`) that Goldreich's TSA predicate
   `x₀⊕x₁⊕x₂⊕(x₃∧x₄)` has `AI ≥ 2` — the linear prefix removes the degree‑1 annihilator that collapsed the bare
   AND.  This is the right primitive (Goldreich/Applebaum local PRG = nonlinear expander CSP) at its base case;
   honest caveats: `AI = 2` is only the smallest immunity, and the family's *decision*‑hardness is a
   cryptographic *conjecture* (a provable one `= P ≠ NP`).

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
