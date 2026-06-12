# Observer-time boundary debt — the dynamical God Move

A scope note for the new-maths attack on the all-decompositions wall, refined by the N-Frame book's
**observer time τ**.  It turns the God Move from a *static* boundary theory (boundary at one cut) into a
*dynamical* **boundary-action** theory (boundary cost integrated across observer time).  Files:
`ComputationalDepthBoundaryDebt.lean`, `ComputationalDepthObserverTimeDebt.lean`.

**Status:** the conservation accounting is **proved**; the SAT super-debt is the **open** quantifier
(`= CookLevinFrontierHyp`).  This is a reformulation that closes one loophole, **not** a proof of `P ≠ NP`.

---

## 1. The idea (from observer time τ)

The book's observer-time picture — an observer cannot skip steps; τ is the sequence of epistemic updates;
each update has informational cost; the observer has a bounded cognitive light cone; branch selection
minimizes epistemic action — maps onto a **time-integrated boundary action**

```
S_obs  =  ∑_τ ( B_τ + D_τ + E_τ − A_τ )
```

* `B_τ` boundary entropy at update τ;   `D_τ` merge debt (decomposition freedom);
* `E_τ` approximation error;            `A_τ` expander amplification gain.

**Why this is the right fix.**  Every static-boundary attempt hit the same wall: a machine *hides* boundary by
**changing decomposition over time** (EQUALITY: carry one bit over a cheap streaming cut).  The book's lesson
is that the invariant is not boundary *size* at one cut but boundary *cost across observer time* — and the
**integral `S_obs` is conserved** even though each `B_τ` can be made small.

## 2. The conserved quantity: distinguishability debt

`D_τ` = **debt** = the number of must-be-separated continuation pairs the observer has currently *merged*
(given the same boundary state at τ).  A *correct* observer ends with debt `0` (all distinguishable
continuations separated).

## 3. What is proved (the conservation accounting)

* `merge_creates_debt`, `correct_view_zero_debt` — debt counts merged must-separate pairs; correctness ⇒
  debt `0`; merging `K` distinguishable pairs ⇒ debt `≥ K`.
* `debt_conservation_varying` — **the integral is conserved**: `debt 0 ≤ debt T + ∑_{τ<T} rate τ`, with the
  per-step servicing `rate τ` *allowed to vary with τ* (the machine changing decomposition).
* `correct_needs_action` — a faithful observer must spend action `≥` its initial debt: `debt T = 0 ⇒
  debt 0 ≤ S_obs`.
* `bounded_action_fails` — **bounded observer-time action ⇒ faithful decision impossible**: `S_obs < debt 0
  ⇒ debt T ≠ 0` (a must-separate pair stays merged — the observer errs).

So **"merge now ⇒ pay later" is a theorem**, and crucially it is the *time-integrated* version: changing
decomposition over τ does not reduce `S_obs`.  The streaming loophole (cheap per-step boundary) is allowed and
the integral still tracks the debt.

## 4. HAL's schema → status

| schema item | content | status |
|---|---|---|
| `merge_creates_debt` | merged distinguishable pair ⇒ debt | ✅ proved |
| `debt_conservation_or_payment` | debt paid by later boundary, or correctness fails | ✅ proved (`bounded_action_fails`) |
| `expander_amplifies_debt` | expander spreads local debt globally (servicing-rate tightness) | **named** — the expander input (§Vb capstone) |
| `bounded_time_boundary_fails` | too-small total action ⇒ faithful decision impossible | ✅ proved (`bounded_action_fails`) |

## 5. The open input (unchanged)

For SAT: the initial debt `debt 0` (distinguishable witness-branch pairs) is **super-logarithmic**, and
`rate τ = O(B_τ)` with `∑_τ B_τ` small for any *low-boundary* trajectory — so **no low-boundary observer-time
trajectory carries the witness-branch debt across all τ without exploding `S_obs` or erring**.  Proving that
for SAT under *every* trajectory is the open all-decompositions quantifier, now in observer-time form.

## 6. The full proved chain (debt arc, after §1–5)

The debt programme now runs from conservation to a genuine restricted lower bound, with the open quantifier
isolated to one statement:

* **Conservation** (`ComputationalDepthBoundaryDebt.lean`, `…ObserverTimeDebt.lean`) — `merge_pay`,
  `debt_conservation_varying`, `correct_needs_action`: `S_obs ≥` initial debt, even with time-varying
  boundary.  Closes the over-time loophole.
* **Mechanism — step 4's engine** (`ComputationalDepthFoolingDebt.lean`) — `foolingSet_forces_debt`: a
  fooling set of size `K` viewed at boundary `B` forces debt `≥ K − 2^B`; the expander amplifies `K` to
  `2^{Ω(n)}`.
* **Reduction** (`ComputationalDepthSATActionConjecture.lean`) — `no_low_action_of_high_debt`: "SAT has no
  low-action trajectory" *follows from* `hdebt` (super-log debt under **every** trajectory) via conservation.
  `hdebt` **is** `P ≠ NP`; stated as an explicit hypothesis, **not** proved.
* **`hdebt` proved on a restricted class** (`ComputationalDepthBoundedBoundaryDebt.lean`) —
  `bounded_boundary_time_lower_bound` / `bounded_boundary_tradeoff` / `bounded_boundary_low_resource_fails`:
  for **bounded-boundary-throughout** trajectories (servicing rate `≤ 2^B`, i.e. width `≤ 2^B`), a correct
  decider of a fooling-set-`K` instance needs `T · 2^B ≥ K − 2^B`, so `T ≥ K/2^B − 1` = **super-poly** for
  `K = 2^{Ω(n)}`, `B = o(n)`.  A low-resource bounded-boundary decider provably **errs**.

* **`hdebt` proved on the larger bounded-total-action class** (`ComputationalDepthAverageBoundaryDebt.lean`) —
  `average_boundary_tradeoff` / `average_boundary_low_action_fails`: the boundary may **spike** at individual
  steps; only the **total** service capacity is constrained.  A correct observer with time-varying boundary
  `B_τ` satisfies `|P| ≤ 2^{B_0} + ∑_{τ<T} 2^{B_τ}` — the total boundary action must cover the fooling set,
  however it is distributed across observer time (a low-total-action observer provably **errs**).  This is
  strictly larger than bounded-boundary-throughout (occasional spikes allowed) and much closer to real
  machines.

* **Burst escape closed under locality** (`ComputationalDepthBurstBoundaryDebt.lean`) —
  `burst_boundary_time_lower_bound` / `burst_boundary_low_resource_fails`: the single-spike escape assumed the
  observer could jump to boundary `log|P|` in one step.  Adding the explicit **locality** hypothesis that the
  boundary grows `≤ r` per step (`B_{τ+1} ≤ B_τ + r` — bounded read-rate / fan-in / write per step) gives
  `B_τ ≤ B_0 + r·τ`, hence **`|P| ≤ (T + 1) · 2^{B_0 + r·T}`**: the spike's height enters the exponent through
  `r·T`, so for `|P| = 2^{Ω(n)}`, `B_0 = O(log n)`, `r = O(1)` it forces **`T = Ω(n/r)`** — a genuine *time*
  lower bound the instant spike cannot dodge.  "The spike pays its height in time."

* **Explicit fooling family + named bounds** (`ComputationalDepthExpanderFoolingInstance.lean`) —
  `hypercubeFool n` is the **complete** must-separate relation on `Fin n → Bool`; `hypercube_card` gives
  `|P| = 2^n` (the maximal fooling set, the explicit realisation of "`2^{Ω(n)}` pairwise-distinguishable
  branches" the expander/`Kₙ`-Tseitin forcing guarantees).  Instantiating the abstract tradeoffs yields named
  corollaries: `hypercube_lowBoundary_requires_superpoly_time` (`2^{n−B} ≤ T+1`, **super-poly** for
  `B = O(log n)`) and `hypercube_bounded_growth_requires_linear_time` (`2^n ≤ (T+1)·2^{B_0+r·T}`, **linear**
  `T = Ω(n/r)` for `r = O(1)`).

* **Adaptive trajectories — decomposition changing over time** (`ComputationalDepthAdaptiveTrajectory.lean`,
  `ComputationalDepthAdaptiveTrajectoryDebt.lean`): an adaptive observer may use a *different* decomposition
  `D_τ` at each step.  Two honest results: (i) the conservation is **decomposition-change-agnostic** —
  `adaptive_total_action` proves the budget bound holds however `D_τ` varies, so adaptivity alone does not
  escape; (ii) the missing ingredient is an explicit **switch cost** `SwitchCost_τ` for translating unresolved
  information between coordinate systems, giving `adaptive_boundary_tradeoff`:
  **`|P| ≤ 2^{B_0} + ∑_τ 2^{B_τ} + ∑_τ SwitchCost_τ`** — *either the boundary pays or the switch pays*.
  Specialisations: `fixed_decomposition_recovers_average` (`SwitchCost ≡ 0`), bounded-switch
  (`∑ SwitchCost ≤ C ⇒ |P| ≤ 2^{B_0} + ∑ 2^{B_τ} + C`).  And
  `single_decomposition_resolving_fooling_needs_full_boundary`: no single decomposition resolves a fooling set
  with sub-`log|P|` boundary (the "free perfect decomposition" escape is blocked).  The load-bearing
  restriction is now named precisely: **`Local`** (per-step debt reduction `≤ 2^{B_τ}`) — the EQUALITY
  streaming escape is a *non-local* trajectory, not merely an adaptive one.
* **A lower bound on `SwitchCost` for the explicit witness geometry** (`ComputationalDepthSwitchCostLowerBound.lean`):
  rearranging the tradeoff isolates the switch channel — `switchCost_lower_bound`:
  `∑_τ SwitchCost_τ ≥ |P| − 2^{B_0} − ∑_τ 2^{B_τ}`.  For the explicit `2^n` hypercube witness geometry on a
  **low-boundary** trajectory (`B_τ ≤ b`), `hypercube_lowBoundary_switchCost_superpoly`:
  `∑_τ SwitchCost_τ ≥ 2^n − (T+1)·2^b` = **super-poly** for `b = O(log n)`, `T = poly`.  So "translating
  witness-branch information across decompositions is expensive" is **proved** — for the maximal witness
  geometry, conditional on low boundary.  HONEST: still restricted — vacuous once `(T+1)·2^b ≥ 2^n` (pay in
  boundary instead, the linear/poly-space escape), and it is the *complete* `2^n` fooling set, not SAT under a
  freely-chosen decomposition.  The unconditional version (both channels expensive under every decomposition)
  is `P ≠ NP`, not proved.

* **Expander no-hiding — residual subfunction explosion** (`ComputationalDepthExpanderNoHiding.lean`): the
  bridge from structured forcing to SAT debt, in honest restricted form.  A decomposition reading few variables
  leaves crossing constraints whose values on the continuation form a **residual outcome vector**; if `r`
  crossing constraints are independent (the residual map surjects onto `Fin (2^r)`), there are `2^r` pairwise
  distinguishable continuations.  `surjective_residual_forces_debt`: any boundary-`B` observer then carries
  residual debt `2^r − 2^B`; `no_hiding_superlog`: for `B ≤ r − 1`, debt `≥ 2^{r−1}` = super-log for
  `r = Ω(n)`.  The explosion ⇒ debt step is fully proved; **expansion** (proved for `Kₙ` in the width kernel)
  supplies `r = Ω(n)` independent crossing constraints for variable-subset reads.  HONEST: `hsurj` is for a
  *fixed* residual map (a fixed decomposition).  Proving the residual *cannot collapse* under every cheap
  adaptive decomposition is the min-over-decompositions = `P ≠ NP`.  This file reduces that core to one clean
  property — **residual non-collapse under every cheap decomposition** — with the debt following mechanically.
* **`hsurj` DISCHARGED for expander Tseitin** (`ComputationalDepthExpanderResidualSurjective.lean`): the
  residual-non-collapse property is now *proved* (not assumed) for the natural read-set decomposition.  Chain:
  expansion (`HasExpansion c`, `c ≥ 1`) ⇒ `constraints_linearIndependent` (the vertex constraints over a medium
  read-set `w : ι → V`, `2·|ι| ≤ |V|`, are F₂-independent — a vanishing combination is `combination S = 0`,
  forbidden by the kernel's `exists_combination_ne_zero_of_expansion`) ⇒ `mulVecLin_surjective_of_row_indep`
  (full row rank ⇒ surjective residual onto `2^{|ι|}` outcomes) ⇒ `expander_residual_forces_debt` (every
  boundary-`B` observer carries residual debt `2^{|ι|} − 2^B`).  For `|ι| = ⌊|V|/2⌋ = Ω(n)`, `B = O(log n)`:
  super-log, **with no surjectivity hypothesis left**.  HONEST: this is for the *read-set* decomposition class
  only; residual non-collapse under *every* cheap adaptive decomposition is still the open min = `P ≠ NP`.
  What it removes: the doubt "is the residual actually large for a real hard instance?" — for expander reads,
  provably yes, via the same expansion that powers the width kernel.
* **Step 4 — the adaptive bottleneck** (`ComputationalDepthAdaptiveBottleneck.lean`): an adaptive observer with
  low *total* action need not be cheap at every step, but must be cheap at *some* step.
  `adaptive_bottleneck_exists` (pigeonhole): `∑_{τ<T} cost τ ≤ A ⇒ ∃ τ, T·cost τ ≤ A` (the minimising step is
  below average).  `cheap_trajectory_has_residual_debt_bottleneck` (the reduction): for a trajectory with total
  boundary action `≤ A` whose residual is non-collapsing at every step, a bottleneck step carries residual debt
  `2^r − A` — super-log for `r = Ω(n)`, `A` sub-`2^{Ω(n)}`.  The **only** open input is non-collapse under the
  observer's *own* (possibly non-read-set) decompositions = residual non-collapse under every cheap adaptive
  decomposition = the min-over-decompositions quantifier = `P ≠ NP` (HAL's step 5).  Everything *around* that
  one property is now proved: the bottleneck always exists, and non-collapse there mechanically yields the debt.
* **Linear/affine non-collapse PROVED** (`ComputationalDepthAdaptiveResidualNonCollapse.lean`): the next rung
  of the staged ladder.  `finrank_map_ker_ge` (abstract `F₂` rank bound: `finrank (range res) − finrank
  (range L) ≤ finrank ((ker L).map res)`) ⇒ `expander_linear_decomposition_noncollapse`: for expander Tseitin's
  residual (rank `|ι| = Ω(n)`) and **any** `F₂`-linear observation `L` of dimension `k`, the residual on `ker L`
  has rank `≥ |ι| − k`.  So **no `F₂`-linear coordinate change + `k`-dim read can collapse the expander residual
  below `2^{|ι|−k}` outcomes** — `AdaptiveResidualNonCollapse` holds for the linear/affine class.  Still not
  `P ≠ NP`: a non-linear (branching / low-degree / arbitrary) decomposition is unconstrained by this.
* **Framework ceiling, as a theorem** (`ComputationalDepthDebtFrameworkBarrier.lean`):
  `tradeoff_vacuous_of_high_initial_boundary` (the bound is content-free once `|P| ≤ 2^{B_0}`) and
  `hypercube_brute_force_escape` (a single full-boundary view resolves the `2^n` geometry with zero debt) —
  the brute-force / linear-space escape is *realised*, so the fooling-debt mechanism provably forces nothing
  against full-boundary observers.  Draws the provable-here / open-there line as a proved statement.

So `hdebt` is proved exactly where the boundary is *constrained* — sub-linear width *throughout*, then the
larger **bounded-total-action** class (spikes allowed, integral bounded), and now the **bounded-growth**
class (spikes allowed but not instant) — a streaming / bounded-width / small-space-style restricted lower
bound.  The chain of escapes is now closed in order: hide-boundary-over-time (conservation), distribute as
spikes (total-action), instant spike (locality `r`).  The fooling-debt mechanism caps at `B < log K ≈ cn`;
the **last** escape is **unbounded growth rate** — a single step with `r = poly` (reading `poly` input bits /
growing a `poly`-bit configuration at once) makes `2^{B_0 + r·T}` exponential and the bound vacuous.  That
poly-per-step / linear-to-poly-boundary case is the genuine ceiling and the open `P ≠ NP` core, not a gap in
the formalization.

## 7. P≠NP reduced to adaptive residual non-collapse (the final jump)

The arc terminates at a single, sharply-stated open property — the God-Move target:

> **`AdaptiveResidualNonCollapse`.**  For expander Tseitin / SAT, **every cheap adaptive decomposition
> preserves `2^{Ω(n)}` residual outcomes** (the residual map does not collapse below super-poly outcomes for
> any decomposition the observer is free to choose with sub-`Ω(n)` boundary action).

The reduction is complete in both directions of plumbing:

* **It suffices.**  `AdaptiveResidualNonCollapse` ⇒ at the bottleneck step of any cheap trajectory
  (`adaptive_bottleneck_exists`) the residual is non-collapsing, so `surjective_residual_forces_debt` /
  `cheap_trajectory_has_residual_debt_bottleneck` forces super-log debt, contradicting cheapness — i.e. SAT
  has no cheap adaptive observer ⇒ `P ≠ NP`.  Every link here is **proved**; only the property is assumed.
* **It is the theorem.**  `AdaptiveResidualNonCollapse` quantifies over *all* decompositions; proving it *is*
  the min-over-decompositions separation.  It cannot be discharged naively.

**Staged ladder (what is proved vs open):**

| decomposition class | residual non-collapse | file |
|---|---|---|
| read-set (vertex-parity) | ✅ proved (`expander_residual_forces_debt`) | `…ExpanderResidualSurjective` |
| `F₂`-linear / affine | ✅ proved (`expander_linear_decomposition_noncollapse`) | `…AdaptiveResidualNonCollapse` |
| bounded-locality / junta / branching-program | ✅ proved (`expander_bounded_locality_noncollapse`) | `…BoundedLocalityNonCollapse` |
| **every** adaptive decomposition | ⛔ open = `P ≠ NP` | — |

The bounded-locality rung (`bounded_support_forces_debt`): a view depending on only `|W|` variables — *with
arbitrary output complexity* (junta / shallow decision tree / read-bounded branching program) — is coarser
than the linear projection `π_W` (`debtCount_mono`), so it carries residual debt `≥ 2^{|ι|} − 2^{|W|}`.  New
content beyond output-boundary no-hiding: the output alphabet may be exponential, yet *locality* (variables
read), not output size, bounds the view's power.

Two classes are now discharged using only the expansion already proved in the width kernel.  The honest
remaining mathematics is the *common invariant* that would let the per-class proofs generalise to all
decompositions — which is exactly the separation, named not faked.

**Holonomy / curvature schema** (`ComputationalDepthBoundaryHolonomy.lean`) — a restricted scaffold for the
high-support nonlinear regime (HAL's curvature direction).  A loop of charts has a net transport (holonomy)
`h`; a *loop-invariant* (cheap, returns-to-same-state) observer has `view ∘ h = view`.
`nonzero_holonomy_forces_debt` / `holonomy_forces_debt_card`: if the holonomy *twists* the residual
(`res (h c) ≠ res c`) the observer has merged a must-separate pair — debt `≥` #twisted configs.  `F₂` instance
`parity_loop_holonomy`: an additive residual with an odd-charge translation `v` (`res v ≠ 0`, the Tseitin
odd-cycle obstruction) flattened by the observer (`view (c+v)=view c`) twists **every** config — debt `=
|Config|` (`= 2^L` on the cube).  HONEST: the holonomy is *supplied* (`res v ≠ 0` + view flattens `v`); the
open `P ≠ NP` content is the converse — that **every** cheap atlas of expander Tseitin is *forced* to flatten
some `v` with `res v ≠ 0` (expander constraints have nonzero curvature against all cheap coordinate systems).
Next rung: expander many-loop amplification, then the forced-twist converse.  Not proved; named.

**Expander many-loop amplification** (`ComputationalDepthExpanderHolonomyAmplification.lean`) — closes the
single-loop escape (observer flattens a *different* direction).  `additive_holonomy_forces_debt` lifts the
holonomy lemma to a vector residual; `expander_manyloop_holonomy`: any observer that flattens a *subspace* `W`
of directions (`view (c+x)=view c` ∀ `x∈W`) of codimension `< |ι|` (`finrank W > |Edge|−|ι|`) carries the full
debt `2^{|Edge|}` — because expansion gives the residual rank `|ι|`, so `W ⊄ ker(residual)`, so `W` contains a
twisting direction.  Curvature reading: **expander constraints have nonzero curvature against every
low-codimension coordinate flattening** — the observer cannot flatten its way around all loops.  HONEST: a
`W`-periodic view has `≤ 2^{codim W}` values, so this is the curvature lens on effective-boundary no-hiding;
genuinely nonlinear non-periodic high-boundary atlases remain the open `P ≠ NP` quantifier.

## 7b. The real gap: time–space tradeoff and the Williams route

The ladder audit is blunt: every decomposition rung (read-set, linear, bounded-locality, holonomy/curvature)
reduces to "effective boundary `< r` ⇒ debt", and `hypercube_brute_force_escape` proves the mechanism is
**empty for boundary `B ≥ r ≈ n`**.  So the genuine open gap is **not** a residual-collapse lemma — it is the
**time–space tradeoff**: a poly-*time* decider may use poly *space* (`B ≥ n`), above the cap.

`ComputationalDepthTimeSpaceWilliamsBridge.lean` sets up the honest attack on exactly that gap:

* **Lower-bound (debt) side, proved.**  `time_space_law`: `|P| ≤ (T+1)·2^B`.  `time_space_tradeoff_curve`:
  `T+1 ≤ Tb ⇒ |P| ≤ Tb·2^B`, i.e. a hard instance (`|P| = 2^{Ω(n)}`) decided in poly time needs space
  `B = Ω(n)` — a genuine *restricted* time–space lower bound (streaming / branching-program flavour).  This
  caps the direct route at linear space.
* **Upper-bound (Williams) side, skeleton.**  `dp_speedup`: a low-boundary decomposition gives a
  sub-brute-force SAT algorithm (DP engine, proved).  `williams_route` / `noncollapse_via_williams`: the
  reduction `CheapDecomp → FastSat → Sep`, with the contrapositive `(cheap ⇒ fast) → ¬fast → ¬cheap`
  (no fast SAT ⇒ no cheap decomposition = non-collapse).  This route goes *past* the `B < n` cap — it needs
  no space lower bound, only the impossibility of fast SAT.

**Two named open inputs** (not faked): (1) the **Williams diagonalisation** `FastSat → Sep` (the
nondeterministic-time-hierarchy theorem; deep, not reproved); (2) **instantiation margin** — that SAT's cheap
decompositions feed the bridge with a speedup strong enough to compound against the hierarchy (a mild
sub-brute-force speedup is not enough).  `P ≠ NP` is not proved; the gap is now located in exactly these two.

## 8. Honest status

The contribution is genuine and bounded: the **dynamical conservation of the time-integrated boundary action
is a theorem** (closing the over-time loophole), the **debt mechanism is a theorem**, the **reduction to
`hdebt` is a theorem**, and **`hdebt` is proved on the bounded-boundary (sub-linear-width) class**.  It does
**not** prove the SAT lower bound: the general `hdebt` — every trajectory, *unbounded* boundary — is the open
quantifier (a poly-time decider may use poly space, boundary up to `poly`, escaping the sub-linear regime),
named not faked.  What changed across this arc: the God Move became a *dynamical* boundary-action theory; the
open problem is sharpened to one statement; and that statement is now *proved on the restricted class where
the boundary cannot grow*, with the unbounded-boundary case standing as the irreducible `P ≠ NP` core.
