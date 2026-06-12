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

So `hdebt` is proved exactly where the boundary is *constrained* — sub-linear width *throughout*, then the
larger **bounded-total-action** class (spikes allowed, integral bounded), and now the **bounded-growth**
class (spikes allowed but not instant) — a streaming / bounded-width / small-space-style restricted lower
bound.  The chain of escapes is now closed in order: hide-boundary-over-time (conservation), distribute as
spikes (total-action), instant spike (locality `r`).  The fooling-debt mechanism caps at `B < log K ≈ cn`;
the **last** escape is **unbounded growth rate** — a single step with `r = poly` (reading `poly` input bits /
growing a `poly`-bit configuration at once) makes `2^{B_0 + r·T}` exponential and the bound vacuous.  That
poly-per-step / linear-to-poly-boundary case is the genuine ceiling and the open `P ≠ NP` core, not a gap in
the formalization.

## 7. Honest status

The contribution is genuine and bounded: the **dynamical conservation of the time-integrated boundary action
is a theorem** (closing the over-time loophole), the **debt mechanism is a theorem**, the **reduction to
`hdebt` is a theorem**, and **`hdebt` is proved on the bounded-boundary (sub-linear-width) class**.  It does
**not** prove the SAT lower bound: the general `hdebt` — every trajectory, *unbounded* boundary — is the open
quantifier (a poly-time decider may use poly space, boundary up to `poly`, escaping the sub-linear regime),
named not faked.  What changed across this arc: the God Move became a *dynamical* boundary-action theory; the
open problem is sharpened to one statement; and that statement is now *proved on the restricted class where
the boundary cannot grow*, with the unbounded-boundary case standing as the irreducible `P ≠ NP` core.
