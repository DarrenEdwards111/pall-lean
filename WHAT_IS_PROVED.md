# WHAT IS PROVED — the converged picture

A single honest ledger of the observer‑boundary / inverter‑frontier programme. All "proved" entries are
Lean 4 / Mathlib, `sorry`‑free, axioms `[propext, Classical.choice, Quot.sound]` (some pure‑`Nat`/`decide`
lemmas use a subset; `native_decide` uses are flagged and absent from the load‑bearing results). Branch
`razborov-recoverRho-wip`.

**This is not a proof of `P ≠ NP`.** It is a formalized restricted lower‑bound theory in which *every reducible
piece has been discharged* and the separation is reduced to **one named statement**, proved equivalent in
strength to `P ≠ NP` and shown — as a theorem — to be unreachable by the methods at hand.

---

## The one‑paragraph summary

A single explicit predicate, **Majority**, has been formalized as **optimal** (`AI(Maj_n)=⌈n/2⌉`) and shown to
**unconditionally resist all four restricted inverter classes** the programme can express — low‑degree algebraic,
`AC⁰[p]`, bounded‑crossing, and bounded‑locality. The last of these, `AC⁰[p]`, was closed by formalizing the
full `MOD_q ≤_{AC⁰[p]} Majority` reduction circuit, making `Majority ∉ AC⁰[p]` an unconditional theorem. The
earlier *complementarity obstruction* — that the `AC⁰[p]`‑resisting witness (parity/`MOD_q`) provably *fails*
low‑degree resistance — is thereby **resolved**: Majority does both, with no remaining hypothesis.

From there the wall was pushed across three axes in turn — **space**, then **time**, then **explicitness** — each
closed to its exact ceiling (Part 4½). The space axis is *settled*: the separating boundary is **exactly `r`**. On
the decision axis a Williams‑style cash‑out lands an **unconditional** lower bound — *some* function escapes every
cheap decider — but only nonconstructively. The remaining residue is isolated as a single named conjunct
(`InNP`) and shown *unbridgeable by counting*: the counting property is large and useful, so under crypto the
**natural‑proofs barrier** forbids it from being constructive. The strongest *explicit*, *non‑natural* decision
bound the corpus reaches is the **Nečiporuk frontier** (`n²/log n`) — real, explicit, barrier‑evading, and
provably capped there. The single gap that remains is resistance against **all** polynomial‑time inverters /
**explicit** decision hardness above `n²/log n`, which appears in five equivalent forms, all `= P ≠ NP`, and which
a proved gap theorem shows the action/space machinery cannot by itself reach.

---

## 1. Proved unconditionally

**The headline — one predicate, every restricted class.**
- **Optimal algebraic immunity.** `AI(Maj_{2t-1}) = ⌈n/2⌉` (`majority_AI_optimal`): the two‑sided lower bound
  (`majority_algebraic_immunity_two_sided`, via the from‑scratch `F₂` Möbius inversion `anf_involutive` +
  degree‑preserving complement symmetry `degreeLt_compl`) and the matching upper bound `AI(f) ≤ ⌈n/2⌉` for
  *every* `f` (`algebraic_immunity_le_ceil`). No `decide`; scales with arity.
- **`Majority ∉ AC⁰[p]` — UNCONDITIONAL** (`…ModqReducesMajority`): the full `MOD_q ≤_{AC⁰[p]} Majority`
  reduction circuit (`thresholdCirc` via `padInputs`; `modqCirc = ⋁_{k≡0}[#ones=k]`; eval‑correctness, `AC⁰[p]`,
  constant depth, polynomial size, and an `IsPolyBounded` closure built from scratch) discharges `AC0pReduction`
  ⇒ `majority_not_in_AC0p`.
- **The simultaneous‑resistance wall, realized on Majority.** `majority_simultaneous_resistance`: `majorityF2`
  unconditionally satisfies **both** binding resistances (low‑degree *and* `AC⁰[p]`), so
  `SimultaneousAlgAC0pResistance` holds with **no remaining hypothesis** — the binding pair of
  `…UnifiedInverterFrontier`, formerly only conditional, now a single‑predicate theorem.

**The engines and invariants.**
- **Dynamical debt accounting.** `debtCount`; conservation (`debt_conservation_varying`, `merge_pay`,
  `correct_needs_action`); mechanism `foolingSet_forces_debt` (`debt ≥ K − 2^B`). Gauge invariance
  `debtCount_relabel_invariant` (no frame change lowers debt).
- **Observer‑boundary invariant.** Fooling‑set principle: `K` non‑mergeable sectors ⇒ boundary `≥ log₂ K`.
- **The `F₂` Möbius / ANF inversion** (Mathlib lacks it): `anf_involutive`, from the interval count
  `card_filter_subset_between`.
- **AI ⇒ separator resistance.** `majority_defeats_low_degree_separator`: no nonzero degree‑`<t` function
  annihilates `Maj`/`¬Maj`.
- **The geometric core of the gap.** `dimension_gap_forces_debt` / `positive_gap_forces_debt`: a low‑`d_obs`
  observer of a high‑`d_res` residual carries debt `≥ 2^{d_res} − 2^{d_obs}`.
- **The cash‑out chains (pure logic, no axioms).** `williams_cashout`, `ravel_wedge`,
  `observer_centric_williams`, `goldreich_observer_williams`, `majority_observer_williams`.
- **The speedup ingredient is PROVED, not assumed** (`…NFrameSpeedupBridge`): a low‑action / low‑boundary
  inverter's reachable‑set DP visits only `∑ 2^{Bτ} = action` configurations, so `lowAction_beats_bruteforce`
  (`action < 2^n` ⇒ DP cost `< 2^n`) and `lowSpace_beats_bruteforce` (via `subcritical_of_lowspace`) make
  `separatorSpeedup` a theorem — the N‑frame side genuinely supplies the Williams cash‑out's speedup half.
  `nframe_speedup_then_no_lowaction` closes the chain, leaving `noCollapse` (the hardness) as the only assumed
  input.
- **The raveling ingredient is PROVED for a concrete `K`** (`…RavelingConcrete`): for `K = {effective dimension
  < r}`, `raveling_lowAction` shows a low‑action observer lands in `K` — the *dynamical* action bounds the
  *structural* dimension (a single layer's capacity `2^{Bτ}` is one summand of `action`, so the decision
  alphabet `≤ 2^{B(T-1)} ≤ action < 2^r`).  With `boundedDim_noSeparator` (`residual_view_card_forces_debt`),
  `lowAction_no_separator`: **no low‑action observer separates the dimension‑`r` residual.**  So for restricted
  `K` *both* observer‑Williams premises (`raveling`, `separatorSpeedup`) are now theorems — only the hardness
  (`noCollapse`) is assumed.  The catch: `K` here is not all of `P` (a poly‑*space* decider keeps a
  full‑dimension view — the brute‑force escape), and extending `raveling` to every `P` observer is the
  `P ≠ NP`‑strength step.
- **`raveling` extended to bounded‑space `P` observers** (`…RavelingBoundedSpace`): a *space* bound genuinely
  bounds the boundary (a space‑`s` machine has `≤ 2^s` configs, so its boundary view takes `≤ 2^s` values).
  `boundedSpace_raveling` (`s < r ⇒` in `K`) and `boundedSpace_no_separator` (a `SPACE(s)`, `s<r`, decider
  cannot separate the dimension‑`r` residual); `boundedSpaceTime_subcritical` is the dynamical form
  (`Tb·2^s < 2^r ⇒ action < 2^r`, via `subcritical_of_lowspace`).  This captures `SPACE(s)` for `s < r ≈ Ω(n)`
  (sub‑residual‑dimension space) — **not** all of `P`: a poly‑*space* decider (`s = n^k ≫ r`) keeps a
  full‑dimension view and escapes `K`.  That last gap is exactly `P ≠ NP`.
- **The separating boundary is TIGHT — exactly `r`** (`…TightSeparatingSpace`): `residual_separates` (the
  boundary‑`r` residual view is a zero‑debt separator — the upper bound) matched with `below_r_fails` (no
  boundary‑`<r` view separates — the lower bound) gives `separating_boundary_tight`: separating boundary `= r`
  exactly.  The hard family is *space‑`r`‑decidable* (the full‑boundary decider), so space is pinned and the
  obstruction to a fast algorithm is **not space** — it is **time**.  The debt/space machinery is exact on the
  space axis and provably cannot reach the time axis (`distinguishability_debt_not_time_lower_bound`) — which is
  where `P ≠ NP` lives.

## 2. Proved for restricted classes (the four resisted inverter classes + the corpus)

The four restricted inverter classes — each `InversionHardness` discharged unconditionally:
- **Low‑degree algebraic** — `no_low_degree_algebraic_inverter` (from `AI(Maj)=t`): the linearization / Gröbner
  attack provably fails.
- **`AC⁰[p]`** — `no_AC0p_inverter_modq` / `no_AC0p_inverter_parity` (Razborov–Smolensky chain: `Layer3`
  approximation + `Layer4` no‑approximation core `mod_q_indicators_false` + `Layer7` family bounds), lifted to
  Majority by the reduction above.
- **Bounded‑crossing** — `boundedCrossing_not_correct_inverter` (`q^w<2^r` ⇒ not a separator), the
  crossing‑sequence bridge `crossingSequence_no_separator`.
- **Bounded‑locality (junta)** — `boundedLocality_not_correct_inverter` (`2^{|W|}<2^r` ⇒ not a separator), via
  `bounded_support_forces_debt`.

Supporting restricted lower bounds:
- **Proof‑space.** `tseitin_totalSpace_lower_bound` (expander‑Tseitin total space `≥ c·t`), via the width kernel.
- **Boundary–time tradeoffs.** `bounded_boundary_tradeoff`, average/burst variants, explicit `2^n` witness,
  switch‑cost bound.
- **The decomposition ladder** (each = "effective boundary `< r` ⇒ debt"): read‑set, `F₂`‑linear, locality,
  holonomy, many‑loop amplification.
- **Calibrations** (known bounds through the invariant): AC⁰[p] = Razborov–Smolensky, Nečiporuk `n²/log n`,
  deterministic communication rectangles.

## 3. The Goldreich / local‑PRG terminus

`…GoldreichMajorityPRG` assembles `goldreichMaj` — the Goldreich local function with the optimal‑AI Majority
predicate over an expander hypergraph — and proves its structural properties: `goldreich_eval_local` (locality),
`majPred_const_true/false` (non‑degeneracy), `goldreichMaj_no_lowAction_inverter` (the conditional separation via
observer‑Williams). The family provably resists every restricted class of §2. Its **full** security
`GoldreichMajHard` (no poly‑time inverter) is the local‑PRG / one‑way‑function assumption — `P ≠ NP`‑strength
(OWF ⇒ `P ≠ NP`) — and is *the wall*: no construction discharges it. This is the honest terminus of the
constructive route: the right primitive, provably hard against every formalized restricted attack, single
remaining hypothesis = exactly `P ≠ NP`.

**The convergence, made one object (`…GoldreichHolonomyTerminus`).** The programme's threads are gathered onto
this single candidate: `GoldreichMajorityConvergence` bundles the *discharged* arrows (`raveling`,
`separatorSpeedup`) with the **lone open field** `goldreichMajorityHard`, and `GoldreichMajorityConvergence.terminus`
proves — *depending on no axioms at all* — that no low‑action observer inverts the family, conditional only on that
one field. Every other thread is referenced as discharged: optimal AI (`majority_AI_optimal` ⇒
`majority_defeats_low_degree_separator`), `AC⁰[p]` resistance (`majority_not_in_AC0p`,
`majority_simultaneous_resistance`), the four restricted classes, and the expander hard side
(`goldreich_expander_holonomy_full`: a `DisjointCycles` gadget from the hypergraph has full holonomy rank `2^m`).
*Honest calibration recorded there:* holonomy is an `F₂`/parity (Tseitin) invariant, so it attaches to the
candidate's **expander structure**, not to the non‑linear Majority predicate directly — stated, not forged. So the
constructive route is reduced to one named statement on an explicit, maximally‑calibrated candidate, with
everything else unconditionally discharged and `goldreichMajorityHard = P ≠ NP`‑strength.

## 4. Retired routes (proved false or proved dead — not merely abandoned)

- **`P_ne_NP_unconditional` (old).** Parked `P`‑side content in unproved sockets; retired for honest conditionals.
- **The `B < r` / brute‑force escape.** `hypercube_brute_force_escape`: a full‑boundary view resolves the `2^n`
  geometry with **zero debt** — the fooling‑debt mechanism is *empty* above boundary `≈ n`.
- **Time ⇒ boundary.** `action_unbounded_by_time`: poly *time* yields **no** boundary/action bound. "P‑time ⇒
  cheap observer" is *false*, not open (holds only given a space bound: `subcritical_of_lowspace`).
- **Proof‑hard ≠ decision‑hard.** `tseitin_unsat_of_odd_charge`: expander‑Tseitin is proof‑hard but
  **decision‑easy** (one parity bit).
- **The complementarity obstruction — now RESOLVED.** `parity_not_resists_lowDegree`: the `AC⁰[p]`‑resisting
  parity is affine (`AI ≤ 1`) and provably fails low‑degree resistance — so the *natural* witnesses are
  incompatible. This obstruction is dissolved by the reduction: **Majority resists both unconditionally**
  (`majority_simultaneous_resistance`). What once looked like a barrier to one‑predicate simultaneity is a
  theorem about the wrong witnesses; the right witness (Majority) clears all four.
- **The AND gadget.** `AI = 1` — filtered out; superseded by TSA (`AI=2`) then Majority (`AI=⌈n/2⌉`).
- **Diagonal SPDP / `χ_φ` bound.** Disproved (`rk ≪ #SAT`); barriered short of `VP` vs `VNP` on the permanent.
- **The HM / metacomplexity socket.** Proved *vacuous* by its own iff — repackaging does not reduce strength.

## 4½. The wall's journey across axes — to the explicit frontier

After the restricted‑inverter classes were closed, the wall was driven across three axes in sequence. Each axis
is now closed to its exact, provable ceiling; the residue that survives every axis is the single irreducible
`P ≠ NP` step. The progression is the substance of the explicit‑frontier picture.

**(a) Space — settled, boundary exactly `r` (`…TightSeparatingSpace`, `…RavelingBoundedSpace`).** `raveling` and
`separatorSpeedup` are theorems for restricted `K`; `boundedSpace_raveling` extends `raveling` to `SPACE(s)` for
`s < r ≈ Ω(n)`; and `separating_boundary_tight` pins the separating boundary at **exactly `r`** (`residual_separates`
upper bound + `below_r_fails` lower bound). The hard family is space‑`r`‑decidable, so the obstruction to a fast
algorithm is provably **not space** — it is time. (Summarized in §1, "engines and invariants".)

**(b) Time — the wall relocated, and shown unreachable by space machinery (`…TimeAxisWall`, `…BoundedWidthBPTime`).**
`space_axis_settled` (separator at `r`, none below); `ResidualSeparatorRequiresSuperpolyTime` (the named missing
bridge: the existing boundary‑`r` separator's decision time is super‑poly); `timeAxis_wall` (bridge + threshold ⇒
family ∉ `P`); `space_machinery_cannot_supply_bridge` (the gap — an action/debt bound of *any* size is hit by a
poly‑time single‑step trajectory, so the space‑exact machinery yields *no* time bound). The first restricted *time*
model is bounded‑width branching programs: `bp_width_no_separator` shows a width‑`W` BP with `W < 2^r` carries debt
`≥ 2^r − W > 0` **for every length `L`** — time cannot compensate for bounded width in *realizing* the separator
(honest caveat: realization/classifier bound, not a `1`‑bit decision bound; that gap *is* the time‑axis bridge).

**(c) Decision — an unconditional lower bound, by counting (`…RestrictedCashout`).** A Williams‑style cash‑out that
bites on the `1`‑bit *decision* axis with **no conjecture**: `cheap ⇒ enumerable` (a bounded‑resource decider has a
short description — the proved speedup `…NFrameSpeedupBridge` quantifies it) and contradiction by
counting/diagonalization. `card_boolFun` (`|BoolFun n| = 2^{2^n}`); `cheap_class_misses_function` (a class
`Fin N → BoolFun n` with `N < 2^{2^n}` misses some function); `restricted_cashout` (a cheap enumerable class is
*not surjective* onto all Boolean functions). A genuine, unconditional **decision** lower bound — *some* function
escapes every cheap decider — but the classical counting limitation bites: it is the **existence** (Shannon) form,
*some* hard function, not an *explicit* family.

**(d) Explicitness — the residue isolated as `InNP` (`…ExplicitnessWall`).** The wall moves from decision to
*explicit* decision. One shared target object: `ExplicitFamily`, `HardFor`, the **opaque** `InNP` parameter,
`ExplicitNPHard := ∃ F, InNP F ∧ HardFor F`. `counting_hard_at_each_length` (per‑length hardness, from the
cash‑out); `hard_family_exists` (choice assembles a hard *family* — with **no** `InNP` guarantee);
`explicitNPHard_imp_hardFamily` (the explicit‑NP target is *strictly stronger* — it implies the `InNP`‑free family
counting already gives). So the **entire** residue between what counting proves and what `P ≠ NP` needs is the
single `InNP` conjunct. `InNP` is left an opaque parameter precisely so no "explicitness by counting" move can
sneak in.

**(e) The natural‑proofs barrier — that residue can't be reached by counting (`…NaturalProofsBarrier`).** Blocks
the "explicitness by counting" shortcut directly. `Hard cheap f`, `LargeProperty` (more than half of functions),
`UsefulAgainst`. Proved: `nonHard_card_le` (non‑hard functions `≤ N`), `counting_property_is_large` (for
`2N < 2^{2^n}`, `Hard cheap` is large), `hard_property_useful` (it is useful). `RazborovRudichBarrier` is a *named
hypothesis* (under crypto, no large+constructive property is useful); `counting_property_not_constructive` then
proves the counting property — large and useful — **cannot be constructive** under crypto+RR. So "most functions
are hard" provably cannot be upgraded into an efficient property isolating `NP`; crossing to explicit hardness
needs a **non‑natural** argument. (RR and crypto are parameters, not claims.)

**(f) The explicit, non‑natural frontier — Nečiporuk, capped at `n²/log n` (`…ExplicitNeciporukHardness`).** The
genuine successor to counting and width: an explicit family with a real *decision* lower bound that *evades* the
barrier of (e). Reusing the crossing‑capacity / Nečiporuk machinery, `StorageAccess m` (explicit indirect
addressing) has `2^m` distinct crossing subfunctions, so `storageAccess_decomposable_lb` (every `CrossingModel`
needs `≥ 2^m` states), `storageAccess_escapes_cheap_decomposable` (no capacity‑`<2^m` decomposable decider computes
it), `explicit_family_beats_decomposable` (an explicit family escapes every bounded capacity). This is genuinely
**explicit** (a named function), a **decision** bound (computing `StorageAccess`, not separating a residual),
against a class **richer than width** (decomposable/communication, by distinct subfunctions), and **non‑natural**
(the subfunction count is not a large/constructive property — which is *why* it is provable). Honest ceiling: per
block `2^m`, summed over `Θ(n/log n)` blocks it gives formula size `Θ(n²/log n)` (`…NeciporukHardFunctionAsymptotic`)
— the decades‑old explicit frontier. The method provably tops out here (`crossing_capacity` bounds states by
subfunction count `≤ 2^{block}`). It does **not** reach `P/poly` or `P ≠ NP`.

**(g) Above the Nečiporuk ceiling — the shrinkage / Andreev mini‑arc.**  Can an *explicit* formula‑size bound beat
`n²/log n`?  Recorded honestly across three files:
* **Ceiling, proved (`…NeciporukCeiling`).**  *Why* subfunction counting caps: per block of `b` variables,
  `log₂ #subfunctions ≤ min(2^b, n-b)` (`log_subfunctions_le_min` — a subfunction is a `b`‑bit function *and*
  there are only `2^{n-b}` other‑variable settings).  The two caps cross at `b ≈ log n`, forcing the method to
  `n²/log n`.  So super‑`n²/log n` is **impossible by subfunction counting** — a different method is required.
* **Non‑counting structural base, proved (`…RelevanceLeafBound`).**  The replacement style: `leaves F ≥
  #{variables the function is *sensitive* to}` (`leaves_ge_relevant_card`) — a leaf per relevant variable, *no
  counting of functions*.  `gAnd_needs_n_leaves`: the `n`‑bit `AND`, sensitive to every variable, needs `≥ n`
  leaves.  Modest (linear) alone, but the genuine non‑counting core.
* **Shrinkage amplifier, cited (`…AndreevShrinkageRoute`, `…RestrictionSensitivity`).**  Håstad's shrinkage
  (`Γ=2`, the deep random‑restriction theorem — *named, cited, not reproved, not open*) multiplies the base
  bound: `andreev_leaf_lower_bound` (shrinkage `leaves_restricted·D ≤ leaves` + surviving complexity `H ≤
  leaves_restricted` ⇒ `H·D ≤ leaves`) and `shrinkage_above_neciporuk` (at balanced Andreev params `k³·2^{2k} <
  2^{3k}`, i.e. `n^{3-o(1)} > n²/log n`).  `RestrictionSensitivity` grounds the surviving complexity `H` in the
  *relevance* base: a restriction of a formula doesn't increase leaves (`restrict_leaves_le`) and the restricted
  formula still needs `≥` its surviving‑relevance leaves, so `shrinkage_plus_surviving_relevance` gives
  `(surviving relevance)·D ≤ leaves` — the relevance base and the shrinkage schematic, tightly connected.

So the mini‑arc is closed: subfunction counting *provably* tops out at `n²/log n`; the non‑counting (relevance +
shrinkage) route *provably* exceeds it to `n^{3-o(1)}` — but that is still **polynomial**, vastly short of the
super‑polynomial explicit bound `P ≠ NP` would need.  The deep shrinkage theorem itself is cited, not reproved;
proving it is a separate project, and even with it the explicit frontier remains polynomial.

**The shape of the residue.** Space is exact; time cannot be reached by space machinery; decision hardness is
unconditional but non‑explicit; the explicit residue is exactly `InNP`; counting provably cannot supply it
(natural‑proofs barrier); and the strongest explicit, *non‑natural* bound reachable caps at `n²/log n`. The one
thing left unbeaten is precisely the part no current method touches: an explicit, non‑natural decision lower bound
**above the Nečiporuk frontier** — which is `P ≠ NP`.

## 4¾. The N‑Frame / Book‑1 CEW route, audited — and the contextual‑invariant dichotomy

The N‑Frame "Book 1" programme proposes to close the separation via a contextual‑entanglement‑width (CEW) / SPDP
route.  It is fully formalized (`…Book1CEWRoute`) as the obligation structure `Book1CEWSPDPEpistemicBoundaryPort`,
whose four fields are Book 1's pillars — **(A1)** every poly‑time SAT decider has polylog CEW; **(A2)** polylog
CEW ⇒ poly SPDP rank; **(A3)** the hard family has super‑poly SPDP rank; **(A4)** a decider transports the hard
rank into its P‑side rank — and these **assemble into the separation** (`no_DTMDecidesSATWithEncoding_of_book1CEWSPDP`
⇒ `standardPvsNP_of_book1CEWSPDP`).  So "A1–A4 ⇒ `P ≠ NP`" is a theorem; the whole content is in the fields.

**A1 is the live wall (`…NFrameBook1Audit`).**  A2 is a proved counting lemma, A3 the calibrated Tseitin/Ramanujan
bound, A4 a transport certificate; **A1** — bounded contextual width for *all* of `P` — is the only `P ≠ NP`‑strength
field, and in `…Book1CEWRoute` it is discharged *only* by a **syntactic** log‑window surrogate
(`book1LogSyntacticPCEW`), explicitly flagged as not a claim about arbitrary deciders.  The audit pins this to
proved theorems: `naive_time_cew_bound_false` (no function of the time bound alone bounds the observer action —
from `action_unbounded_by_time`); `space_bound_does_supply_A1` (a *space* bound does, via `subcritical_of_lowspace`
— the working surrogate is always space/contextual, never time‑only); `correct_decider_escapes_boundary_A1` (a
*correct* full‑boundary decider exists, so "every decider has low boundary" is false even semantically — CEW must
be strictly finer than boundary).

**The contextual‑invariant dichotomy — both horns proved.**  A1 asks for a contextual invariant that is
**bounded for `P`** *and* **super‑polynomial on the hard family**.  We define both natural unweighted forms and
prove neither can be both at once:

* **Additive horn (`…TimeContextualWidth`).**  `tcw = ∑_{τ<T} log₂(contextWidth (views τ))` — cumulative
  contextual log‑width, tied to the *realized image* at each step (so it dodges `action_unbounded_by_time`, which
  the raw action did not).  `tcw_le_steps_mul_bits` (`tcw ≤ T·n`) and `tcw_A1_bounded_for_polyTime`
  (`≤ n^{k+1}` for `T ≤ n^k`) make **A1 a theorem** — bounded contextual width for *all* of `P`.  But
  `additive_tcw_below_superpoly_threshold` proves the price: being additive, `tcw` is capped at `T·n` = poly, so
  at infinitely many lengths *every* poly‑time observer (any correct SAT decider included) has `tcw` strictly
  below the super‑poly threshold `n^{log₂ n/4}` — **A3 is provably false** for it.
* **Multiplicative / rank horn (`…RankContextualWidth`).**  `crank M = ` #distinct rows of the past/future cut
  matrix — a genuine rank/communication quantity, super‑additive across the cut.  `crank_cube_full`
  (`crank(equality matrix) = 2^a`) and `crank_unbounded` (`∀ N, ∃ a, N < crank`) make **A3 reachable** — the
  super‑poly half the additive horn lacked.  But `rank_space_bound_tight` proves the price: the only bound the
  budget yields is `crank ≤ 2^{space}`, and it is **tight**; a poly‑*time* observer has only poly *space*, so its
  rank ceiling is `2^{poly}` — exponential, not poly, and achievable — so **A1 does not follow from the budget**.
  Raw rank fails A1 even more sharply: linear‑time functions (inner‑product, equality) already have *full* rank
  `2^{n/2}`, so raw `crank` is in `P` at the top of its range.

| invariant | shape | A1 (bounded for `P`) | A3 (super‑poly on hard family) |
|---|---|---|---|
| `tcw` (additive) | `∑ log width` | **provable** (`≤ T·n`) | **provably false** (capped at `T·n`) |
| `crank` (multiplicative) | `#distinct rows` | **the wall** (only `≤ 2^{space}`, tight; false for raw rank) | **provable** (`= 2^a`, unbounded) |

So an *unweighted* contextual invariant is provably either too small to separate (additive) or achieved by easy
functions and bounded only by space (multiplicative).  A1 can hold *and* A3 hold only for a rank that is low
**because of the time structure** — a *projected* SPDP rank where the poly‑time presentation forces the projection
low.  That projection is exactly Book 1's A2/A1 bridge, which the corpus audit (`…NFrameHypercubeConstraint`)
already found **assumed, not derived** — the one irreducible `P ≠ NP`‑strength step.  The dichotomy is *proved*,
not asserted: it converts "you would need a finer invariant" into a machine‑checked no‑go on both natural forms.

**The projected‑rank arc — and its closing verdict (`…ProjectedContextualRank` → `…AffineIndicatorCollapse`).**
The dichotomy left exactly one opening: a *projection* `proj : (row) → R` that collapses easy high‑rank rows but
preserves hard ones.  This was made a concrete target and then probed to its conclusion:

* **The certificate framework** (`…ProjectedContextualRank`): `pcrank proj M = ` #distinct projected rows.  Sanity
  laws proved — `pcrank_le_crank`, `pcrank_id_eq_crank`, `pcrank_le_of_factor` (a richer projection only raises
  rank), `pcrank_eq_crank_of_injOn` (rank survives an injective projection), `pcrank_ge_of_injOn` (A3‑survival
  certificate).  A1 becomes a checkable certificate: `BoundedRangeProjection` ⇒ poly `pcrank`, and
  `boundedRange_cannot_be_separating` proves the cheap (small‑codomain) A1 is fatal to A3.  The isolated target:
  `SeparatingProjection` — and `separatingProjection_forces_selective` proves any solution must *merge* easy rows
  yet stay injective on hard rows (distinguish hardness from easiness at the row‑vector level).
* **Two concrete projections, calibrated.**  *Low‑degree* (`…LowDegreeProjection`): the row's restriction to
  low‑Hamming‑weight inputs.  It collapses the easy equality matrix to poly (`lowDegProj_eqMatrix_le`) and escapes
  the deathtrap (feature space `2^{poly}`).  *SPDP* (`…SPDPFeatureProjection`): the order‑`≤k` discrete
  derivatives on low‑weight inputs.  `spdp_refines_lowDeg` proves SPDP **dominates** low‑degree (the `S=∅`
  coordinate *is* the value), so it preserves at least as many rows — the strictly stronger candidate.
* **The A3 probes.**  On the *linear* core (`…SPDPHardSurvivalProbe`, the inner‑product/parity matrix) SPDP
  **survives** — `spdp_ipMatrix_survives` gives full rank `2^a` — but so does low‑degree (`ipMatrix` is degree 1,
  and is in `P`), so this separates nothing.  The decisive test is the *high‑degree* affine‑indicator residual
  (`…AffineIndicatorCollapse`): rows `= {v : v|_P = s}` (degree `|P|`), raw rank `2^{|P|}` (super‑poly).
* **The closing verdict — locality kills it (`…AffineIndicatorCollapse`).**  `spdpProj_zero_of_vanishing`:
  **SPDP at constant order `(k,d)` only ever evaluates a row on the weight‑`≤(k+d)` ball** — it is a *local*
  probe.  So `spdp_constraintMatrix_collapse` gives `pcrank (spdpProj a k d) ≤ N(|P|, k+d)+1` = **poly** while the
  raw rank is `2^{|P|}`: **SPDP collapses the high‑degree affine / Tseitin‑style residual to polynomial rank, just
  as low‑degree does** (`lowDeg_constraintMatrix_collapse`).  The locality/feature‑count tension is the
  quantitative shadow of the SPDP‑rank barrier: a *bounded*‑order feature map is too local to separate
  high‑codimension residuals, and making the order scale with the codimension (`k+d = Ω(distance)`) blows the
  feature space to `2^{super‑poly}`, breaking A1's poly feature‑count.  **A projected rank with a *fixed* feature
  order is ruled out** — the surviving live direction is precisely a projection whose order scales with the
  instance, which is the SPDP‑rank lower‑bound program itself (the barriered `P ≠ NP`‑strength step).  Net: the
  one opening the dichotomy left is closed for every *fixed*‑order projection, by a proved locality no‑go.

**The scaling‑order arc — chasing the one surviving opening to a single named bridge.**  The fixed‑order no‑go
left exactly one route: let the projection order *scale*.  Three amplifiers were tried and the Gödel‑hierarchy
tower built; all converge on one theorem.

* **Expander amplification (`…ExpanderAmplificationBoundary`).**  Can a Ramanujan/expander layer rescue survival?
  `highDistance_spdp_collapse`: if every accepting input has weight `≥ Δ` (the expansion distance) and the probe
  order `k+d < Δ`, then `pcrank ≤ 1` — coupling many high‑distance copies amplifies the *zero* feature, so the
  collapse becomes **total**.  An expander amplifies *visibility, not invisibility*.  `lowDeg_full_order_eq_crank`
  (at radius `a`, `pcrank = crank`) marks the other end: the rank turns on only once the radius crosses `Δ`.
* **PAC operations (`…PACProjectionBoundary`).**  The `p vs np1` PAC layer helps two real ways —
  `pac_postProjection_nonincrease` (PAC restrictions are rank‑non‑increasing: P‑side A1 control) and the
  positive‑minor geometry (A3 side) — but `pacRelabel_spdp_collapse` proves a local PAC relabelling (weight blowup
  `≤ c`) only rescales the visibility radius by `c`, so a high‑distance residual still collapses when `c·(k+d)<Δ`.
  `pacPositiveMinorSurvival_needs_scaling`: a surviving positive minor (`s ≥ 2`) *forces* `Δ ≤ k+d`.  PAC's only
  opening is scaling order.
* **The Gödel hierarchy tower (`…GodelHierarchySPDPScaling`).**  Book 1's Gödel hierarchy = an *ascending*
  projection tower `levelProj L`, `godelLevel n = (log₂ n, log₂ n)`.  `levelProj_monotone` (proved): higher levels
  see at least as much (lower‑level features are coordinates of higher).  `levelProj_full_radius_eq_crank`
  (proved): at the top of the tower `pcrank = crank` — full visibility.  So the tower provably does what fixed
  SPDP could not: **visibility rises with level**, and a high enough level sees the hard residuals.
* **But the feature budget is vacuous at the scaling level (`…GodelFeatureCount`).**  `godel_feature_bound_vacuous`:
  the only generic bound is `pcrank ≤ 2^{count}`, and `godel_feature_count_superlinear` proves `count > n/2` at the
  Gödel level (`count ≥ 2^{log₂ n}`, `n < 2·2^{log₂ n}`).  So the ceiling is `2^{>n/2}` — **exponential, no better
  than the trivial `crank`**.  A polynomial A1 therefore **cannot** come from bounding the *size* of the feature
  space; it must come from poly‑time *structure* forcing few *realized* features.  A1 is provably **not a counting
  fact**.

The whole arc converges on one statement, named in `…GodelHierarchySPDPScaling`: **`PolyTimeLowGodelSPDP`** — at
the Gödel‑scaled level, every poly‑time observer's *realized* pcrank is polynomial, while the hard family's is
super‑polynomial (`HardFamilyHighGodelSPDP`); `godelSPDP_no_shared_rank` proves these are incompatible, so the
pair *is* the separation.  This is the **`ScalingSPDPBridge`**: order `≥` distance (to see the hard residual) with
*realized* feature count polynomial for `P` (to bound it) — exactly the barriered SPDP‑rank lower bound, and the
single irreducible `P ≠ NP`‑strength step the entire projected/scaling‑rank programme reduces to.

**ACC⁰ calibration — the method's credibility test (`…ACC0DynamicSPDPCalibration` → `…ACC0Composition`).**
*Diagnostic, explicitly necessary‑not‑sufficient: `NP ⊄ ACC⁰` is strictly weaker than `P ≠ NP` (`ACC⁰ ⊊ P/poly`),
and even Williams only has `NEXP ⊄ ACC⁰`.*  ACC⁰ is where AC⁰[p] (Razborov–Smolensky, handled) meets the
mixed‑moduli wall, so it tests whether dynamic‑SPDP has teeth.  A modular gate is a function of a few **weight
statistics**; `statRow_realized_le` proves a class of statistic‑rows whose reachable statistics lie in a set `R`
has `≤ 2^{|R|}` realized features.  Consequences, all proved:

* **single modulus is tame** — `godel_symmetric_realized_poly`: one statistic (total weight) gives `≤ 2n`
  realized features at the Gödel level — *polynomial*.  The framework explains AC⁰[p]/single‑modulus cleanly.
* **`k` moduli cost `2^{(d+1)^k}`** — `kStat_realized_le`: `k=1` poly, `k=2` quasi‑poly (`2^{O(log² n)}`),
  growing `k` super‑poly.
* **composition drives `k` to the gate count** — `…ACC0Composition`: a depth‑2 circuit of `m` modular gates
  factors through the combined `m`‑tuple statistic (`composed_realized_le`, `≤ 2^{(d+1)^m}`), and
  `composed_budget_ge_double_exp` gives `2^{2^m} ≤ 2^{(d+1)^m}` — doubly exponential in the gate count.

So the reach is sharp and matches the AC⁰[p] → ACC⁰ frontier exactly: **counting statistics works for one gate and
is vacuous for composed ACC⁰** (the budget leaves polynomial at the first mixed‑modulus stacking).  An A1 bound for
the full class (`ACC0LowRealizedGodelSPDP`, named) **cannot come from counting** — it needs the genuine
Razborov–Smolensky / correlation structure, the open `NP ⊄ ACC⁰`‑strength content.  The calibration *locates* that
obstruction precisely (the number of independent moduli the projection must jointly resolve); it proves no new
lower bound, and clearing ACC⁰ would still be a waypoint below `P ≠ NP`, not the separation.

**The naturalness range — why dynamic‑SPDP reaches ACC⁰ but provably not `P ≠ NP` (`…DynamicSPDPNaturalnessRange`).**
Dynamic‑SPDP is a *feature‑counting* method, so its lower‑bound certificate ("`f` has high realized features" =
`f` is `Hard` for the low‑feature class) is a **natural property** — large, useful, constructive.  The
Razborov–Rudich barrier we already formalized (`…NaturalProofsBarrier`) is *class‑dependent* (`Crypto` = the class
contains PRFs):

* `dynamicSPDP_certificate_large` / `dynamicSPDP_certificate_useful` — the certificate is natural (reuses the
  barrier file's `counting_property_is_large`, `hard_property_useful`).
* `dynamicSPDP_blocked_of_crypto` — `Crypto` (PRFs, e.g. `P/poly`) ⇒ the barrier derives `False` from a
  constructive certificate: **dynamic‑SPDP cannot reach `P ≠ NP`**, by the very barrier we proved.
* `dynamicSPDP_unblocked_of_no_crypto` — `¬ Crypto` (no PRFs, e.g. ACC⁰) ⇒ the barrier is *vacuous*: a natural
  lower bound is **permitted**.
* `dynamicSPDP_range_dichotomy` — the three together.

So the method's reach is **exactly the PRF‑free classes**: ACC⁰ is a legitimate, un‑barriered avenue (the
composition theorem is worth attempting, via a natural/algebraic route distinct from Williams' non‑natural
algorithmic method), while `P/poly`/`P ≠ NP` is *blocked by the same barrier* — capped precisely where PRFs
appear.  "Stronger than Williams" is plausible only at the ACC⁰ level, and is provably not a path to the
separation.

**The holonomy arc — a global cycle detector that sees what local SPDP missed, fully characterized
(`…HypergraphHolonomySPDP` → `…HolonomyPSideControl` → `…HolonomyBoundedCycleRank` → `…HolonomyCompositionRank` →
`…HolonomyEffectiveRank` → `…HolonomyHardEffectiveRank`).**  Within the un‑barriered ACC⁰ avenue, the most promising
invariant: not a local Hamming‑ball probe but a *cycle‑obstruction* one.  On a Tseitin constraint graph the
**holonomy of a cycle `C`** is the `F₂` sum of vertex charges around it, `⊕_{v∈C} charge(v)` — zero for a
satisfiable charge, nonzero exactly when the cycle is globally inconsistent.

* **Hard side (`…HypergraphHolonomySPDP`).**  `cycleHolonomy_singleton` — a single charge on a cycle gives
  *nontrivial* holonomy: the obstruction is **visible at Hamming weight 1**, the regime where the affine‑indicator
  collapse killed local SPDP.  `holonomy_realizes_all` — `m` disjoint cycles realize **all `2^m` holonomy
  signatures** (`holonomy_zero_charge` gives the trivial/satisfiable collapse).  This is the first invariant in
  the arc that does what fixed SPDP could not — a genuine global‑cycle detector, not renamed geometry.
* **The linear asset (`…HolonomyPSideControl`).**  `holSigZ_add` / `holSigZ_zero` — over `F₂` holonomy is a
  **linear** map of the charge, so the realized signatures form a *subspace* and the class count is `2^{rank}`,
  governed by the **cycle rank** rather than the gate count.  `holonomy_acyclic_trivial` (no cycles ⇒ 1 class) and
  `holonomy_classes_le_of_generators` (`k` generators ⇒ `≤ 2^k`) bracket it.
* **Tame side, provable (`…HolonomyBoundedCycleRank`).**  `holonomy_classes_le_of_basis` — **cycle rank `≤ r` ⇒
  `≤ 2^r` holonomy classes**, for any charge family, independent of `m`/gate count; `holonomy_classes_le_of_few_distinct`
  proves the factoring concretely (`m` cycles from `r` distinct basis cycles).  So bounded‑treewidth/planar
  constraint graphs (cycle rank `O(\log n)`/`O(1)`) are *provably tame* (poly/constant classes), expanders
  (`Ω(n)`) hit `2^{Ω(n)}` — conditional only on a **graph property**, not a complexity assumption (not a socket).
* **Composition — rank is subadditive (`…HolonomyCompositionRank`).**  `holonomy_classes_submultiplicative`
  (`#classes(A ⊞ B) ≤ #classes(A)·#classes(B)`) and `holonomy_rank_subadditive` (`2^{rₐ}·2^{r_b} ⇒ 2^{rₐ+r_b}`):
  composing `k` sources of rank `≤ s` gives `≤ 2^{k·s}` — exponent **linear** in `k`, versus the feature budget's
  `2^{(d+1)^k}` (exponent *exponential* in `k`).  The genuine quantitative advantage over feature‑counting.
* **Effective rank of *realized* charges, two‑sided (`…HolonomyEffectiveRank`, `…HolonomyHardEffectiveRank`).**
  The right object is not the raw graph's cycle rank but the rank the circuit's *actual* charges span.
  `realized_le_of_factorThroughStat` + `modular_layer_realized_le` — a `k`‑gate modular layer's realized charges
  factor through `k` statistics ⇒ `≤ q^k` classes (effective rank `≤ k·log₂ q`, *additive*): the AC⁰[p] success in
  holonomy form.  `expander_realizedClasses_eq` — the matching lower bound: the charged expander gadget realizes
  the full `2^m` classes (effective rank `= m`).

So the holonomy invariant is now **fully characterized, both ends proved on the same object** (`realizedClasses`):
tame computations (low statistic count) → low effective rank `≤ k·log₂ q`; the Tseitin/expander family → full
effective rank `= m`.  It genuinely does what fixed SPDP could not — weight‑1 visibility, linear `2^{rank}` control,
*additive* composition — and it cleanly separates tame from hard.  The one missing implication is exactly
**poly‑time ⇒ low *effective* cycle rank on hard instances** (= `ACC0LowRealizedGodelSPDP`), which is *false* for
the raw constraint graph (an ACC⁰ circuit can encode an expander) so it is genuinely about the *realized* charges;
it is the open `NP ⊄ ACC⁰`‑strength step, and the PRF‑free naturalness ceiling
(`…DynamicSPDPNaturalnessRange`) caps even that below `P ≠ NP`.

**The direct bridge attempt, and the exact wall (`…ACC0BridgeAttempt`).**  Attacking the bridge head‑on yields a
genuine *restricted* lower bound, not the separation: `effectiveRank_gate_lower_bound` — a `MOD q` circuit whose
realized charges have effective rank `≥ m` and factor through `k` modular statistics needs `2^m ≤ q^k`, i.e.
`k ≥ m/log₂ q` gates (so the expander charge family needs `≥ m/log₂ q` modular gates).  `logGate_bridge_holds` —
the bridge *holds* for `O(log n)`‑gate circuits (`≤ n^q` classes, poly).  `polyGate_counting_bound_ge_two_pow` —
the wall: at poly gates the counting bound is `q^n ≥ 2^n`, vacuous.  The attempt stops at two precise barriers:
(i) **model gap** — it bounds charge *realization*, not language *decision*; (ii) **the log→poly gate jump** — the
method proves tameness only for `O(log n)` gates.  Either way it does not reach `NP ⊄ ACC⁰`, and even if it did
the naturalness ceiling caps it below `P ≠ NP`.

**The restriction / switching surrogate — proved for the fragment, named for general ACC⁰
(`…ACCHolonomyRestriction`, `…FragmentSwitching`).**  The sharpest two‑sided formulation of what an ACC⁰ lower
bound needs, with one side proved.  *Hard side, proved:* `tseitin_holonomy_survives_restriction` — a restriction
leaving `K` cycles free preserves all `2^{|K|}` holonomy classes (Tseitin/expander holonomy is robust under
restriction).  *Tame side, the switching surrogate, proved for the modular‑statistic fragment:*
`restriction_lowers_effective_holonomy_rank` — a restriction fixing `k − j` statistics leaves the charge factoring
through `j` free ones, so `realizedClasses ≤ q^j` and `q^j < q^k` (the rank bound strictly drops).  Combined,
`fragment_below_surviving_tseitin`: when `q^j < 2^{|K|}` the fragment realizes *strictly fewer* classes than the
hard family retains — a genuine fragment‑level lower bound, the switching mechanism (restriction lowers the
circuit, Tseitin survives) closing end‑to‑end **on the fragment**.  *The open core:* the same surrogate for
*poly‑gate* ACC⁰ — `ACC0LowEffectiveHolonomyRank` (`acc0_holonomy_separation` is the conditional it feeds) —
fails to generalize for a precise reason: a poly‑gate ACC⁰ circuit need not factor through few statistics, and a
restriction need not reduce its statistic count (it can encode an expander).  That exact hypothesis is
`NP ⊄ ACC⁰`‑strength, still under the naturalness ceiling.  So the mechanism is *correct and complete on the
fragment*; extending it to poly‑gate ACC⁰ is the major missing theorem, not a gap in the surrogate.

**The rank‑lowering rung‑ladder — climbing fragments toward ACC⁰, with the wall exposed.**  Following the route of
proving rank lowering for ever‑richer fragments (rather than ACC⁰ directly), four rungs are proved, each
*deriving* the rank drop from circuit structure:

| rung | why incidence / statistic count is controlled | file |
|---|---|---|
| modular‑statistic | restriction fixes `k − j` statistics directly (`restriction_lowers_effective_holonomy_rank`) | `…FragmentSwitching` |
| read‑once (disjoint supports) | fixing a gate's whole support makes it constant (`gate_constant`); free gates `{i ∉ T}` give `q^{#free}` (`readonce_restriction_lowers_rank`) | `…ACCRankLoweringTarget` |
| bounded overlap (incidence `≤ d`) | `#free gates ≤ d · #free vars` (`bounded_overlap_free_gates_le`), so `q^{d·u}` (`bounded_overlap_restriction_lowers_rank`) | `…BoundedOverlapRankLowering` |
| bounded‑depth tree (no re‑use) | `incid v t ≤ depth t + 1` (`incid_le_depth`) ⇒ incidence `≤ D+1` ⇒ the bounded‑overlap bound with `d = D+1` | `…BoundedDepthTreeRung` |

Climbing exposes the **common mechanism**: every rung relies on a restriction fixing some gate's *whole support*,
making it constant, which drops the realized statistic count; each rung supplies a different reason the incidence
(hence surviving‑gate count) stays controlled — disjointness → bounded incidence → bounded depth.  And it
characterizes the **wall** exactly: *poly‑gate ACC⁰ with unbounded re‑use defeats that hook* — a single variable
can feed unboundedly many gates, so a restriction need not fix any gate's whole support, no gate need become
constant, and the statistic count need not drop (the circuit can stay fully live, encoding an expander).  That is
`ACCRestrictionLowersEffectiveRank` (`…ACCRankLoweringTarget`), `NP ⊄ ACC⁰`‑strength, under the naturalness
ceiling.  Bounded *re‑use* (`≤ r` gates per variable) is already covered (it is bounded incidence with `d = r`);
the genuinely‑open case is *unbounded* re‑use — the wall itself.  The ladder climbs exactly as far as the
whole‑support‑fixing mechanism reaches, and names where it stops.

**The reuse boundary — the route's terminus (`…ACCReuseSwitchingTarget`).**  Pushing one step past the ladder
confirms it is genuinely exhausted, with the negative outcome proved.  `restricted_rank_le_two_pow_free` — a
*fully general* rank lowering surviving arbitrary re‑use: after any restriction leaving `u` free variables the
restricted charge depends only on those coordinates, so `realizedClasses ≤ 2^u` for **any** circuit
(`override_eq_extend`).  So restrictions do lower rank despite reuse — but to the **circuit‑independent** bound
`2^{#free vars}`, which *cannot separate*: it is tight (the expander achieves it, `expander_realizedClasses_eq`),
so a restriction leaving `u` free variables lowers **both** the circuit and the hard family to `≤ 2^u` — no gap.
The whole‑support hook gave a *circuit‑specific* drop (`q^{#free gates} ≪ 2^{#free vars}`) that beat the hard
family; unbounded re‑use kills it, leaving only the non‑discriminating generic bound.  A separation therefore
needs a *circuit‑specific* drop under reuse — `RandomRestrictionLowersEffectiveRankDespiteReuse`, the named target
— which is Håstad‑shrinkage / Razborov–Smolensky‑correlation content, `NP ⊄ ACC⁰`‑strength under the naturalness
ceiling.  **The counting / restriction family of mechanisms is now provably exhausted for this purpose**; the next
move is the Williams / correlation mechanism, not another rung.

So this exploration is **closed as a characterized invariant**: the strongest the arc produced, separating tame
from hard, with the single remaining bridge named precisely and proved to lie beyond the method's reach — not
bridged, and honestly not bridgeable here.  (Adjacent and also closed: the explicit‑Nečiporuk frontier — the
corpus's arc reaches the `n²/log n` method ceiling, and `…NeciporukCeiling` formalizes *why* subfunction counting
cannot exceed it — `log₂ #subfunctions ≤ min(2^b, n-b)` per block — so super‑`n²/log n` explicit bounds require a
different method, shrinkage/Andreev, not this one.)

### 4¾.bis  The correlation / Williams mechanism — opened, with the engine and the fragment test proved

The reuse boundary closed the *counting / restriction* family; the named successor was the **correlation /
Williams** mechanism (non‑natural, evading the Razborov–Rudich barrier that caps the rank route).  That mechanism
is now **opened and tested**, not merely named.

**The frontier and the cash‑out shape (`…ACCWilliamsCorrelationTarget`).**  `class_agreement_le_majority` — a
predictor with a fixed value on a class agrees with the target on at most that class's *majority*
(`max(#true,#false)`); summed over a coarse predictor's few classes, a balanced target is matched only `≈ ½`.
`acc0_williams_cashout` — the algorithmic‑method skeleton `smallACC0 → fastSat → collapse`, so `¬collapse ⇒
¬smallACC0` (no axioms); the hard `smallACC0 → fastSat` step (Williams' fast ACC⁰‑SAT algorithm) is a named,
*non‑natural* hypothesis.  Open target named: `ACC0CorrelationAgainstTseitin`.

**The engine — measure bias, not class count (`…HolonomyCorrelationEngine`).**  This is the genuinely new object.
`agreement_le_sum_majority` — **the correlation bridge**: a class‑constant predictor `g∘π` agrees with `f` on `≤`
the sum over its classes of the per‑class majority of `f`.  `low_rank_predictor_low_correlation_with_full_holonomy`
— **the seed**: if `f` is *balanced on every predictor class*, then `2·agreement ≤ #inputs` — the predictor
correlates `≈ ½`, **no advantage**.  Correlation is forced by the predictor's *coarseness*, not by counting
functions — the route the naturalness barrier does not cap.  The open input was *balance‑per‑class*.

**The first real test — balance for restricted predictors (`…HolonomyBalanceFragments`), proved.**  Balance is now
*discharged* for restricted predictors against the genuine holonomy/parity target `fParity D x = ⊕_{i∈D} x i`.
Mechanism: a **missed parity variable**.  `balanced_per_class_of_involution` — a class‑preserving,
target‑flipping involution forces per‑class balance (it swaps `f=true` with `f=false` inside each class).  The
involution is `flipAt v` (flip an *unread* coordinate `v∈D`): `factorsThrough_flipAt` (a predictor that ignores
`v` is flip‑invariant) + `fParity_flipAt_mem` (flipping `v∈D` toggles the parity, via `parityCharge_flipAt_mem`
and the `ZMod 2` toggle).  Hence `parity_balanced_of_missed_var`, and `parity_balanced_of_card_gap` (pigeonhole:
`#read set < #parity support ⇒` a missed variable).  Combined with the seed:
`restricted_fragment_low_correlation` — **a predictor reading fewer variables than the holonomy parity spans has no
correlation advantage against it** (`2·agreement ≤ #inputs`).  The three named fragments each supply the read‑set
bound from their gate structure: `logGate_predictor_classes_balanced` (gate‑count × fan‑in), `readOnce_…`
(disjoint supports ⇒ `∑|supp|`), `boundedOverlap_…` (direct read‑set bound).  All clean axioms
(`[propext, Classical.choice, Quot.sound]`), no `sorry`.

**The honest finding.**  At the *rank* level the three fragments were genuinely distinct (incidence drove distinct
`q^{·}` bounds).  At the *correlation* level they **collapse to one condition** — does the read set miss a parity
variable? — and the overlap parameter that mattered for rank is *irrelevant* to balance.  A real structural
observation, not a gap.

**Where it stops (`ACC0ApproximatesByLowRankPredictors`, named open).**  This bites *restricted* predictors whose
read set is provably smaller than the parity support.  A general poly‑size ACC⁰ circuit reads *all* `n` variables,
so no single unread coordinate exists — balance via a fixed flipped coordinate fails, and one needs an
*approximate* low‑dimensional predictor (ACC⁰ ≈ a coarse holonomy predictor up to a `½−ε` deficit).  That bridge,
fed into `restricted_fragment_low_correlation` + `acc0_williams_cashout`, would give `NP ⊄ ACC⁰` — and is itself
`NP ⊄ ACC⁰`‑strength under the PRF‑free naturalness ceiling.  So the correlation route is **opened and proved on
fragments**; the load‑bearing ACC⁰‑approximation step is named and lies (as expected) at the same wall.

**The bridge tested explicitly on a `MOD q` gate (`…ModQGateBalance`).**  Running the smallest genuine
all‑variable ACC⁰ gate confirms the engine's prediction *precisely*.  A `MOD q` gate is the cleanest low‑rank
predictor — it factors through the count statistic `modQStat q x = (∑_i x_i) ∈ ZMod q` (`q` classes) — but it
reads every variable, so the missed‑variable involution `flipAt v` breaks: one flip changes the count by `±1` and
leaves the `MOD q` class.  **What survives is a count‑preserving *pair* swap** `pairSwap v w` (flip `v∈D` and a
witness `w∉D` together): on the off‑diagonal `{x_v ≠ x_w}` it preserves the count *exactly*
(`modQStat_pairSwap_offdiag`: one coordinate `0→1`, the other `1→0`) and toggles the parity (`fParity_pairSwap`),
so `balanced_per_class_of_involution` gives **exact per‑class balance off‑diagonal** (`modQ_class_balanced_offdiagonal`,
`offdiag_balanced`) and hence **no `MOD q`‑gate correlation advantage against the holonomy parity on the
off‑diagonal** (`modQ_gate_low_correlation_offdiagonal`: `2·agreement ≤ #off‑diagonal inputs`).  All clean axioms,
no `sorry`.  **The residual is exactly the diagonal** `{x_v = x_w}` (there the pair swap changes the count by `±2`
and leaves the class) — and this is now a *theorem*, not an observation: `modQ_class_imbalance_on_diagonal` proves
the full‑class holonomy‑parity imbalance **equals** the diagonal imbalance (split each class off/diagonal via
`card_eq_offdiag_add_diag`; the off‑diagonal part is exactly balanced via `balanced_of_involution`, so it cancels).
That diagonal residual is the classical `MOD q`‑vs‑parity correlation, exponentially small in `n−|D|` by a
Fourier/character recursion but *not* by any involution (`ModQParityCorrelationExpSmall`, named open).  So the
approximate bridge **partly survives** — a count‑preserving symmetry recovers exact balance on the symmetric part,
and *localizes* the entire deficit to the diagonal — and the irreducible remainder is, once again, the same
Razborov–Smolensky‑flavoured `NP ⊄ ACC⁰`‑strength estimate.

**Attacking the diagonal recursively settles the modulus split.**  Pushing the recursion onto the diagonal answers
the closing question — involutive bound or character sum? — with *it depends on `q`*.  On the diagonal the only
count‑preserving parity‑toggling move is the flip‑both involution `pairSwap v w` (which keeps `x_v=x_w` and changes
the count by `±2`).  **For `q = 2` that `±2` is `0`**, so `modQStat_two_pairSwap` preserves the `MOD 2` count
*unconditionally*, the diagonal is balanced (`modQ2_diagonal_balanced`), and combined with the localization the
recursion **closes**: `modQ2_class_balanced` / `modQ2_gate_zero_correlation` prove a `MOD 2` gate has **exactly
zero** correlation advantage against *any* holonomy parity over `D ⊊` variables, over *all* inputs, fully by
involution (no character sum, no `sorry`, clean axioms).  **For `q > 2`** the `±2` is nonzero mod `q`, the diagonal
involution is blocked, and only there does the genuine character‑sum residual remain
(`ModQParityCorrelationExpSmall`, now scoped to `q > 2`).  So the involution method reaches *all the way* at the
modulus `2` (an exact RS‑style zero‑correlation theorem, proved) and bottoms out only for higher moduli — a clean,
honest delineation of exactly where the elementary method stops.

**Disjoint pair stacking extends the recursion to `q > 2` (`imbalance_localize_step`, `imbalance_stacked`).**  The
single‑pair flip‑both is blocked for `q > 2` only on the *diagonal*; a *fresh disjoint* pair `(v_i ∈ D, w_i ∉ D)`
(all coordinates distinct from earlier pairs) flips one‑up / one‑down on its own off‑diagonal — count change `0`
mod **any** `q` — and leaves the earlier pairs' coordinates untouched, so it peels another exactly‑balanced layer.
Proved (clean, all `q`, by induction over a `Nodup`‑coordinate list of pairs): `imbalance_stacked` —
**the holonomy‑parity imbalance of a `MOD q` class equals that of its `k`‑fold diagonal** `⋂_{i≤k} {x_{v_i} =
x_{w_i}}`.  So even for `q > 2` involution does real work: it shrinks the imbalance‑carrying support pair by pair
(general step `imbalance_localize_step` parameterised by any ambient set closed under the flip‑both on its
off‑diagonal).  The recursion runs until no fresh disjoint `(in‑D, out‑D)` pair remains — `min(|D|, n−|D|)` steps —
and only that final core is the irreducible character sum.  Net delineation: **modulus `2` is fully involutive;
higher moduli are involutive down to a shrinking diagonal core**, the character sum required only on the core.

**The shrinkage becomes a numeric bound (`flipAt_card_eq_ne`, `diag_card_mul`, `imbalance_stacked_bound`).**  Each
disjoint equality constraint *halves the cube* — flipping a fresh coordinate `v` is a bijection between
`{x_v = x_w}` and `{x_v ≠ x_w}` (`flipAt_card_eq_ne`) — so the `k`‑fold diagonal has size exactly `2^{n-k}`
(`diag_card_mul`: `2^{|L|} · #(k‑fold diagonal) = 2^n`, proved by induction).  Since the imbalance equals the
`k`‑fold‑diagonal imbalance (`imbalance_stacked`) and any set's imbalance is bounded by its size,
`imbalance_stacked_bound` gives — for **all `q`**, clean, no `sorry` — the two‑sided bound
`|#{parity=true} − #{parity=false}| ≤ 2^{n-k}` on a `MOD q` class, with `k` the number of disjoint stacked pairs
(`k ≤ min(|D|, n−|D|)`).  This is a **genuine involutive exponential bound** on the `MOD q`‑vs‑parity correlation,
exp‑small whenever `min(|D|, n−|D|)` is large — the elementary method's quantitative reach, made explicit, with the
sharper `|cos(π/q)|^{n-|D|}` character estimate needed only to push past it on the residual core.

**Composition: two (and many) gates (`…TwoGateCorrelation`).**  The first mixed‑moduli ACC⁰ composition test.  The
general engine `balanced_offdiag_of_pres` / `low_correlation_of_pres` proves: *any* predictor `π` preserved by the
off‑diagonal flip‑both has exact off‑diagonal balance and no correlation advantage against the holonomy parity.
Two cases of the composition question:
- **Full‑support gates (any number, mixed moduli) compose freely.**  The off‑diagonal flip‑both moves one
  coordinate `0→1` and the other `1→0`, preserving the *integer weight* `∑_i x_i` exactly — hence every statistic
  factoring through it (`MOD q_j` for all `j`, threshold, exact‑count) at once.  `twoStat_pairSwap_offdiag` /
  `twoGate_low_correlation_offdiagonal`: the *single* involution `pairSwap v w` handles both gates, so mixed
  moduli are no obstacle.
- **Different supports give the product‑class obstruction.**  For supports `A, B` the swap must preserve both
  support‑counts: `weightOn_pairSwap_eq` shows `∑_S x` is preserved by the flip‑both **iff `v, w` lie on the same
  side of `S`**.  So a usable `D`‑witness pair needs `v ∈ D`, `w ∉ D` *and* `v, w` in a common cell of the
  partition `{A∩B, A∖B, B∖A, (A∪B)ᶜ}` — `twoGateOn_offdiag_balanced` (balance under `v∈A↔w∈A`, `v∈B↔w∈B`).  Same
  support collapses the cell conditions to one; full support makes them automatic; disjoint / bounded‑overlap
  supports turn finding witnesses into a **matching / flow problem** — the composition version of the engine, and
  `NP ⊄ ACC⁰`‑strength once the supports are adversarial.

**Many gates: the cell‑covering obstruction, made precise (`…ManyGateCorrelation`).**  For `k` gates with supports
`S₁,…,S_k`, the **cell** of a coordinate is its membership pattern `(v∈S₁,…,v∈S_k)`; the flip‑both preserves every
support‑count (hence every `MOD q_j`, any moduli) **iff `v,w` share a cell** (`SameCell`), so the `k`‑gate weight
vector is preserved (`weightVec_pairSwap`).  Proved: `kGate_offdiag_balanced` / `kGate_low_correlation_offdiagonal`
— a same‑cell `D`‑witness pair `(v∈D, w∉D)` gives exact off‑diagonal balance and no correlation advantage for *any*
gate function of the `k` statistics.  The frontier is then a clean **covering characterization**
(`cellWitness_iff_not_respects`): a witness exists *iff* `D` does **not** respect the cell partition (is not a union
of cells).  Two regimes: coarse supports (few gates → few cells) leave most `D` crossing a cell, so the engine
bites; but if the supports **shatter** `Fin n` into singleton cells (`respectsCells_of_separating`: separating
supports ⇒ *every* `D` respects the cells ⇒ no witness), the involution engine has nothing to act on.  Shattering
needs `≥ ⌈log₂ n⌉` independent modular statistics — so the elementary involution method survives exactly until an
ACC⁰ predictor reads enough gates to separate the coordinates, at which point composition becomes the
matching/shattering wall, `NP ⊄ ACC⁰`‑strength.  This pins where the correlation engine stops: not at a modulus,
not at two gates, but at the point where the gates' cells refine past the holonomy support's structure.

**The pigeonhole converse makes the `log₂ n` threshold a theorem (`…ManyGateCorrelation`).**  The cell map
`v ↦ (v∈S₁,…,v∈S_k)` lands in `Bool^{Fin k}` (size `2^k`); if `2^k < n` it cannot be injective
(`Fintype.exists_ne_map_eq_of_card_lt`), so two distinct coordinates share a cell — `exists_sameCell_pair_of_card_lt`
— and the singleton of one of them is a holonomy support the engine bites on — `exists_cellWitness_of_card_lt`
(clean, `2^k < n ⇒ ∃ D, CellWitness`).  This is the exact converse of `respectsCells_of_separating` (which needs
the supports to *separate* every coordinate, i.e. `≥ ⌈log₂ n⌉` gates): **below `k = ⌈log₂ n⌉` the engine always has
a `D` to act on; at or above it the supports can shatter the coordinates and kill the involution.**  So the
elementary correlation engine's survival is pinned to a sharp gate‑count threshold — `k` vs `log₂ n` — turning
"few gates ⇒ engine bites" from intuition into a proved dividing line, and locating the ACC⁰ wall exactly where the
modular‑statistic count crosses `log₂ n`.

**Past the shattering wall: restriction collapses cells (`…ACCRandomRestrictionCellCollapse`).**  The route through
the `log₂ n` wall (switching‑lemma strategy): a restriction simplifies the supports so the live coordinates regain
large cells, after which the same‑cell witness machinery bites on the restricted instance.  The *combinatorial*
half is proved deterministically; the *probabilistic* half is named.  Cell‑collapse mechanism: if the supports are
**trivial on the live set `L`** (each support lies entirely in or out of `L`, `TrivialOn`), then *all* live
coordinates share one cell (`sameCell_of_trivialOn`), so any holonomy support `D` separating two live coordinates
is a witness (`cellWitness_of_trivialOn`) and the `k`‑gate predictor has no correlation advantage
(`collapse_gives_low_correlation`, via `kGate_low_correlation_offdiagonal`).  A concrete instance needing **no
probability**: if `⋃_j S_j` misses `≥ 2` coordinates (fan‑in too small to cover), those untouched coordinates share
the empty cell and the engine bites (`exists_cellWitness_of_small_union`).  The one open step is named:
`ACC0RestrictionCollapsesCells` (a small‑depth ACC⁰ family admits a trivializing restriction on `≥ 2` live
coordinates) — proving a *random* restriction achieves this is the Håstad / Razborov–Smolensky switching content,
`NP ⊄ ACC⁰`‑strength; granted it, `acc0_collapse_gives_cellWitness` discharges the rest (collapse ⇒ witness ⇒
engine bites again below the live‑variable threshold).  So route 2 stands in skeleton: the deterministic cell
combinatorics are fully proved, the single probabilistic switching step isolated and named.

**A *proved* deterministic switching instance — bounded fan‑in.**  On the bounded‑fan‑in fragment the named
hypothesis becomes a theorem.  The explicit, non‑random restriction is the simplest possible: **kill every touched
coordinate**, i.e. take the live set `L = (⋃_j S_j)ᶜ`.  Then every support is disjoint from `L`
(`trivialOn_compl_union`: `TrivialOn` holds via the all‑disjoint branch), and for fan‑in `≤ s` the live set is
large — `card_compl_union_ge`: `n − k·s ≤ |L|` (`card_biUnion_le` + `∑ s = k·s`).  Hence `boundedFanIn_collapsesCells`:
`|S_j| ≤ s` and `k·s + 2 ≤ n` ⇒ `ACC0RestrictionCollapsesCells` *outright*, no probability.  Chained end‑to‑end,
`boundedFanIn_cellWitness`: bounded fan‑in too small to cover the cube ⇒ the engine bites (a holonomy support the
predictor cannot correlate with).  This converts the switching hypothesis into a proved lemma for depth‑2 /
bounded‑fan‑in supports; the full probabilistic switching lemma is what remains to lift it to poly‑size ACC⁰
(fan‑in up to `n`, where `k·s ≫ n` and the deterministic "kill‑all‑touched" restriction leaves nothing live).

**The probabilistic half — first moment (`…ACCRestrictionSwitchingProb`).**  The genuinely probabilistic rung: keep
each coordinate live independently with probability `p` (a `p`‑biased random restriction, live set `L` with weight
`p^{|L|}(1-p)^{n-|L|}`).  Proved: `biased_sum_one` — the weights form a real distribution (binomial theorem via
`Finset.prod_add`); `survProb_le` — a support of fan‑in `m` is killed with probability `(1-p)^m`, hence survives
with probability `1-(1-p)^m ≤ m·p` (Bernoulli's inequality `one_add_mul_le_pow`); `expectedLive_eq` — expected live
coordinates `= n·p`; and the payoff `expectedSurviving_le` — **the expected number of surviving supports is `≤
k·s·p`**, shrinking linearly in `p`.  So heavy restrictions (small `p`) drive the expected surviving count below
`1`, forcing a support‑killing restriction to exist — the first‑moment skeleton of switching.  Honest scope: the
first moment alone reaches the same `k·s < n` regime as the deterministic restriction (keeping `≥ 2` live needs
`p ≥ 2/n`, and `k·s·p < 1` then needs `k·s < n/2`); beating it — a *constant* live fraction `p` while still
collapsing high‑fan‑in supports — needs the higher‑moment Håstad switching argument, the genuine
`NP ⊄ ACC⁰` content.  The random restriction is now modelled, its distribution validated, and the expected
surviving‑support count provably shrinks; the higher‑moment concentration is the remaining frontier.

**The probabilistic half — second moment (`…ACCRestrictionSwitchingVariance`).**  Chebyshev needs the variance.
For `X = ∑_j X_j` (surviving‑support count), the covariance of two survival indicators equals that of the kill
indicators, and kill events are "all coordinates dead": `cov_eq` —
`Cov(X_S, X_T) = (1-p)^{|S∪T|} − (1-p)^{|S|+|T|}`.  Proved: `cov_nonneg` (overlapping supports are *positively*
correlated, since `|S∪T| ≤ |S|+|T|` and `0 ≤ 1-p ≤ 1`); `cov_disjoint` (disjoint supports are *uncorrelated* —
independence, `|S∪T| = |S|+|T|`); `cov_self_le` (`Cov(X_S,X_S) = P(S kill)·P(S surv) ≤ P(S surv)`, an indicator's
variance `≤` its mean).  Hence the payoff `variance_disjoint_le` — **`Var[X] ≤ k·s·p` for pairwise‑disjoint
supports**: off‑diagonal covariances vanish, so `Var[X] = ∑_j Cov(X_j,X_j) ≤ ∑_j P(S_j surv) = E[X] ≤ k·s·p`.
This is the **Chebyshev input** (`P(|X−E[X]| ≥ t) ≤ Var/t²`) that upgrades "few survive in expectation" to "few
survive w.h.p." at constant `p` — the move beyond the first‑moment `k·s < n` regime, for disjoint supports.  For
*overlapping* supports `cov_nonneg` exposes the obstruction exactly: positive correlation inflates the variance,
and controlling that term is the higher‑moment Håstad switching content, `NP ⊄ ACC⁰`‑strength.  So the second
moment is computed in closed form, the disjoint case is Chebyshev‑ready, and the overlap term is the named
frontier.

**Bounded overlap: the variance bound past independence (`…ACCRestrictionSwitchingVariance`, cont.).**  The overlap
covariance is bounded by the intersection size: `cov_le` — `Cov(X_S, X_T) ≤ |S∩T|·p` (factor
`Cov = (1-p)^{|S∪T|}·(1−(1-p)^{|S∩T|})`, first factor `≤ 1`, second `≤ |S∩T|·p` by Bernoulli).  Then double counting
under **bounded overlap** (each coordinate in `≤ d` supports) gives `∑_{j,l}|S_j∩S_l| = ∑_v deg(v)² ≤ d·∑_v deg(v) =
d·∑_j|S_j| ≤ d·k·s` (proved per‑`j`: `∑_l|S_j∩S_l| = ∑_{v∈S_j} deg(v) ≤ d·|S_j| ≤ d·s`, via `card_filter` +
`sum_comm`).  Hence `variance_boundedOverlap_le` — **`Var[X] ≤ d·k·s·p`** when each coordinate lies in `≤ d`
supports (disjoint supports are the case `d = 1`, recovering `k·s·p`).  This is the genuine rung *past
independence*: the Chebyshev‑ready variance bound now holds for bounded‑overlap support families, with the overlap
degree `d` entering linearly.  Unbounded overlap (`d` up to `k`) is where the bound degrades to `k²sp` and the
higher‑moment Håstad argument is genuinely required — the precisely‑located `NP ⊄ ACC⁰` frontier.

**Chebyshev: the variance bound becomes a concentration statement (`…ACCSwitchingChebyshev`).**  The Markov and
Chebyshev inequalities are proved *over the exact `p`‑biased restriction measure* (`weight p L =
p^{|L|}(1-p)^{n-|L|}`, total `1` by `total`/`biased_sum_one`; `Pr`/`Exp` the weight of an event / average of a
function).  Proved: `markov` (`a·Pr(f ≥ a) ≤ Exp f` for `f ≥ 0`), `chebyshev`
(`Pr((g−Eg)² ≥ t²) ≤ Exp((g−Eg)²)/t²`, Markov on the squared deviation), and the packaging
`chebyshev_of_variance_le` (`Exp((g−Eg)² ) ≤ B ⇒ Pr((g−Eg)² ≥ t²) ≤ B/t²`).  Taking `g = X` the surviving‑support
count, `Exp((X−EX)²) = Var[X] ≤ d·k·s·p` (the second‑moment bound) gives **`Pr(|X − E[X]| ≥ t) ≤ d·k·s·p / t²`** —
so a constant‑`p` random restriction leaves few surviving supports *with high probability*, the concentration that
turns first‑moment existence into a robust restriction (for bounded‑overlap supports).  This completes the
switching skeleton's probabilistic packaging: the concentration inequalities are proved in full over the genuine
measure; the only remaining inputs are the (proved) variance bound and its routine identification with
`Exp((X−EX)²)`.  Unbounded overlap remains the higher‑moment frontier.

**The end‑to‑end pipeline, assembled (`…ACCSwitchingPipeline`).**  The whole random‑restriction programme is chained
into one conditional theorem with the single higher‑moment gap isolated.  Proved: `exists_of_pr_lt_one` (the
probabilistic method over the `p`‑biased measure — an event of probability `< 1` has a complementary outcome, from
`total`); `exists_low_survival` (**a low‑survival restriction exists** — by Markov, expected survivors `≤ B < a` ⇒
some restriction leaves `< a` surviving supports); `cellWitness_gives_low_correlation` (**a same‑cell `D`‑witness
defeats the predictor** — `2·agreement ≤ #off‑diagonal`, via `kGate_low_correlation_offdiagonal`).  The assembly
`bounded_overlap_acc0_low_correlation_whp` chains them: from the expected‑survivor bound (`hE`, the first‑moment
value `≤ k·s·p`) a low‑survival restriction exists; the cell bridge (`hbridge`: few survivors ⇒ same‑cell witness —
the second‑moment/pigeonhole collapse, proved for bounded overlap, the higher‑moment frontier for unbounded) turns
it into a `CellWitness`; the witness defeats the bounded‑overlap ACC⁰ predictor.  So **every link of the pipeline is
proved except the single named cell bridge**, and the theorem makes the full
"bounded‑overlap ACC⁰ predictor fails on the holonomy parity under a random restriction" argument explicit, with
the genuine `NP ⊄ ACC⁰` hardness localized to exactly one combinatorial step (unbounded‑overlap cell collapse).

**The cell bridge proved via pigeonhole (`…ACCSwitchingPipeline`, cont.).**  The named gap `hbridge` is now
*discharged* by pigeonhole, with the key observation that a *live* coordinate cannot belong to a *killed* support
(it would witness non‑disjointness), so a live coordinate's cell pattern is determined entirely by the **surviving**
supports — at most `2^{#survivors}` patterns, not `2^k`.  Proved: `exists_sameCell_pair_of_survivors`
(`2^{#survivors} < |L| ⇒` a same‑cell live pair, via `exists_ne_map_eq_of_card_lt_of_maps_to` mapping `v ↦ {j : v∈S_j}`
into the powerset of the surviving set, card `2^{#survivors}`); `exists_cellWitness_of_survivors`
(`⇒ ∃ D, CellWitness`, taking `D` the singleton of one of the pair); and `predictor_fails_of_survivors`
(`2^{#survivors} < |L| ⇒ ∃ D, the k‑gate ACC⁰ predictor cannot correlate with the holonomy parity D`, with **no extra
hypothesis**).  So for a restriction whose surviving‑support count is below `log₂` of its live‑coordinate count, the
predictor *provably* fails — the bridge is closed by pigeonhole.  The probabilistic half (`exists_low_survival`)
delivers few survivors; the dual first moment (`E[#live] = n·p`) keeps the live count large; together they place a
restriction in this regime for bounded overlap.  The genuine remaining hardness is only the joint
**few‑survivors‑and‑many‑live** control at unbounded overlap (where the survivor count can reach `~log₂|L|`) — the
higher‑moment Håstad frontier, now isolated to that single quantitative tension.

**The joint tension closed by a union bound (`…ACCSwitchingPipeline`, cont.).**  The two tails are combined.  Proved:
`Pr_union_le` (union bound over the `p`‑biased measure, `Pr(E₁∨E₂) ≤ Pr E₁ + Pr E₂`, via `sum_filter` +
`split_ifs`); `exists_both_of_pr_add_lt_one` (if the two tail probabilities sum to `< 1`, some restriction avoids
*both* bad events — joint existence from the probabilistic method); and `bounded_overlap_predictor_fails_whp` — **if
the "too many survivors" tail (`≥ a`) and the "too few live" tail (`≤ b`) sum to `< 1` and `2^a ≤ b`, then a random
restriction defeats the bounded‑overlap ACC⁰ predictor** (`∃ D`, no correlation advantage), with *no cell‑bridge
hypothesis*: the joint restriction has `survivors < a` and `live > b`, so `2^{survivors} < 2^a ≤ b < live`, and
`predictor_fails_of_survivors` fires.  The two tails are Markov‑controlled by the first moments (`E[#surviving] ≤
k·s·p`, `E[#live] = n·p`); the feasibility `< 1` *is* the joint few‑survivors‑and‑many‑live condition.  So the
predictor failure is reduced to a single feasibility inequality, attainable for bounded overlap — and the precise
quantitative tension (survivor count reaching `~log₂` of the live count) at unbounded overlap is the residual
higher‑moment Håstad frontier.  The whole pipeline — moments, concentration, pigeonhole cell bridge, union‑bound
joint control — is now machine‑checked end to end, with the genuine `NP ⊄ ACC⁰` hardness isolated to that one
feasibility tension.

**An actual circuit class, with support extraction (`…ACC0CircuitModel`).**  The machinery now speaks about real
circuits, not abstract support families.  Defined: `ACC0Circuit` (the target class — AND/OR/NOT over `MOD q` gates,
with `depth` and `size`); `ModGate`, `Depth2ModCircuit` (the depth‑2 `MOD`‑bottom fragment) and its `supports`
family.  Proved: `eval_factors` — **support extraction**: a depth‑2 `MOD`‑bottom circuit's output factors through
its bottom statistics, `eval x = g (weightVec supports x)` for an explicit `g` (by `rfl`, axioms `[propext,
Quot.sound]` only); and `depth2_circuit_fails_of_survivors` — **the bridge**: such a circuit fails to correlate with
the holonomy parity after any restriction whose surviving‑support count is below `log₂` of its live count
(support extraction `+` the pigeonhole cell bridge).  So the proved lower‑bound machine now attaches to a named
circuit class: *bounded‑overlap depth‑2 `MOD`‑bottom ACC⁰ circuits fail to correlate with holonomy parity after a
suitable random restriction.*  The remaining wall is precisely located: lifting past depth 2 needs the
depth‑reduction switching (random restrictions collapsing AND/OR layers to `MOD`‑bottom survivors), and lifting
past bounded overlap is the higher‑moment Håstad tension — together, **unbounded support reuse / high‑overlap
depth‑reduction**, which is exactly where full ACC⁰ difficulty lives.

### Summary of the restricted ACC⁰ lower‑bound machine

The complete proved arc, attached to a real circuit class, with the honest remaining wall:

| stage | proved content | file |
|---|---|---|
| target | holonomy parity `fParity D` on the hypercube | `…HolonomyBalanceFragments` |
| engine | `MOD q` / many‑gate correlation via count‑preserving involutions | `…ModQGateBalance`, `…TwoGateCorrelation`, `…ManyGateCorrelation` |
| threshold | cells shatter iff `≥ ⌈log₂ n⌉` gates (pigeonhole + converse) | `…ManyGateCorrelation` |
| restriction | `p`‑biased measure; first moment `E≤k·s·p`, second `Var≤d·k·s·p`; Markov/Chebyshev | `…SwitchingProb`, `…SwitchingVariance`, `…SwitchingChebyshev` |
| cell bridge | `2^{survivors} < |L| ⇒` witness (killed supports blind to live coords) | `…ACCSwitchingPipeline` |
| joint control | union bound: few survivors ∧ many live ⇒ predictor fails | `…ACCSwitchingPipeline` |
| circuit class | `ACC0Circuit`; support extraction; depth‑2 `MOD`‑bottom bridge | `…ACC0CircuitModel` |
| depth reduction | locality (any depth); MOD‑support extraction; depth‑2 transfer bridge | `…ACC0DepthReduction` |
| high‑overlap probe | star family: core blowup `Var ≤ ksp + k²·\|core\|·p`; core surgery | `…ACCOverlapStar` |
| spread‑overlap probe | design `Var ≤ ksp + k²λp`; surgery cost `= \|overlapCoords\|`; star ⊆ core | `…ACCOverlapDesign` |
| core decomposition | killing `overlapCoords` ⇒ pairwise‑disjoint restricted family, `Var ≤ ksp` | `…ACCCoreDecomposition` |
| restriction tree | recursive depth `d → 2` descent (one‑step switching named) | `…ACCRestrictionTree` |
| Williams cash‑out | whole arc as one conditional: no small ACC⁰ predictor correlates | `…ACCWilliamsCashout` |
| depth-3 switch step | *real* deterministic switch on CNF-of-`MOD`: forced clause drops | `…ACCDepth3Switch` |
| Williams `NEXP ⊄ ACC⁰` scaffold | algorithmic‑method cash‑out; N‑frame route (speedup bridge named) | `…WilliamsNEXP_ACC0` |
| N‑frame ACC⁰‑SAT kernel | SAT collapses to a `weightVec`‑image (cell) search via support extraction | `…NFrameACC0Speedup` |
| ACC⁰‑SAT time-cost model | cell search `≤ (n+1)^k < 2^n` (small-gate regime): beats brute force | `…ACC0SatTimeCost` |
| branched ACC⁰‑SAT bound | `2^{killed}·(n+1)^r < 2^n` (few-survivor regime): past small-gate | `…ACC0SatBranched` |
| ACC⁰‑SAT time model | `cellSearch` algorithm: decides SAT, `steps` = #cells, `< 2^n` proved | `…ACC0SatMachine` |
| operational step machine | `step`/`runFor` interpreter: decides SAT in `#cells` transitions, `< 2^n` | `…ACC0SatStepMachine` |
| elementary op count | `totalOps = k·#cells ≤ k·(n+1)^k < 2^n`: every gate‑eval counted | `…ACC0SatOpCount` |
| survivor → cell count | `#cells ≤ (n+1)^{#active}`: speedup governed by active (surviving) gates | `…ACC0SatSurvivorCells` |
| speedup capstone | few survivors ⇒ correct, sub‑`2^n` SAT decider (correctness ∧ time) | `…ACC0SatSpeedupCapstone` |
| restriction ⇒ active | `#active(S·∩L) = survivingCount`; `#cells ≤ (n+1)^{surviving}` | `…ACC0SatRestrictionActive` |
| branch correctness | `SAT ↔ ∃ branch, branchSAT` (the branch‑and‑restrict decomposition) | `…ACC0SatBranchCorrect` |
| master bridge | `NFrameGivesACC0SatSpeedup`: whole pipeline, one socket (few survivors) | `…NFrameACC0Master` |
| socket reduction | `socket_of_expectation`: `Exp(survivingCount) ≤ r` + `(n+1)^r < 2^n` ⇒ the socket | `…ACC0SatSocketReduction` |
| first moment / regime | `prDisjoint`: `Pr(S∩L=∅)=(1-p)^{|S|}`; `Exp(survivingCount)=∑survProb≤ksp`; `socket_of_regime`: `ksp ≤ r` + `(n+1)^r < 2^n` ⇒ the socket | `…ACC0SatFirstMoment` |
| second moment / concentration | `Exp((survivingCount−E)²)=variance`; `survivingCount_concentration`: `Pr(\|X−E\|"≥"t)≤dksp/t²`; `most_restrictions_good`: most restrictions within `t` of mean | `…ACC0SatSecondMoment` |
| exponential tail (independent) | factorial moment `Pr(t≤X)≤Exp(C(X,t))=∑_{\|T\|=t}Pr(all T survive)`; kill+survival independence (disjoint); `exp_tail_disjoint`: `Pr(t≤X)≤C(k,t)(sp)^t` | `…ACC0SatExpTail` |
| **clause‑count‑free switching tail** | `pweight_total`: `∑pweight=1`; **`hastad_switching_prob_tail`: `∑_{Bad}pweight ≤ (4pw/(1-p))^s`** (depth‑`≥s` mass, NO clause‑count factor), reconstruction discharged by `reconstructionCorrect_fullpath` | `…Depth3SwitchingProbTail` |
| depth reduction whp | **`depth_collapse_mass_ge`: `{depth<s}` carries mass `≥ 1−(4pw/(1-p))^s`** (complement of the tail) — width‑`w` DNF collapses to depth‑`≤2` whp | `…Depth3SwitchingDepthReduction` |
| cross‑model bridge (NO‑GO) | `modQStatOn_flip_ne`: MOD statistic fully sensitive (`q≥2`); **`mod_gate_parity_nonconstant`**: parity gate non‑constant on any cube with a free support coord ⇒ switching (leaves coords free) CANNOT drive `switch_step` (needs full support) — the Razborov–Smolensky wall | `…ACCSwitchingModBridge` |
| **PIVOT → polynomial method** | road‑map: switching capped, MOD no‑go proved, RS layer already complete; next = effective‑dimension/correlation fusion | `ACC_ROADMAP.md` |
| N‑frame target = parity (RS bridge) | `fParity_univ_eq_parity`: holonomy target = `decide(Odd #ones)`; **`nframe_parity_target_size_lower_bound`**: N‑frame target needs `2^{Ω(n^{1/2d})}` AC⁰[p] size (inherits the proved RS bound) | `…Layer3NFrameParityRS` |
| **socket 1: eff‑dim ↔ holonomy fusion** | top‑frequency functional kills `V_D`, separates parity; **`holonomy_parity_not_lowDegEval`**: holonomy target `∏pmOne` ∉ degree‑`≤D` span for `D<n` (eff‑dim `≥n`). Per‑class engine genuinely does NOT fuse (parity determined, never balanced) | `…Layer3LowDegHolonomy` |
| **socket 2: ACC⁰ ≈ low‑rank predictors** | `eval_mem_lowDegSpan`: degree‑`≤D` poly's cube‑eval ∈ `V_D` (multilinear reduction); **`acc0_approx_by_lowRankPredictor`**: AC⁰[p] circuit (`p^t≥4·#subcirc`) `3/4`‑approximated by a function in `V_D`, `D=((p-1)t)^depth` — same `V_D` socket 1's target escapes | `…Layer3ACC0LowRank` |
| **socket 3: modulus boundary (WALL)** | `fermat_indicator` (`1−a^{p−1}=1[a=0]`); **`modp_eval_mem_lowDegSpan`**: `MOD_p` detector exactly degree‑`(p−1)` over `F_p` (any fan‑in) ⇒ ∈ `V_{p−1}` — WHY `modulus=p` is load‑bearing. `MOD_q` (q≠p) / composite / `NEXP⊄ACC⁰` = algorithmic‑method frontier, NOT polynomial method (delimited, not faked) | `…Layer3ModulusBoundary` |
| **Tier 3 frontier: mixed modulus** | `fp_statistic_eq_count` (F_p stat = count mod p); **`mod6_eq_mod2_and_mod3`** (CRT: MOD_6 = MOD_2 ∧ MOD_3); `mod2/3_detector_lowdeg` (each component low‑degree over its OWN prime field — no common field). `MixedModulusStratifiedObserverSocket` = named OPEN target (hybrid observer; Williams arc, not RS). Consolidated map: `ACC_THEOREM_MAP.md` | `…Layer3MixedModulus` |

**Strongest proved statement.** *Bounded‑overlap depth‑2 `MOD`‑bottom ACC⁰ circuits fail to correlate with the
holonomy parity after a random restriction, under an explicit feasibility inequality* (`Pr(survivors ≥ a) +
Pr(live ≤ b) < 1` with `2^a ≤ b`).  **The one remaining wall:** unbounded support reuse / high‑overlap
depth‑reduction (the higher‑moment Håstad switching), where the survivor count can reach `~log₂` of the live count
and the two tails cannot both be driven below `1`.  Everything reachable by the moment method, pigeonhole, bounded‑
overlap double‑counting, and union bounds is proved sorry‑free with clean axioms; that single tension is the genuine
`NP ⊄ ACC⁰`‑strength residue.

**Depth reduction toward deeper circuits (`…ACC0DepthReduction`).**  The deterministic backbone for lifting past
depth 2 is proved: `support` and `eval_eq_of_agreeOn` (**locality** — a circuit of any depth reads only its
support, by induction); `eval_const_of_support_disjoint` (**killed ⇒ constant** — a subcircuit whose support is
disjoint from the live set is constant across live completions, the deterministic version of the collapse a
restriction produces); `modSupports` (**MOD‑support extraction** for arbitrary depth — the support family the
switching machinery acts on); and `reduction_bridge` (**transfer** — any circuit extensionally equal to a depth‑2
`MOD`‑bottom `C'` inherits `C'`'s correlation failure after a low‑survivor restriction).  The two layers of the
remaining wall are named as one property: `Depth2Reducible` (a circuit *is* extensionally depth‑2 `MOD`‑bottom) and
`HastadDepthReduction` (a poly‑size constant‑depth circuit, after a random restriction, becomes `Depth2Reducible`
with bounded‑overlap survivors).  Granted `HastadDepthReduction`, `reduction_bridge` discharges the rest — so the
**entire remaining `NP ⊄ ACC⁰` difficulty is isolated to that single named property**: the random restriction
simultaneously collapsing the AND/OR depth to a `MOD`‑bottom survivor *and* keeping its overlap bounded.

**The star family — a concrete miniature of the high‑overlap wall (`…ACCOverlapStar`).**  To see *where* high
overlap hurts, the star family `S_j = core ∪ petal_j` (shared `core`, pairwise‑disjoint `petals`) concentrates all
overlap in the core: `star_inter` proves `S_i ∩ S_j = core` for `i ≠ j`.  Consequences, all proved: `star_cov_le`
(`Cov(X_{S_i}, X_{S_j}) ≤ |core|·p` off‑diagonal) and `star_variance_le` — **`Var[X] ≤ k·s·p + k²·|core|·p`**, the
*quadratic‑in‑`k`* core blowup that the second moment cannot absorb when `|core|` is large (the miniature of the
higher‑moment wall).  But `core_surgery` shows it is **removable by a restriction**: with the core dead (disjoint
from the live set), every live coordinate lies in *at most one* star support — overlap collapses to `1`, so the
disjoint pipeline (`Var ≤ k·s·p`) fires.  **Verdict: for star families high overlap is bad only while the shared
core stays live**; a depth‑reduction restriction that kills the core defeats it.  This locates the genuine wall
precisely — it is *not* concentrated‑in‑a‑small‑core overlap (solvable by core surgery) but overlap that no small
killed set can disjointify, which is where the real Håstad difficulty lives.

**The spread‑overlap probe — the genuine Håstad regime (`…ACCOverlapDesign`).**  Testing the real enemy: a *design
family* with bounded but spread pairwise intersections.  The decisive finding, all proved: `design_variance_le`
gives `Var[X] ≤ k·s·p + k²·λ·p` under `|S_i ∩ S_j| ≤ λ` — **the same bound shape as the star**, so the second
moment *cannot* distinguish concentrated from spread overlap.  What separates them is the **surgery cost**, the size
of `overlapCoords = {v : v lies in ≥ 2 supports}`: `disjointify_requires_kill` proves any live set on which the
supports are disjoint must have *every* overlap coordinate dead (`Disjoint overlapCoords L`), so
`card_overlapCoords_le_compl` gives `|overlapCoords| ≤ #dead` — disjointifying costs killing `≥ |overlapCoords|`
coordinates.  And `star_overlapCoords_subset_core` proves the star is the small‑`overlapCoords` case
(`overlapCoords ⊆ core`), surgically removable; a spread design with *large* `overlapCoords` is not — killing few
coordinates cannot disjointify, and killing many destroys the live set the cell bridge needs.  **Net: the variance
bound does not see the wall; the explicit quantity that does is `|overlapCoords|`.**  The remaining `NP ⊄ ACC⁰`
difficulty is now pinned to one concrete object — a support family with *small pairwise intersections yet large
`overlapCoords`* (spread overlap) — exactly the Håstad regime, where no small killed set disjointifies.

**Core decomposition — the dichotomy made sharp (`…ACCCoreDecomposition`).**  The star surgery generalizes to
*every* family.  The canonical core is `overlapCoords`, and: `kill_overlap_gives_disjointOnLive` (converse of
`disjointify_requires_kill`) gives the exact characterization `disjointOnLive supports L ↔ Disjoint (overlapCoords)
L` (`disjointOnLive_iff`); `restricted_pairwise_disjoint` proves that after killing the core the restricted family
`supports j ∩ L` is *genuinely pairwise disjoint*; and `core_decomposition_variance` then gives the *clean disjoint
bound* `Var[X] ≤ k·s·p` for the restricted family — **the `k²·λ` overlap term is gone**.  So the surgery cost to
remove all overlap is exactly `|overlapCoords|`, and the dichotomy is sharp: **`|overlapCoords|` small ⇒ cheap to
kill ⇒ reduces to disjoint (`Var ≤ ksp`, the easy case, e.g. the star); `|overlapCoords|` large ⇒ no small kill
disjointifies (the hard spread/Håstad case).**  The entire remaining `NP ⊄ ACC⁰` difficulty is now pinned to one
explicit cardinality — `|overlapCoords|` of the bottom‑gate support family — and the whole easy side of the
dichotomy is proved sorry‑free.

**The restriction tree — recursive depth reduction (`…ACCRestrictionTree`).**  The deterministic descent toward the
depth‑2 bridge is mechanized.  A restriction is a partial assignment `ρ : Fin n → Option Bool` (`Agrees` = input
respects ρ's fixings); restrictions accumulate as a *list* with `AgreesAll` the conjunction, so composing steps is
list concatenation.  The one‑step Håstad step is named `RestrictionTreeSwitch` (every depth‑`≥3` circuit, under some
restriction, equals a strictly‑smaller‑depth circuit on agreeing inputs).  Proved: `reduces_to_depth2` —
**granted one‑step switching, every circuit reduces to a depth‑`≤2` circuit** over an accumulated restriction list
(`AgreesAll ρs x → eval C x = eval C' x`, `depth C' ≤ 2`), by well‑founded recursion on depth (axioms `[propext,
Quot.sound]` only — constructive).  Each step strictly decreases depth, so iteration terminates at `2`; the
depth‑2 survivor then feeds the depth‑2 `MOD`‑bottom bridge and the correlation/pigeonhole machinery.  So the entire
depth‑reduction *structure* — the restriction tree's descent — is mechanized; the lone unproved input is the single
per‑layer switching `RestrictionTreeSwitch`, the Håstad lemma.

**The Williams cash‑out — the whole arc as one conditional (`…ACCWilliamsCashout`).**  The programme is assembled
into a single top‑level theorem in the contrapositive (Williams) shape.  `williams_correlation_cashout` proves: a
small ACC⁰ predictor correlating with the holonomy parity ⇒ (`reduces_to_depth2`) it reduces to a depth‑`≤2`
survivor ⇒ that survivor fails to correlate (`hfail`, the proved support‑extraction + pigeonhole machinery) ⇒ by
transfer of correlation under restriction (`htransfer`), contradiction — hence **no small ACC⁰ predictor correlates
with the holonomy parity**, conditional on the named gaps.  The cash‑out *logic* is fully proved (axioms `[propext,
Quot.sound]`, driven by the proved descent); the load‑bearing inputs are exactly the two `NP ⊄ ACC⁰`‑strength walls
— the per‑layer Håstad switching `RestrictionTreeSwitch` and the subcube‑transfer `htransfer` — plus the proved
survivor‑failure machinery (`hfail`).  So the entire reduction is now **one explicit theorem with the irreducible
difficulty isolated to those named hypotheses**, the honest culmination of the restricted ACC⁰ lower‑bound machine.

**A real switching step, deterministically (`…ACCDepth3Switch`).**  One concrete instance of the
`RestrictionTreeSwitch` wall is now *discharged with no probabilistic hypothesis*, on a depth-3 fragment: a
**CNF of `MOD` gates** (AND of clauses, each clause an OR of `MOD` gates — depth 3 AND/OR/`MOD`).  Proved:
`modGate_eval_eq_of_agreeOn` (a `MOD` gate depends only on its support); `agree_on_fixed` (inputs respecting a
restriction that fixes `S` agree on `S`); `evalClause_true_of_mem` / `evalCNF_cons_of_clause_true` (a true disjunct
satisfies its clause, a satisfied clause drops from the AND); and `switch_step` — **the real switching atom**: if a
restriction fixes a gate `G ∈ c`'s support (bounded fan-in: `≤ s` coordinates) and forces `G` true, then on the
restricted cube `evalCNF (c :: cnf) = evalCNF cnf` — the clause drops.  All constructive (axioms `[propext,
Quot.sound]`).  Iterating it over the clauses reduces the CNF to depth `≤ 2`, feeding the depth-2 bridge.  So the
restriction tree's atom is **no longer assumed** — it is proved for this fragment via support fixing and `MOD`
locality; only the *simultaneous / with-high-probability* control (forcing one gate per clause at once while
keeping coordinates live) remains the named Håstad difficulty.

**Williams' `NEXP ⊄ ACC⁰` scaffold (`…WilliamsNEXP_ACC0`).**  `NEXP ⊄ ACC⁰` is a *theorem* (Williams 2011), so its
algorithmic‑method skeleton is mechanizable with the hard ingredients named.  Proved (pure logic, **no axioms**):
`acc0_sat_speedup_implies_NEXP_not_ACC0` — a nontrivial ACC⁰‑circuit‑SAT algorithm (`ACC0SatSpeedup`) together with
Williams' core implication (`williams`: speedup + `NEXP ⊆ ACC⁰` ⇒ nondeterministic‑hierarchy collapse) and the time
hierarchy (`hierarchy`: no collapse) gives `¬ NEXPHasACC0Circuits`, i.e. `NEXP ⊄ ACC⁰`.  And `nframe_williams_cashout`
— the N‑frame route: *if* the holonomy/correlation structure yields the speedup (`NFrameGivesACC0SatSpeedup` via a
named `bridge`), then `NEXP ⊄ ACC⁰`.  **Honest scope:** this is the *scaffold* of a known theorem — the implication
structure, mechanized — conditional on the two real inputs (`williams`/`ACC0SatSpeedup` = Williams' SAT‑speedup
algorithm; `hierarchy` = the nondeterministic time hierarchy).  The N‑frame supplies the geometric route and the
hard target, but **not** the SAT speedup itself: proving `NFrameGivesACC0SatSpeedup` (N‑frame ⇒ nontrivial
ACC⁰‑SAT) is the genuine open Williams bridge.  It does not prove `NP ⊄ ACC⁰` or `P ≠ NP`; it states exactly which
known inputs close `NEXP ⊄ ACC⁰` and where the N‑frame machinery would attach.

**The N‑frame → ACC⁰‑SAT speedup kernel (`…NFrameACC0Speedup`).**  The structural half of the open Williams bridge
(`NFrameGivesACC0SatSpeedup`) is discharged honestly.  Proved: `sat_iff_image` — a predicate factoring through a
statistic is satisfiable iff some *achieved* statistic value is accepted (search the image, not the domain); and
`sat_depth2_reduces` — **a depth‑2 `MOD`‑bottom circuit's satisfiability reduces to a search over its `weightVec`
image** (via the proved support extraction `eval_factors`).  So SAT over the `2^n` cube collapses to a search over
the cell/residue space of the bottom support family — whose size is the speedup parameter (`≤ 2^{#surviving}` after
a low‑survivor restriction, far below `2^{#live}`).  This is the N‑frame's genuine contribution to the SAT speedup,
powered by the corpus's support‑extraction and cell/survivor analysis.  **Honest scope:** this is the *search‑space
collapse* half only; converting it to a `2^{n − n^ε}` *time bound* (restriction‑tree branching over killed
coordinates + a time model) is the named algorithmic gap — the genuine Williams content.  So
`NFrameGivesACC0SatSpeedup` is *partially* discharged (structural kernel proved; time accounting named), and the
companion boundary/action speedup (`…NFrameSpeedupBridge`: `action < 2^n ⇒` beats brute force) gives the dual,
DP‑based form.  Nothing here proves `NEXP ⊄ ACC⁰`, `NP ⊄ ACC⁰`, or `P ≠ NP`.

**A time-cost model for the ACC⁰‑SAT speedup (`…ACC0SatTimeCost`).**  The structural kernel becomes a genuine
*model-relative time bound*.  In the natural cost model where deciding SAT means enumerating the achievable cells,
the cost is `|image(weightVec)|`, and: `weightVec_le` (each cell coordinate `≤ n`) + `imageSearchCost_le`
(`|image(weightVec)| ≤ (n+1)^k` — the cell vectors live in `(Fin k → {0,…,n})`) + `imageSearch_beats_bruteforce`
(`(n+1)^k < 2^n ⇒ |image| < 2^n`) give `nframe_acc0_sat_timebound` — **a depth‑2 `MOD`‑bottom circuit's SAT is
decided by a cell search of cost `< 2^n` in the small‑gate regime** (`k = o(n/log n)`).  All proved
(`Fintype.piFinset` cardinality + `card_le_card`).  **Honest scope:** this is a *search‑count* model (cost = cells
enumerated, the dominant term), and the regime `(n+1)^k < 2^n` is where the single base‑case search alone beats
brute force, *no branching*.  For larger gate counts one branches over killed coordinates (restriction tree),
giving `2^{#killed} ·` cell‑cost with the survivor count the parameter — that combination is the remaining named
accounting toward the full `2^{n−n^ε}` bound.  So the speedup is now a *real model‑relative time bound* in the
small‑gate regime; it is **not** the full ACC⁰‑SAT theorem, and proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**The branched bound — past the small‑gate regime (`…ACC0SatBranched`).**  The unbranched bound needed few *gates*;
branching needs only few *survivors*.  Branch over a killed coordinate set; on each branch the killed gates are
constant (locality, `eval_const_of_support_disjoint`), so the per‑branch cell search is over the survivor count `r`,
not `k`.  Proved: `branched_cost_le` (branched cost `≤ 2^{#killed}·(n+1)^r`, via `imageSearchCost_le` on the
survivor family); `branched_regime` (the arithmetic: `#killed + #live = n` and `(n+1)^r < 2^{#live}` ⇒
`2^{#killed}·(n+1)^r < 2^n`, via `mul_lt_mul_of_pos_left` + `pow_add`); and `branched_beats_bruteforce` — **the
branched cell search beats brute force in the few‑survivor regime**.  Since the restriction tree / core
decomposition is exactly what makes `r` small, this extends the model‑relative time bound *past* the small‑gate
`(n+1)^k` regime to the few‑survivor regime.  **Honest scope:** still the cell‑search model; the branch enumeration
correctness (SAT = OR over the `2^{#killed}` branches) is the standard branch‑and‑restrict decomposition (the cost
interpretation), and survivor‑constancy per branch is the proved locality.  Not a full Turing‑machine
`2^{n−n^ε}` analysis; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**A minimal time-complexity model (`…ACC0SatMachine`).**  The abstract cell cost becomes a *real timed algorithm*.
A `TimedDecision` is a result paired with a step count; `cellSearch C` enumerates the achievable cells, checks
`cellPredicate` on each, and accepts if any does, with `steps` = the number of cells examined.  Proved:
`eval_eq_cellPredicate` (the circuit value at `x` is `cellPredicate` at its cell, by `rfl` — support extraction at
the value level); `decideSAT_correct` (**the algorithm decides SAT**: `(cellSearch C).result = true ↔ Satisfiable
C.eval`); `cellSearch_steps_eq_checks` (**`steps` is the operation count** — equals the length of the enumerated cell
list); and `cellSearch_steps_le` / `cellSearch_beats_bruteforce` (**the time bound in the model**: `steps ≤ (n+1)^k`,
and `< 2^n` in the small-gate regime).  So "time" is now the step count of a defined algorithm whose correctness is
proved — closing the gap from "abstract cell cost" to "machine time" *for this cost model*.  **Honest scope:** a
unit‑cost cell‑check model (one step per cell, each check `O(k)`), not a Turing‑machine simulation; `cellSearch` is
`noncomputable` only because the enumeration order is choice‑supplied (irrelevant to result/steps).  Still not the
full `2^{n−n^ε}` ACC⁰‑SAT theorem; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**An operational step machine (`…ACC0SatStepMachine`).**  The `steps` field becomes the transition count of a real
interpreter.  A `MachineState` is `(acc, todo)`; `step` consumes one cell, OR‑ing its `cellPredicate` into `acc`;
`runFor t` runs `t` steps.  Proved: `foldl_or_eq_any` (OR‑accumulation `= List.any`); `runFor_length` (running
`#todo` steps drains the list and folds the accumulator); `machine_decides` — **the machine computes SAT**: after
`#cells` steps its `acc` is `true` iff the circuit is satisfiable; and `machine_steps_le` / `machine_beats_bruteforce`
— **the machine halts in `≤ (n+1)^k` steps, `< 2^n` in the small‑gate regime**.  So "time" is now the number of
`step` transitions of a defined machine with proved correctness — operational, not a field.  **Honest scope:** a
*list‑processing step machine* (one cell per transition), **not** a Turing machine with tape/head/input encoding,
and no `n^ε` accounting; it grounds machine time for the cell‑search cost model.  The full Turing‑machine
`2^{n-n^ε}` ACC⁰‑SAT analysis remains the named gap (the genuine Williams content).  Proves nothing about
`NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**The faithful elementary‑operation count (`…ACC0SatOpCount`).**  The finest the cell‑search cost model goes:
checking a cell evaluates `k` gate residues, so the true elementary operation count is
`totalOps = k·#cells = k·|image(weightVec)|`.  Proved: `totalOps_eq_gates_mul_steps` (`= k·(cellSearch steps)`);
`totalOps_le` (`≤ k·(n+1)^k`); `totalOps_beats_bruteforce` (`k·(n+1)^k < 2^n ⇒ totalOps < 2^n`).  So *every*
elementary gate‑residue operation is counted and the total is sub‑`2^n` for `k = o(n/log n)`.  This is the endpoint
of the operational‑cost refinement: a real algorithm whose every elementary op is counted and proved below brute
force in the small‑gate regime.  The full Turing‑machine model (tape/head/input encoding + the genuine
`2^{n-n^ε}` ACC⁰‑SAT algorithm) is the remaining Williams content — a research‑grade complexity formalization beyond
this corpus.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Survivor → cell count: the speedup tied back to the core machinery (`…ACC0SatSurvivorCells`).**  The cell bound is
refined from *all* `k` gates to the **active** (non-empty) gates.  An empty support gives a constant‑`0` `weightVec`
coordinate (`weightVec_eq_zero_of_empty`), so the cell vector is determined by its active coordinates; proved
`image_card_le_active` — **`|image(weightVec)| ≤ (n+1)^{#active}`** (an `InjOn` of the cell image into
`(active → {0..n})` plus `Fintype.piFinset` cardinality), hence `cells_le_active` (`cellSearch` steps
`≤ (n+1)^{#active}`).  After a restriction the killed gates become empty on the live set, so `#active = #surviving`
— the *same* survivor parameter the correlation/restriction machinery (`…ACCSwitchingPipeline`,
`…ACCCoreDecomposition`) controls.  So the SAT‑speedup is now **directly tied back to the survivor machinery**:
*few survivors ⇒ few active gates ⇒ few cells ⇒ fast search* (`(n+1)^{#surviving}`), closing the loop between the
speedup and the core correlation analysis.  A real, completable theorem; still the cell‑search model, not the full
Turing‑machine `2^{n-n^ε}` analysis, and proving nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Capstone: the survivor‑parameterized speedup (`…ACC0SatSpeedupCapstone`).**  The whole sub‑arc folds into one
statement.  `survivor_sat_speedup` — **if `(n+1)^{#active} < 2^n`, then `cellSearch C` correctly decides SAT *and*
runs in `< 2^n` steps** (correctness `∧` time bound, combining `decideSAT_correct` with `cells_le_active`).  Since
`#active = #surviving` after a restriction, this is exactly *few surviving gates ⇒ a correct SAT decision below
brute force*, driven directly by the survivor machinery (`…ACCSwitchingPipeline`, `…ACCCoreDecomposition`,
`…ACCRestrictionTree`).  This is the headline of the cell‑search speedup, in the parameter the corpus controls — a
real, correct, timed algorithm beating brute force when few gates survive.  Still the cell‑search model, not the
full Turing‑machine `2^{n-n^ε}` theorem; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Restriction ⇒ active, branch correctness, and the master bridge (`…ACC0SatRestrictionActive`,
`…ACC0SatBranchCorrect`, `…NFrameACC0Master`).**  Three moves finish assembling the N‑frame → ACC⁰‑SAT speedup.
*(i) Restriction ⇒ active:* after restricting to live set `L`, the restricted family `S_j ∩ L` is active at `j`
iff `S_j` survives, so `activeSupports_restrict_card` gives `#active(S·∩L) = survivingCount`, and
`cells_restrict_le_surviving` gives **`#cells(S·∩L) ≤ (n+1)^{survivingCount}`** — the cell cost is governed by the
*surviving* count the restriction/switching/core‑decomposition machinery controls.  *(ii) Branch correctness:*
`sat_branch_decompose` — `(∃ x, f x = true) ↔ ∃ b, branchSAT f K b`, the proved branch‑and‑restrict decomposition.
*(iii) Master bridge:* `nframe_gives_acc0_sat_speedup` assembles the pipeline into one visible theorem —
**a restriction with `(n+1)^{survivingCount} < 2^n` makes the restricted cell search beat brute force** — with the
single remaining socket `NFrameGivesACC0SatSpeedupSocket` (a restriction leaving few surviving gates), discharged by
`speedup_of_socket`.  So the **entire pipeline is one theorem with the open content isolated to exactly one socket**:
*the restriction/switching/core‑decomposition machinery guarantees few active surviving gates while leaving enough
live variables* — the heart of the ACC⁰ push.  Still the cell‑search model, not the full Turing‑machine
`2^{n-n^ε}` theorem; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Attacking the socket from `exists_low_survival` (`…ACC0SatSocketReduction`).**  The master socket
`NFrameGivesACC0SatSpeedupSocket` (`∃ L, (n+1)^{survivingCount} < 2^n`) is now **discharged from the probabilistic
existence theorem**.  `socket_of_expectation`: if the *expected* surviving‑gate count is `≤ r` (with
`(n+1)^r < 2^n`), then by `exists_low_survival` some restriction `L` has `survivingCount L < r+1`, i.e. `≤ r`, so
`(n+1)^{survivingCount L} ≤ (n+1)^r < 2^n` — the socket.  `speedup_of_expectation` chains this to the master, so
**expected survivors `≤ r` (with `(n+1)^r < 2^n`) ⇒ a restriction whose cell search beats brute force**, with no
combinatorial socket left.  This reduces the open content to a single *standard* quantity: the measure expectation
`Exp p (survivingCount) ≤ r`.  By the first moment that expectation is `≤ k·s·p`; the only remaining input is the
routine identification `Exp p (survivingCount) = ∑_j Pr(S_j survives)` (linearity of the discrete expectation over
the support indicators) with `Pr(S_j killed) = (1-p)^{|S_j|}` (the per‑support marginal) — standard facts about the
`p`‑biased measure.  Still the cell‑search model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Collapsing the socket to the bare regime (`…ACC0SatFirstMoment`).**  The expectation hypothesis `hE` is now
**discharged**, by proving the two measure facts in full.  *(i) Per‑support marginal:* `prDisjoint` —
`Pr p (Disjoint S ·) = (1-p)^{|S|}`: the event `Disjoint S L` is `L ⊆ Sᶜ`; factoring
`weight p L = (1-p)^{|S|}·p^{|L|}(1-p)^{|Sᶜ|-|L|}` over `L ⊆ Sᶜ` and summing with `biased_sum_one Sᶜ` gives
`(1-p)^{|S|}`.  *(ii) Linearity:* `exp_sum` — `Exp p (∑_j g_j) = ∑_j Exp p (g_j)`; writing `survivingCount` as a sum
of survival indicators (each `= 1` minus the kill indicator, so `exp_indicator_eq_survProb` gives
`Exp = 1-(1-p)^{|S|} = survProb`) yields **`exp_survivingCount_eq`: `Exp p (survivingCount) = expectedSurviving`**,
and with `expectedSurviving_le` (Bernoulli) **`exp_survivingCount_le`: `Exp p (survivingCount) ≤ k·s·p`**.  Composing
with `socket_of_expectation` gives **`socket_of_regime`**: the socket holds from the *bare arithmetic regime*
`k·s·p ≤ r` and `(n+1)^r < 2^n` — no probabilistic hypothesis remaining — and `speedup_of_regime` chains it to the
master speedup.  This is exactly the *first‑moment* regime (heavy restriction, `p` small); beating it (constant `p`
while collapsing high‑fan‑in gates) is the higher‑moment Håstad content, the genuine `NP ⊄ ACC⁰` frontier.  Still
the cell‑search model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**The second moment: variance identification and Chebyshev concentration (`…ACC0SatSecondMoment`).**  The variance
file computed the *abstract* `∑_{j,l} cov ≤ d·k·s·p`; the Chebyshev file gave `Pr((g−Eg)²≥t²) ≤ Exp((g−Eg)²)/t²`.
The missing link — the **identification of the measure variance `Exp((survivingCount−E)²)` with `∑_{j,l} cov`** —
is now proved in full.  Route through the **kill** indicators `kind S L = 1[S∩L=∅]`: the product
`kind A · kind B = 1[Disjoint(A∪B)]` is a *single* disjointness event, so `exp_kind_mul`:
`Exp(kind A·kind B) = (1-p)^{|A∪B|} = killProb(A∪B)` directly via `prDisjoint` (no inclusion–exclusion).  Since
`cov` is *defined* as `killProb(S∪T)−killProb S·killProb T`, expanding `Exp(K²)−(EK)²` (`exp_sub_sq`) for the kill
count gives `kill_variance_eq`: `∑_{j,l} cov = variance` term‑by‑term; and `survivingCount = k−K` (so equal centred
squares) yields **`survivingCount_variance_eq`: `Exp((survivingCount−E)²) = variance p supports`**.  Feeding this and
`variance_boundedOverlap_le` into `chebyshev_of_variance_le` gives **`survivingCount_concentration`:
`Pr(|survivingCount−E|"≥"t) ≤ d·k·s·p/t²`**, and the complement (`pr_compl`) gives **`most_restrictions_good`:
`Pr(within t of mean) ≥ 1 − d·k·s·p/t²`** — at *constant* `p` almost every restriction is good.  **Honest scope:**
this is a high‑probability (robustness) upgrade of first‑moment *existence*, **not** a lower existence threshold —
`min survivingCount ≤ E` always, so existence at `r ≈ k·s·p` was already free; concentration controls the *measure*
of good restrictions, not a smaller witness.  Pushing the threshold past constant `p` needs the **exponential**
switching tail `Pr(survivingCount≥t) ≤ (O(p·s))^t`, beyond the second moment — the genuine `NP ⊄ ACC⁰` content, and
exactly the overlap term `cov_nonneg` exposes.  Still the cell‑search model; proves nothing about `NEXP/NP ⊄ ACC⁰`
or `P ≠ NP`.

**The exponential tail: factorial‑moment method and the independent `(s·p)^t` tail (`…ACC0SatExpTail`).**  Pushing
to the exponential tail `Pr(survivingCount ≥ t) ≤ (…)^t`.  *(i) Factorial‑moment method:* `pr_ge_le_factorial_moment`
— `Pr(t ≤ X) ≤ Exp(C(X,t))` (the binomial coefficient `C(X,t) ≥ 1 ⟺ X ≥ t`, Markov on it).  *(ii) Elementary‑
symmetric identity:* `factorial_moment_eq` — `Exp(C(survivingCount,t)) = ∑_{|T|=t} Pr(all of T survive)` (`C(X,t)`
counts `t`‑subsets of the surviving set), giving `pr_ge_le_sum_jointSurv`: `Pr(t ≤ survivingCount) ≤ ∑_{|T|=t}
Pr(all of T survive)`.  *(iii) Independence (pairwise‑disjoint supports):* `exp_prod_kind_disjoint` — the product of
kill indicators is a *single* disjointness event of the disjoint union (card `∑|S_j|`), so `Exp(∏ kind) = ∏ killProb`;
the multilinear expansion `∏(1−kind) = ∑_{U}∏_U(−kind)` lifts this to **survival independence**
`jointSurv_disjoint_eq_prod`: `Pr(all of T survive) = ∏_{j∈T} survProb`.  *(iv) The tail:* `exp_tail_disjoint` —
**`Pr(t ≤ survivingCount) ≤ C(k,t)·(s·p)^t`** for pairwise‑disjoint supports of fan‑in `≤ s`.  **Honest scope:**
the `(s·p)^t` decay is genuine but (a) **requires independence** (`cov_disjoint`) and (b) carries the **clause‑count
factor `C(k,t)`**.  For *overlapping* supports it is *false*: `cov_nonneg` (positive correlation) gives
`Pr(all survive) ≥ ∏ survProb`, so no `(s·p)^t` bound holds — the precise wall.  Håstad's clause‑count‑free
`(5·p·w)^t` tail evades both defects but is about **decision‑tree depth** via the encoding/canonical‑labelling
argument (the `…Switching*` arc), not gate survival; that clause‑count‑free tail is the genuine `NP ⊄ ACC⁰` content
and remains open.  Still the cell‑search model; proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

**Connecting the switching decoder arc to a probability tail (`…Depth3SwitchingProbTail`).**  The decoder arc already
proves the *weighted* switching bound `tight_descent_switching_prob`: `∑_{Bad} pweight ≤ (2p/(1-p))^s·(2w)^s·∑_{Short}
pweight` — the `(2w)^s` from the proved injective path‑label encoding (`card_pathLabels`, `reconstructionCorrect_
fullpath`), the `(2p/(1-p))^s` from the per‑restriction weight gain.  The missing link to an actual **probability
tail** was that `pweight` is a *distribution*.  `pweight_total` proves it (`∑_ρ pweight p ρ = 1`, via
`Finset.prod_univ_sum` and the per‑coordinate mass `p+(1-p)/2+(1-p)/2=1`), so `∑_{Short} pweight ≤ 1` (`pweight_le_
one`), turning the weighted bound into **`hastad_switching_prob_tail`: `∑_{σ∈Bad} pweight p σ ≤ (4·p·w/(1-p))^s`** —
the `p`‑biased probability that a width‑`w` DNF/CNF needs canonical decision‑tree depth `≥ s` decays as `(O(p·w))^s`
**with NO dependence on the number of clauses**.  `hastad_switching_prob_tail_fullpath` discharges the
reconstruction invariant via the proved `reconstructionCorrect_fullpath`, so the tail is unconditional given the
concrete deepest‑descent hypotheses on `Bad`.  This is exactly the clause‑count‑free decay the gate‑survival tail
(`…ACC0SatExpTail`) provably *could not* achieve (its intrinsic `C(k,t)` factor) — the genuine switching‑lemma
phenomenon, now a probability statement.  **Honest scope:** depth‑3 DNF/CNF model, canonical deepest‑descent tree;
the full `NEXP ⊄ ACC⁰` programme needs this iterated across depth, composed with the MOD‑gate switching step
(`ACCDepth3Switch.switch_step`) and the Williams method — separate work.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or
`P ≠ NP` on its own.

**Depth reduction whp — the complement of the tail (`…Depth3SwitchingDepthReduction`).**  Since `pweight` is a
distribution (`pweight_total`), the switching tail's complement carries the rest of the mass: `switching_depth_
reduction` proves `1 − (4pw/(1-p))^s ≤ ∑_{σ∈Badᶜ} pweight σ`, and `depth_collapse_mass_ge` gives the explicit form —
the restrictions whose canonical decision tree has depth `< s` carry mass `≥ 1 − (4pw/(1-p))^s`.  A depth-`<s`
decision tree is a width-`<s` DNF *and* CNF, so on a `1 − (4pw/(1-p))^s` fraction of restrictions the **width-`w`
DNF depth-collapses to a depth-`≤2` (width-`<s`) circuit** — the single‑layer `depth 3 → depth 2` reduction as a
probability statement.  `switching_depth_reduction_fullpath` discharges reconstruction via
`reconstructionCorrect_fullpath`.  **Honest scope / `switch_step`:** this is the depth reduction *in the DNF model*
(`canonicalDT`, `pweight`); `ACCDepth3Switch.switch_step` is the *deterministic* atom of the sibling **`MOD` model**
(a forced `MOD` gate drops its CNF clause) — the same "a clause collapses" phenomenon in the modular layer.  A
*literal* cross‑model composition needs a bridge identifying `canonicalDT` depth with `MOD`‑gate forcing; that bridge
is **not** done here (not faked).  The full programme iterates this across layers and composes with the `MOD` step and
the Williams method.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP` on its own.

**The cross‑model bridge — and it is a NO‑GO (`…ACCSwitchingModBridge`).**  Building the bridge between the switching
depth reduction (DNF model: collapses by fixing only `~s` of `n` coordinates, leaving the rest *free*) and
`switch_step` (`MOD` model: a clause drops only when its gate is *forced*, which by locality needs the gate's
**entire support fixed**) resolves to the **Razborov–Smolensky vs. switching wall**, formalised.  Algebraic core:
`weightOn_update_add`/`modQStatOn_update` show a support‑coordinate flip shifts the `MOD` statistic by `±1`, so
`modQStatOn_flip_ne` — **the `MOD` statistic is fully sensitive** (`q ≥ 2`): every support‑coordinate flip changes it.
Hence `mod_statistic_live_on_free_cube`: the statistic is non‑constant on *any* restriction cube leaving a support
coordinate free; and for parity `mod_gate_parity_nonconstant`: the **gate value** is non‑constant there, so the gate
is neither forced true nor false and `switch_step` cannot fire.  Contrast: a width‑`w` DNF depth‑collapses with `~s`
coordinates fixed (`depth_collapse_mass_ge`), but a `MOD` gate of support `s` stays live until *all* `s` coordinates
are fixed.  That gap is exactly **why switching reduces `AC⁰` depth but provably does not reduce `MOD`/`ACC⁰` depth**
— the two models do not compose into a switching‑driven `ACC⁰` lower bound (which would contradict the known
hardness).  This is the *correct* mathematical answer to the cross‑model question: genuine `ACC⁰` lower bounds need a
different tool on the `MOD` layer (polynomial approximation / Razborov–Smolensky, the Williams method), not switching.
Proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.

## 5. The exact missing theorem — where everything converges

Every route terminates at the **same** wall, in five equivalent forms (all `= CookLevinFrontierHyp = P ≠ NP`):

| form | statement | provable half | open half |
|---|---|---|---|
| decision‑holonomy | every correct SAT trajectory has super‑poly decision time | — | the time bound |
| `AdaptiveResidualNonCollapse` | every cheap adaptive decomposition keeps `2^{Ω(n)}` outcomes | one fixed decomposition | the `min` over **all** |
| `DimensionGapHard` | `d_res(SAT) − d_obs ≥ Ω(n)` for *every* poly observer | a fixed observer carries debt | the `min` over **all** |
| global SPDP bridge | every poly‑time observer has poly SPDP rank | restricted `K` | all of `P` |
| Book‑1 CEW (A1) | every poly‑time SAT decider has polylog contextual width | syntactic surrogate; both unweighted invariants (dichotomy); all *fixed*‑order projections (locality no‑go); expander/PAC amplifiers can't rescue fixed order | `ScalingSPDPBridge` = `PolyTimeLowGodelSPDP`: at scaling order, **realized** feature count poly for `P` (not a counting fact) |
| `(Goldreich)InversionHardness` | the family resists fast inversion (OWF / local‑PRG security) | the four classes of §2 | all poly inverters |

In every form the **provable half is geometric/pointwise** (a fixed low‑`d_obs` observer, a fixed class) and the
**open half is universal** (the quantifier over *all* poly observers / *all* cheap decompositions / *all* poly
inverters). The gap theorem `distinguishability_debt_not_time_lower_bound` proves *why* the debt machinery — an
*action/space* bound — cannot by itself cross from the pointwise to the universal: that crossing is exactly
`P ≠ NP`.

**Bottom line.** The optimal predicate is identified and proved optimal; it unconditionally defeats every
restricted inverter class the programme expresses; the binding pair (low‑degree ∧ `AC⁰[p]`) is realized on that
single predicate with no hypothesis; the complementarity that blocked this is resolved; the false routes are
retired. The wall was then pushed across all three axes to its exact ceiling: **space** is settled (boundary
exactly `r`), the **time** axis is proved unreachable by the space machinery, the **decision** axis has an
unconditional (but non‑explicit) lower bound, and the **explicit** residue is isolated as the single `InNP`
conjunct — which the natural‑proofs barrier proves counting cannot supply, leaving the Nečiporuk `n²/log n`
frontier as the strongest explicit, non‑natural bound reachable. The N‑Frame / Book‑1 CEW route was audited to the
same wall — its A1 (bounded contextual width for all `P`) is the lone `P ≠ NP`‑strength field — and a proved
dichotomy shows *no unweighted contextual invariant* can discharge it: additive ones are too small to separate,
multiplicative/rank ones are achieved by easy functions, so only a *time‑structure‑coupled projection* (the
assumed‑not‑derived SPDP bridge) could.  The projected‑rank arc then probed that opening to its end: a proved
locality no‑go (`…AffineIndicatorCollapse`) shows **every *fixed*‑order projection — low‑degree and SPDP alike —
collapses the high‑degree affine/Tseitin residual to polynomial rank**, and expander/PAC amplifiers were proved
unable to rescue fixed order (they amplify *visibility*, not *invisibility*).  The Gödel‑hierarchy tower
(`…GodelHierarchySPDPScaling`) does raise visibility with level — but its feature budget at the scaling level is
*vacuous* (`…GodelFeatureCount`: the ceiling is exponential), so the surviving direction is one named theorem,
`ScalingSPDPBridge` / `PolyTimeLowGodelSPDP`: that poly‑time observers keep a polynomial number of *realized*
features at scaling order — A1 is provably **not a counting fact**, exactly the SPDP‑rank lower bound. The separation is reduced to one named statement, shown equivalent to
`P ≠ NP` in six forms and shown *unreachable* by these methods. Everything reducible is discharged. The one
irreducible step — an explicit, non‑natural decision lower bound above `n²/log n`, equivalently a contextual
invariant low *because of* the poly‑time structure, equivalently universal quantification over all polynomial‑time
machines — is `P ≠ NP` itself, and nothing here claims to take it.
