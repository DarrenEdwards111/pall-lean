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
