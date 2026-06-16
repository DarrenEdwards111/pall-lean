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

**The `ACC⁰` arc, and a finished `AC⁰` package.** A second, self‑contained line built the Yao–Beigel–Tarui /
Razborov–Smolensky polynomial method *from scratch* in Lean and ran it to its exact ceiling. First it proved the
obstruction is real: an exact unbounded‑fan‑in `OR`/`AND` over `F₂` has degree **= fan‑in** (`…ACC0ExactDegreeNoGo`),
so no single exact low‑degree polynomial works — the only route is *approximate*‑then‑*decode*. That route was then
built end to end: the balancedness of random `F₂` linear forms, degree‑`t` boosting (correct on a `1−2^{-t}`
fraction), a self‑contained **finite Chernoff** + union‑bound sampling to a quasipolynomial majority‑correct family,
and the **basis bridge** showing the boosted parity predictor *is* a low‑monomial‑`AND`‑degree object (its wide sets
live in the degree‑1 *linear* part). On top, an unbounded‑fan‑in circuit datatype and the **depth induction** were
formalized, yielding the **complete, quantitative `AC⁰` theorem**: *every `MOD`‑free circuit has an `F₂` approximant
of degree `≤ t^depth` and error `≤ size·2^{-t}`* (`…ACC0QuantDegree`, `…ACC0QuantError`) — for `t = O(log size)` and
constant depth, polylog degree and `<1/2` error, the textbook Razborov–Smolensky bound. This is **classical**
(`AC⁰`/`AC⁰[2]`‑level: `PARITY ∉ AC⁰`, `MOD ∉ AC⁰[p]`), *not* new mathematics and *not* progress toward `P ≠ NP`; its
value is a clean sorry‑free reconstruction. Crucially the construction *stops exactly where the method stops*: it
extends to `MOD` only for **prime‑power** moduli (`MOD₂` done, `…ACC0Mod2Exact`), and **composite `MOD_m` has no
low‑degree representation over any single field** — the genuine `ACC⁰` barrier, the same wall the rest of this corpus
documents, and the reason `NEXP ⊄ ACC⁰` required Williams' algorithmic (separation‑strength) method rather than the
polynomial method. So the `AC⁰` package is *finished*; the `ACC⁰` frontier is open mathematics, not Lean engineering.

### Why this does not prove `ACC⁰` — the composite‑`MOD` barrier (the honest ceiling of the polynomial method)

The polynomial method *extends cleanly to a prime modulus* and *provably stops at a composite one*. Both halves are
now formalized, so the boundary is a theorem, not a hope:

* **Prime side — `MOD_p` is exactly low‑degree over `F_p` (`…ACC0ModPExact`, proved, clean axioms).** By Fermat's
  little theorem, over `F_p` the count‑`≡0` indicator is `MOD_p(x) = 1 − (∑_{i∈S} x_i)^{p−1}` *exactly*
  (`modp_exact_eval`), of total degree `≤ p−1` (`modpPoly_totalDegree_le`), and so lies in the degree‑`≤(p−1)`
  monomial‑`AND` span over `F_p` (`modp_mem_monoAND_span`). This is the prime‑`p` generalisation of the `MOD₂`/parity
  case (`…ACC0Mod2Exact`); together with the OR/AND boosting it gives the full Razborov–Smolensky picture for
  `AC⁰[p^k]` (prime powers reduce to `F_{p^k}` by the same argument).
* **Composite side — there is no such field (the barrier).** For `m = p·q` with two distinct prime factors, the
  Fermat exponent is pinned to the order of the *chosen* field: `a^{p−1} = 1` for `a ≠ 0` in `F_p`, but `a^{m−1}` is
  **not** a `{0,1}`‑indicator there (the order is `p−1`, not `m−1`), and over `F_q` it fails symmetrically. So no
  *single* field sees `MOD_m` as a low‑degree `{0,1}` function. Formalized as the mixed‑modulus split: `MOD₆`
  decomposes by CRT into `MOD₂ ∧ MOD₃` (`mod6_eq_mod2_and_mod3`, `…Layer3MixedModulus`), each component low‑degree
  over its **own** prime field with **no common field** — and the `MOD_q`‑over‑`F_p` reachable residue set is provably
  **not** an `F`‑subspace for `q ≥ 3` (`modq_residue_image_not_subspace`, `…ACC0ModQFeasibility`), so the `2^{rank}`
  linear‑algebra shortcut that closes the parity case is genuinely `MOD₂`‑specific.

This is *exactly* why `NEXP ⊄ ACC⁰` (Williams) needed a fundamentally different, **algorithmic** method
(faster‑than‑brute‑force `ACC⁰`‑SAT ⇒ the separation, opened but not closed here — the `fastSat` socket in
`…WilliamsCashout` / `…ObserverWilliams`) rather than the polynomial method. The composite‑`MOD` low‑degree representation is not a missing
Lean lemma — it is a genuine mathematical obstruction, the same wall the rest of this corpus documents from the
observer/effective‑rank side. **The polynomial‑method package is complete up to `AC⁰[p^k]` and provably no further; it
is not `NEXP ⊄ ACC⁰` and not `P ≠ NP`.**

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
| **mixed‑modulus SAT speedup (residue compression)** | `modResVec` + `eval_factors_residue` (MOD‑circuit factors through residue vector ∈ ∏ZMod q_j); `sat_iff_residue_image` (SAT ⇔ residue‑cell search); `residue_cell_count_le` (≤ ∏q_j, const/gate); **`mod_circuit_sat_speedup`** / **`mod6_circuit_residue_speedup`**: `∏q_j<2^n` (resp `6^k<2^n`) ⇒ `<2^n` cells — Williams' compression kernel | `…ACC0ModResidueSpeedup` |
| **operational residue machine** | `residueSearch` (step‑counted SAT algorithm, residue analogue of `cellSearch`); **`residueSearch_decides`** (decides SAT), `residueSearch_steps_le_prod_moduli` (`steps≤∏q_j`), **`residueSearch_beats_bruteforce`** / `…_mod6_…` (`∏q_j<2^n` resp `6^k<2^n` ⇒ `steps<2^n`) | `…ACC0ResidueMachine` |
| **branched residue cost** | `branched_residue_cost_le` (`≤2^killed·∏surviving q_j`); `branched_residue_regime` (`killed+live=n`, `∏q_j<2^live` ⇒ `<2^n`); **`branched_residue_beats_bruteforce`** / `…_mod6_…` — past the `∏q_j<2^n` base regime (per‑branch `∏q_j` vs cell‑search `(n+1)^r`) | `…ACC0BranchedResidue` |
| **restriction ⇒ few surviving residue gates** | `residue_image_card_le_active` (`\|cells\|≤∏_{active}q_j`); `residue_active_after_restriction` (active = surviving = `¬Disjoint`); **`residue_cells_le_surviving_moduli`**: `\|cells(C↾L)\|≤∏_{surviving}q_j` — discharges step 2's per‑branch bound | `…ACC0ResidueRestriction` |
| **depth iteration (socket)** | `MixedModResidueSearchable` / `MixedACCDepthReductionSocket` (Yao–Beigel–Tarui depth‑2 normal form, OPEN); `residueSearchable_base` (nonvacuous); **`acc0_depth_reduction_speedup`**: socket ⇒ residue search decides `Satisfiable(eval C)` in `<2^n` (switching CAN'T supply the collapse — MOD no‑go) | `…ACC0ResidueDepthReduction` |
| **Williams cash‑out interface** | `mixedACC_speedup_of_depthReduction` (PROVED link: depth socket ⇒ residue speedup ∀ACC⁰); **`residue_cashout_bundled`** (headline: depth socket + `UniformWilliamsRealizationSocket` ⇒ `NEXP⊄ACC⁰`); `williams_socket_iff_separation` / `realization_socket_iff_separation` (SELF‑AUDIT: each cash‑out socket ⟺ the separation — reduces nothing; abstract `Prop` params, NOT a proof) | `…ACC0WilliamsCashout` |
| **residue‑observer algebra** | `ObservedBy`; `observed_sat_iff`/`observed_cellCount_le`; `.comp`/`.and`/`.or`/`observer_sat_branch`; **`observed_top_pi`** (composition law: top over observed ⇒ product observer) + `observed_pi_cellCount_le` (`≤∏card`); `modGate_observedBy`/`depth2_observedBy` (residue speedup re‑derived) | `…ACC0ResidueObserver` |
| **toy Beigel–Tarui** | `boundedGate_observedBy` (bounded‑support gate observed by projection, `card 2^{\|T\|}`); **`toy_bounded_bottom_searchable`**: arbitrary top over fan‑in‑`≤w` bottom gates is searchable in `<2^n` when `∏2^{\|T_i\|}<2^n` (the SYM‑of‑AND_w form — depth‑reduction socket discharged for the bounded‑bottom fragment) | `…ACC0BeigelTaruiToy` |
| **depth‑3 MIXED fragment** | **`depth_mixed_searchable`**: arbitrary top over a bottom MIXING `MOD_q` (`card q`) and bounded‑`AND_w` (`card 2^{\|T\|}`) gates — observer types vary per gate — is searchable in `<2^n` when `∏(per‑gate states)<2^n`; `modGate_card_le`/`boundedGate_card_le` (the two qualifying gate observers) | `…ACC0Depth3Mixed` |
| **support normal form (ACC⁰ syntax ⇒ observer)** | `support`/`eval_depends_on_support` (value depends only on read‑vars, induction on circuit); **`acc0_observed_by_projection`**: ANY `ACC0Circuit` (any depth) observed by projection to its support; `acc0_junta_searchable` (junta ⇒ searchable `<2^n`); **`acc0_top_over_subcircuits_searchable`** (top over ACC⁰ subcircuits jointly reading `<n` vars ⇒ searchable, via union support) — chips `ACC⁰⊆mixed‑bottom` at syntax level | `…ACC0SupportNormalForm` |
| **depth‑3 MOD normalization (residue gain)** | `mod_bottom_circuit_searchable` (arbitrary top over MOD family ⇒ residue‑searchable `<2^n` when `∏q_i<2^n`, ANY supports); **`and_of_mods_searchable`**: syntactic `MOD_{q₁}∧MOD_{q₂}` normalizes to a `Depth2ModCircuit`, residue‑searchable when `q₁·q₂<2^n` even with `S₁=S₂=univ` (where junta gives `2^n`) | `…ACC0Depth3ModNormalize` |
| **AC⁰‑over‑MOD normalization (general)** | `ModComb` (boolean comb over MOD leaves); `combEval_eq_combTop` (value factors through MOD outputs, induction); **`modComb_normalizes`**: any AND/OR/NOT comb of a MOD family `= ⟨gates, combTop C⟩.eval` (a `Depth2ModCircuit`); `modComb_searchable` (residue‑searchable `<2^n` when `∏q_i<2^n`) | `…ACC0ModCombNormalize` |
| **observer extracted from raw `ACC0Circuit` syntax** | `stateBound`/`ModsPos` (occurrence product, positive‑modulus predicate); **`acc0_residueObserved`**: by induction on the circuit, ANY `ACC0Circuit` (positive MOD moduli) is `ObservedBy` a product statistic of state count `≤ stateBound C` — `MOD` leaf→`modGate_observedBy` (`ZMod q`, `card q`), `var`→coordinate projection (`Bool`, `card 2`), gates→`.comp`/`.and`/`.or`; **`acc0_modcircuit_searchable`** (`stateBound C<2^n` ⇒ SAT‑searchable `<2^n` cells). The MOD‑bottom is now *derived* from syntax, not assumed (subsumes `modComb`/`and_of_mods`, adds `var` leaves). Honest gap unchanged: `stateBound` is the *occurrence* product, so the gain is for few‑leaf circuits; a *small* bound for arbitrary ACC⁰ is full Yao–Beigel–Tarui (open) | `…ACC0ExtractObserver` |
| **deduplicated state bound (collapses the occurrence overcount)** | `modOcc` (`MOD`‑occurrence product; `var`/`const` cost `1` — vars read *inside* a `MOD` gate absorbed into its residue) + `varSupp` (deduplicated *set* of vars read by `var`‑leaves); **`acc0_dedupObserved`**: by induction, `eval C` observed by `(mstat, ONE projection to `varSupp C`)` with the residue part of card `≤ modOcc C` — the `∧`/`∨` arms **share a single** projection onto `varSupp a ∪ varSupp b` (each arm recovered by restriction along `vsₐ ⊆ vsₐ∪vs_b`), so the bound carries `2^\|vsₐ∪vs_b\|` not `2^(\|vsₐ\|+\|vs_b\|)`; **`acc0_dedup_searchable`** (`modOcc C·2^\|varSupp C\| < 2^n` ⇒ SAT‑searchable `<2^n`). Strict tightening of `stateBound` (vars counted once, `MOD`‑internal vars free); fires where neither pure‑support (`2^\|support\|`) nor pure‑occurrence reaches. Honest gap unchanged: `varSupp C = univ` ⇒ `2^n`; small bound for arbitrary ACC⁰ = full Yao–Beigel–Tarui (open) | `…ACC0DedupShrink` |
| **syntactic restriction + boundary shrinkage** | `subst1 C i v` (substitute `v` for var `i`; on `MOD`: `mod q S t ↦ mod q (S.erase i)(t-[i∈S]·v)` — fixed coordinate dropped, target shifted by its residue contribution); `weightOn_update` (support count splits across the fixed coord); **`eval_subst1`**: `eval (subst1 C i v) x = eval C (Function.update x i v)` (induction — syntactic restriction = semantic); `varSupp_subst1_subset` (`⊆ (varSupp C).erase i`), `modOcc_subst1_le`, `ModsPos_subst1` (boundary monotone, moduli preserved); **`varSupp_subst1_card_lt`** (`i ∈ varSupp C` ⇒ `\|varSupp(subst1 C i v)\| < \|varSupp C\|` — restricting a read var strictly shrinks the dedup boundary); **`sat_branch_subst1`** (`Satisfiable(eval C) ↔ Satisfiable(eval(subst1 C i false)) ∨ Satisfiable(eval(subst1 C i true))`). The restriction algebra for shrinkage. Honest: NOT a switching lemma — one branch halves each boundary (`2·modOcc·2^{\|vs\|-1}=modOcc·2^{\|vs\|}`), no asymptotic gain alone; the random‑restriction collapse is the deep open content | `…ACC0RestrictShrink` |
| **random‑restriction collapse of the dedup boundary** | `restrList` (multi‑var restriction = iterated `subst1`) + `applyRestr`; **`eval_restrList`** (`= eval C (applyRestr l x)`, induction — genuine restriction); `varSupp_restrList` (`⊆ varSupp C \ fixed`), `modOcc_restrList_le`, `ModsPos_restrList` (lift from single‑var lemmas, no `MOD`‑shift re‑proof); `fixedListOf Lᶜ β` + `varSupp_restr_compl_subset` (fixing `L`'s complement ⇒ `varSupp ⊆ varSupp C ∩ L`, only live vars survive); `exp_coord_eq` (single coord live w.p. `p`, via `exp_indicator_eq_survProb` on `{i}`); **`exp_liveBoundary_eq`**: `Exp p (\|varSupp C ∩ L\|) = p·\|varSupp C\|` (proportional collapse in expectation, `exp_sum`+linearity over the existing `p`‑biased measure); `exists_small_liveBoundary` (Markov + `exists_of_pr_lt_one`); **`dedup_restriction_collapses`**: ∃ live set `L` s.t. *for every* fixed‑assignment `β`, the restricted circuit's dedup boundary is `< a` (just above `p·\|varSupp C\|`). Honest: *proportional* (first‑moment) collapse, NOT switching — no SAT speedup alone (`2^{#fixed}·2^{p\|vs\|}=2^{\|vs\|}`); *super*‑proportional collapse (function depends on fewer vars = Håstad switching whp) is the deep open content | `…ACC0RandomRestrictShrink` |
| **function‑level collapse: decision‑tree observer** | **`dt_observed`**: `BoolDecisionTree.eval T` is `ObservedBy` a statistic of cell‑count `≤ 2^{T.depth}` (induction; the query node combines subtrees by a **sum** type `S_low ⊕ S_high` = additive leaf count, which is why the bound is `2^{depth}` not `2^{\#queried vars}`) — the boundary is the *function's leaf*, INDEPENDENT of how many vars it syntactically reads; **`dt_searchable`** (`2^{depth}<2^n` ⇒ SAT‑searchable `<2^n`); **`function_collapse_of_dt`** (any function *computed by* a shallow DT is SAT‑searchable below brute force, via `Computes`). The cash‑out converting decision‑tree depth — the complexity measure switching reduces — into the observer boundary. AC⁰ layer only (switching provably can't collapse `MOD` — the MOD no‑go) | `…ACC0DecisionTreeObserver` |
| **`DTree → BoolDecisionTree` bridge: switching's canonical tree, observed** | **`toBoolDT`** (constructor‑for‑constructor map `leaf/node ↦ leaf/query`); **`toBoolDT_eval`** (`[propext]` only) + **`toBoolDT_depth`** (semantics & depth preserved, one‑line inductions — the two datatypes are isomorphic, same branch convention & depth recurrence); `dtree_observed`/`dtree_searchable` (the `dt_observed`/`dt_searchable` cash‑out transferred to `Depth3.DTree`); **`canonicalDTree_observed`/`canonicalDTree_searchable`**: the switching arc's `canonicalDTree` (width‑`w` DNF, fuel `F`, depth `≤ F·w` by `canonicalDTree_depth_le`) has a `≤ 2^{F·w}`‑cell observer boundary, SAT‑searchable `<2^n` when `2^{F·w}<2^n`. The representation step previously flagged separate is now DONE — the function‑level collapse composes end‑to‑end with switching's canonical tree. Caveats: `DTree.eval(canonicalDTree …)=restricted DNF` is cited canonical‑tree soundness (not re‑proved); MOD layer excluded (MOD no‑go) | `…ACC0DTreeBridge` |
| **AC⁰ + MOD composition across the no‑go** | **`dt_oracle_observed`**: a depth‑`d` decision tree over Boolean *oracle*‑subfunctions `h : Fin m → (Fin n→Bool)→Bool` (each query branches on `h i x`, not a raw bit) computes a function `ObservedBy` a `≤ 2^d` boundary (same sum‑typed leaf observer as `dt_observed`); **`acc0_over_mod_observed`**: instantiating `h j = (gⱼ).eval` for `MOD` gates, `x ↦ T(g₁(x),…,g_m(x))` (`T` a depth‑`d` DT top) is `ObservedBy` a `≤ 2^d` boundary — the `MOD` gates are QUERIED as oracles along each path, **never collapsed** (respecting the no‑go), and the boundary is independent of the gates' moduli and of how many variables they read; **`acc0_over_mod_searchable`** (`2^d<2^n` ⇒ SAT‑searchable `<2^n`). Honest: this is the *deterministic* composition law — *given* a shallow `T` over the gate outputs, boundary `2^d`. Supplying such a `T` is the OPEN part: gate outputs `gⱼ(x)` are determined by `x` (not independent random bits), so the switching random‑restriction does **not** collapse the top over them — the no‑go's deeper form. Composes a *single* AC⁰‑over‑MOD level; iterating switching through a `MOD` layer stays blocked (the genuine open ACC⁰ frontier) | `…ACC0ModComposition` |
| **oracle‑control syntax → decision‑tree observer** | **`OracleControl`** (Boolean control circuit `leaf j`/`const`/`¬`/`∧`/`∨` over `m` oracle leaves) + `controlEval`; **`treeOf`/`treeOf_eval`/`treeOf_depth_le`** (complete query tree: `eval = f` on the path‑determined assignment; depth `≤ |L|`) + **`fullTree`** (query all `m` positions: ANY `f : (Fin m→Bool)→Bool` reduces to a depth‑`≤m` DT computing it); **`control_to_decision_tree`** (every control reduces to a depth‑`≤m` `BoolDecisionTree`); **`oracle_control_dt_searchable`** (control computed by a depth‑`d` DT ⇒ `x ↦ controlEval C (fun j => (gⱼ).eval x)` SAT‑searchable `<2^n` when `2^d<2^n`); **`oracle_control_over_mod_searchable`** (unconditional fragment speedup: an `AC⁰` control over `m` `MOD` oracles is SAT‑searchable below brute force whenever `2^m<2^n` — `<≈n` `MOD` gates — regardless of control structure). Honest: deterministic control→DT reduction (depth `m` in general) | `…ACC0OracleControl` |
| **step 3 (DNF fragment): random restriction makes the control shallow** | **`dnf_control_switching_searchable`**: for a DNF control `D` over `k` oracle positions (per‑term width `≤w`, `≤M` clauses, switching union‑bound `(2p/(1-p))(2wM)<1` and `r^s/(1-r)<1`) and `MOD` gates `gate : Fin k → ModGate n` with `s≤n`, there **exists a position‑restriction `ρ`** under which `(canonicalDT D F ρ)` is shallow (depth `<s`) and `x ↦ (canonicalDT D F ρ).eval (fun j => (gateⱼ).eval x)` is SAT‑searchable in `<2^n`. The collapse is the **proved fully‑discharged** switching lemma `Depth3.exists_shallow_all_tight_uncond` (NO reconstruction socket — only width/clause‑count + the union‑bound smallness condition, instantiated at `G={D}`); `canonicalDT` returns a `BoolDecisionTree` directly, so it composes with `acc0_over_mod_searchable` with no extra bridge (`2^{depth}<2^s≤2^n`). HONEST: `ρ : Restriction k = Fin k → Option Bool` restricts the oracle **positions**, not the `n` input vars `x` — the composed function plugs the gate outputs into the *position‑restricted* tree, which is **not** the original circuit restricted by an `x`‑restriction (gate outputs determined‑not‑independent = the no‑go's deeper form). So this is the control‑position‑level switching collapse composed with the oracles — a genuine fragment result — NOT an `x`‑level circuit speedup. The position/`x` bridge is the open frontier, not faked; shallow tree computes the `ρ`‑restricted DNF by cited `canonicalDT` soundness | `…ACC0DNFControlSwitching` |
| **position → `x` bridge: realizing oracle restrictions by input restrictions** | `Extends x σ` + **`RealizableByInputRestriction ρ gate`** (∃ input restriction `σ` s.t. every completion forces each fixed gate `j` (`ρ j = some b`) to output `b` — forcing a MOD gate needs its whole support fixed, per the no‑go); `modGate_eval_congr` (MOD value depends only on its support, via `weightOn` sum‑congr); **`realizable_of_disjoint`** (POSITIVE fragment: pairwise‑disjoint supports + per‑gate achievability `∀ j b, ρ j = some b → ∃ a, (gateⱼ).eval a = b` ⇒ realizable — `σ` fixes coord `i` to the witness of the unique fixed gate whose support contains `i`; disjointness ⇒ well‑defined & `Classical.choose` lands on the right gate); **`position_restriction_not_always_realizable`** (THE NO‑GO: `![⟨2,{0},0⟩,⟨2,{0},1⟩]`, `ρ ≡ some true` — both gates forced `true` would give `modQStatOn{0}2 x = 0` and `= 1`, so `0=1` in `ZMod 2`, impossible). **So the position→`x` bridge is TRUE on the disjoint fragment and FALSE in general** — exactly why it must stay fragment‑restricted (a socket for arbitrary circuits), not a free theorem. Honest: solves the *forcing* half (fixing the determined gates); the full switching composition also needs the *free* gates to stay free under `σ` (the disjoint case supports it; not assembled here) | `…ACC0OracleRestrictionRealization` |
| **disjoint-fragment `x`-level speedup (exact reduction)** | **`gate_vector_realizable`**: disjoint supports + each gate both-achievable (`∀ j b, ∃ a, (gateⱼ).eval a = b`) ⇒ the gate-output vector is SURJECTIVE onto `{0,1}^k` (`∀ y : Fin k → Bool, ∃ x, ∀ j, (gateⱼ).eval x = y j` — via `realizable_of_disjoint` instantiated at `ρ = some ∘ y`, witness `x = fun i => (σ i).getD false`); **`disjoint_fragment_sat_iff`**: the EXACT reduction `Satisfiable (x ↦ controlEval C (fun j => (gateⱼ).eval x)) ↔ Satisfiable (controlEval C)` (the `n`-variable circuit is satisfiable iff the `k`-variable control is — `→` takes `y := g(x)`, `←` realizes any satisfying `y` by surjectivity); **`disjoint_fragment_speedup`**: `f`-SAT over `Fin n` ↔ search over `Finset.univ (Fin k → Bool)`, whose card `2^k < 2^n` (`Fintype.card_fun`+`card_bool`+`card_fin`). The `n`-variable circuit collapses EXACTLY to the `k`-variable control — a genuine `x`-level restricted speedup. Disjointness is **load-bearing**: the no-go (`position_restriction_not_always_realizable`) breaks surjectivity for overlapping gates, so the reduction provably fails there — which is why the fragment restriction is essential, not cosmetic. The disjoint case is the *worst* case for the output-cell count (image is the full `2^k`), so `2^k` is tight | `…ACC0DisjointFragmentSpeedup` |
| **parity (MOD₂) constraint realization: realizable ⟺ F₂ system consistent** | **`realizable_iff_achievable`** (arbitrary MOD, NO disjointness: `RealizableByInputRestriction ρ gate ↔ ∃ x, ∀ j b, ρ j = some b → (gateⱼ).eval x = b` — realizability is *exactly* existence of an achieving input; disjointness was only used to *construct* it, the no-go is when none exists; proof: `→` via `x = fun i => (σ i).getD false`, `←` builds `σ` fixing the fixed gates' supports to `x`, forcing via `modGate_eval_congr`); `parityGate := ⟨2,S,t⟩`, `zmod2_ne_iff` (`¬s=t ↔ s=t+1` over `ZMod 2`, `revert;decide`), **`parity_force_linear`** (`(parityGate S t).eval x = b ↔ modQStatOn S 2 x = (if b then t else t+1)` — forcing a parity gate IS the F₂ equation); **`parity_realizable_iff_consistent`** (realizable ⟺ `∃ x, ∀ j b, ρ j = some b → modQStatOn (Sⱼ) 2 x = (if b then tⱼ else tⱼ+1)` — the F₂ linear system has a Boolean solution); **`control_sat_iff_reachable_image`** (arbitrary MOD: `Satisfiable (x ↦ controlEval C (g x)) ↔ ∃ y ∈ univ.image (gate-vector), controlEval C y = true` — SAT searches the *reachable* gate-output image, the genuine observer boundary, not pretended-independent `2^k`); `parityVector`, `modQStatOn_two_eq_sum`, **`parityVector_xor`** (`parityVector` of bitwise xor = `ZMod 2` sum — parity is additive), `parity_reachable_zero_mem`+**`parity_reachable_add_mem`** (the reachable parity image is an F₂-SUBSPACE: closed under `0` and `+`). So `\|reachable image\| = 2^rank` — `2^k` only in the disjoint/full-rank case; this REPLACES "disjoint-only" with linear-algebraic compatibility. Honest: the structural (subspace) half of `2^rank`; the exact `finrank`-card closed form is in `…ACC0ParityRankCardinality`; general `MOD_q` is a harder 0/1-feasibility problem | `…ACC0ParityConstraintRealization` |
| **exact `2^rank` cardinality of the reachable parity image** | **`parityLinMap S`** (the F₂-`LinearMap` `(Fin n→ZMod 2) →ₗ[ZMod 2] (Fin k→ZMod 2)`, `v ↦ fun j => ∑_{i∈Sⱼ} vᵢ`, with `map_add'`/`map_smul'` via `Finset.sum_add_distrib`/`Finset.mul_sum`); `parityVector_eq_linMap` (`parityVector S x = parityLinMap S (boolEmbed x)`); `zmod2_ite` (`if decide(z=1) then 1 else 0 = z` over `ZMod 2`, `revert;decide`); **`range_parityVector`** (`Set.range (parityVector S) = ↑(LinearMap.range (parityLinMap S))` — the Boolean-input embedding is surjective onto `Fin n → ZMod 2`); **`parity_subspace_card`** (`Fintype.card ↥(range parityLinMap) = 2 ^ Module.finrank (ZMod 2) (range parityLinMap)` via `Module.card_eq_pow_finrank` + `ZMod.card`); **`parity_reachable_card`**: `Nat.card (Set.range (parityVector S)) = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (parityLinMap S))` (`↥(↑M)→↥M` via `SetLike.coe_sort_coe`). The parity-gate observer boundary is **exactly `2^rank`** — `2^k` iff the parity gates are independent (full rank), strictly smaller under linear dependence. Quantitative closure of the reachable-image story for `MOD₂`; general `MOD_q` is a `0/1`-feasibility problem over `ZMod q` (not free linear algebra) | `…ACC0ParityRankCardinality` |
| **rank-based `x`-level speedup (parity)** | **`image_parityVector_card`** (`(Finset.univ.image (parityVector S)).card = 2^rank`, via `Nat.card_eq_fintype_card`+`Set.toFinset_card`+`Set.toFinset_range`+`parity_reachable_card`); **`parity_rank_speedup`**: for a parity-gate control `C` over `(parityGate (Sⱼ) (tⱼ))`, `f`-SAT over `Fin n` ⟺ search the reachable gate-output image (the gate vector `= (fun y => fun j => decide (y j = tⱼ)) ∘ parityVector S` — a relabeling of `parityVector`), and that image's card is `< 2^n` once `2^rank < 2^n` (via `Finset.image_image`+`Finset.card_image_le`+`image_parityVector_card`). Strictly stronger than disjoint `2^k`: `rank ≤ k` with strict inequality under any linear dependence among the parity gates — a parity control whose gates span an `<n`-dimensional F₂ row space is sub-`2^n` searchable EVEN with overlapping supports. The rank analogue of `disjoint_fragment_speedup`, now with the F₂ rank in place of `k` | `…ACC0ParityRankSpeedup` |
| **general `MOD_q` realization = 0/1-feasibility (no rank for `q>2`)** | **`modGate_eval_true_iff`** (`G.eval x = true ↔ modQStatOn G.support G.modulus x = G.target`, via `decide_eq_true_eq`) / **`modGate_eval_false_iff`** (`= false ↔ count ≠ target`); **`modq_realizable_iff_feasible`** (`RealizableByInputRestriction ρ gate ↔ ∃ x : Fin n→Bool, ∀ j, (ρ j = some true → count_{Sⱼ}(x) = tⱼ) ∧ (ρ j = some false → count_{Sⱼ}(x) ≠ tⱼ)` over `ZMod qⱼ` — the general-`q` analogue of `parity_realizable_iff_consistent`, now an equality/disequality **0/1-integer-feasibility** system, NOT free linear algebra; `[propext, Quot.sound]`); `modQStatOn_singleton` (`modQStatOn {i} q x = if x i then 1 else 0`); **`modq_residue_image_not_subspace`** (THE OBSTRUCTION, proved: for a single `MOD₃` gate the reachable residue set is `{0,1}⊆ZMod 3` — `1` reachable, `1+1=2` NOT — so it is *not closed under +*, hence the `2^rank` F-subspace structure is genuinely **MOD₂-specific**). Honest: the `x`-level speedup is `q`-independent (`≤2^k` Boolean gate-output patterns, already `oracle_control_over_mod_searchable` for arbitrary moduli); what `MOD_q` changes is *which* of the `2^k` patterns are reachable — the 0/1-feasibility region, with **no closed-form cardinality / lattice shortcut for `q≥3`** (the honest barrier beyond parity) | `…ACC0ModQFeasibility` |
| **mixed moduli `MOD₆ = MOD₂ ∧ MOD₃` realization via CRT** | **`mod6_eval_true_iff`** (the CRT split: `(⟨6,S,t⟩ : ModGate n).eval x = true ↔ (weightOn S x ≡ t.val [MOD 2]) ∧ (weightOn S x ≡ t.val [MOD 3])` — proved via `modGate_eval_true_iff` → `ZMod.natCast_rightInverse`+`ZMod.natCast_eq_natCast_iff` to pass to `Nat.ModEq`, then `Nat.modEq_and_modEq_iff_modEq_mul` with `Nat.Coprime 2 3`); **`mod6_realizable_iff_mixed`** (a forced-true `MOD₆` family `(fun _ => some true)` is realizable ⟺ `∃ x : Fin n→Bool, ∀ j, (weightOn (Sⱼ) x ≡ (tⱼ).val [MOD 2]) ∧ (weightOn (Sⱼ) x ≡ (tⱼ).val [MOD 3])` — the simultaneous solvability of the mod-2 **and** mod-3 count systems). Combines the F₂-linear/rank story (mod-2 part) with the F₃-feasibility story (mod-3 part), **coupled through the shared `x`** — neither the F₂ rank nor the F₃ feasibility alone suffices; the realizability is the intersection of an F₂-affine condition and an F₃-feasibility region, with no product/closed-form shortcut. Honest: forced-true case (cleanest); a general `ρ` (mixing forced true/false) makes each gate's condition a conjunction/disjunction of the two CRT parts | `…ACC0Mod6Mixed` |
| **mixed moduli `MOD₆`, general `ρ` (forced true ∧, forced false ∨)** | **`mod6_eval_false_iff`** (`(⟨6,S,t⟩ : ModGate n).eval x = false ↔ ¬(weightOn S x ≡ t.val [MOD 2]) ∨ ¬(weightOn S x ≡ t.val [MOD 3])` — forcing false negates the CRT conjunction into a DISJUNCTION; proved `rw [Bool.eq_false_iff, ne_eq, mod6_eval_true_iff, not_and_or]`); **`mod6_realizable_iff_general`** (arbitrary `ρ : Fin k → Option Bool`: `RealizableByInputRestriction ρ (fun j => ⟨6, Sⱼ, tⱼ⟩) ↔ ∃ x, ∀ j, (ρ j = some true → (count ≡ tⱼ.val [MOD 2]) ∧ (≡ [MOD 3])) ∧ (ρ j = some false → ¬(count ≡ tⱼ.val [MOD 2]) ∨ ¬(≡ [MOD 3]))` — the fully-general mixed-modulus condition). Forced-true gates give a *conjunction* of CRT congruences, forced-false gates a *disjunction* of CRT disequalities; all coupled through the shared `x` — a genuine mixed CSP over the Boolean cube (linear mod-2 ∧ feasibility mod-3 atoms), no rank/product shortcut. Completes the MOD-realization arc for all `ρ` | `…ACC0Mod6MixedGeneral` |
| **YBT `SYM`-top count observer (the tractable heart of `SYM∘AND`)** | `gateCount g x := ∑ⱼ (if gⱼ x then 1 else 0)` (count of accepting sub-gates); `symEval g h x := h (gateCount g x)` (a symmetric = count-function of `m` sub-gates); `gateCount_le` (`≤ m`, via `Finset.sum_le_sum`); **`sym_observed`** (`symEval g h` is `ObservedBy (gateCount g)`, decoder `h`); **`sym_count_card_le`** (`(univ.image (gateCount g)).card ≤ m+1`, image `⊆ range(m+1)` — **the symmetric top collapses the boundary from `2^m` to `m+1`**); **`sym_searchable`** (`SYM∘(m gates)` SAT-searchable in `< 2^n` once `m+1 < 2^n`; at the YBT normal form `m = 2^{polylog n}` ⇒ `< 2^n`). Proves the structural reason the YBT `SYM` output gate is tractable — it sees only the *count* of accepting sub-gates — for **arbitrary** sub-gates (the YBT-specific content only fixes `m`). Honest: the YBT **reduction** (arbitrary `ACC⁰` → `SYM∘AND` with `m` quasipolynomial) is the deep structural theorem and is **NOT** formalized — the open `ACC⁰` wall, socketed as `MixedACCDepthReductionSocket`; a small cell count is not a uniform algorithm | `…ACC0SymmetricObserver` |
| **low-degree polynomial → `SYM∘AND` (YBT chip)** | `monoAND S x := decide (∀ i ∈ S, x i = true)` (monomial `AND` gate, fan-in `\|S\|`); `lowDegSubsets n D := (range (D+1)).biUnion (fun i => univ.powersetCard i)` + **`lowDegSubsets_card`** (`= ∑_{i ∈ range (D+1)} n.choose i`, via `Finset.card_biUnion` with `PairwiseDisjoint` powersetCards + `Finset.card_powersetCard`); **`monomial_count_le`** (`mono : Fin m → Finset (Fin n)` injective with `(mono j).card ≤ D` ⇒ `m ≤ ∑_{i≤D} C(n,i)` — the bottom-gate-count bound, via `card_image_of_injective` + `card_le_card` into `lowDegSubsets`); **`lowDegreePoly_searchable`** (a `SYM` gate over `m` monomial-`AND`s `symEval (fun j x => monoAND (mono j) x) h` is SAT-searchable in `< 2^n` once `m+1 < 2^n` — the polynomial value `∑_S monoAND_S` is `gateCount` over its monomial-`AND`s, so `sym_searchable` applies directly). The polynomial→`SYM∘AND` cash-out for a `0/1`-coefficient multilinear polynomial (a sum of distinct monomials); general `ℕ`/`F_p` coefficients duplicate each monomial gate (scaling the count by the coefficient bound). Honest: the hard direction — that an arbitrary `ACC⁰` circuit *is* such a low-degree polynomial (the Razborov–Smolensky approximation + composition) — is **NOT** proved; it is the open structural wall (`MixedACCDepthReductionSocket`). YBT pipeline: `ACC⁰ ─[RS approx: OPEN]→ low-deg poly ─[PROVED]→ SYM∘AND ─[PROVED]→ count observer ─[PROVED]→ searchable` | `…ACC0PolyToSymAnd` |
| **RS low-degree span → `SYM∘AND` bottom layer (the RS bridge)** | **`squarefreeEvalMonomial_eq_monoAND`** (`squarefreeEvalMonomial p S x = if monoAND S x then (1 : ZMod p) else 0` — the RS generator `∏_{i∈S} boolToZMod p (xᵢ)` is `1` iff every bit in `S` is set, i.e. **the low-degree-span generators ARE the monomial-`AND` gates**; proved by `by_cases (∀ i∈S, x i = true)`, `Finset.prod_eq_one`/`Finset.prod_eq_zero`); **`lowDegPolyEval_mem_monoAND_span`** (lifts Layer3's `eval_mem_lowDegSpan` through the bridge — a degree-`≤D` `MvPolynomial`'s Boolean‑cube eval lies in the `ZMod p`-`Submodule.span` of the monomial-`AND` indicators of degree `≤ D`, the `SYM∘AND` bottom layer, via `funext` + `rw [hgen]`). Connects the existing RS machinery (`…Layer3DimensionCount`) to the `SYM∘AND` world exactly. Honest gaps (both flagged): (1) RS is **approximate** (`acc0_approx_by_lowRankPredictor` agrees on `1-ε`), so this is an *approximate* `SYM∘AND`, not the exact YBT form; (2) the `ZMod p`-linear top → count-mod-`p` `SYM` gate needs (weighted) gate duplication; the exact `AC⁰[p] → SYM∘AND` across depth is the open structural wall (`MixedACCDepthReductionSocket`) | `…ACC0RSToSymAnd` |
| **weighted-count `SYM` observer (closes the `ZMod p`-linear → count-mod-`p` gap)** | `weightedGateCount c g x := ∑ⱼ cⱼ * (if gⱼ x then 1 else 0)` (the `ℕ`-coefficient polynomial value = count over the multiset with gate `j` duplicated `cⱼ` times) + `weightedSymEval c g h x := h (weightedGateCount c g x)`; `weightedGateCount_le` (`≤ ∑ⱼ cⱼ`, via `Finset.sum_le_sum`, `split <;> simp`); **`weightedSym_observed`** (`ObservedBy` the weighted count, `⟨h, fun _ => rfl⟩`); **`weightedSym_count_card_le`** (`(univ.image (weightedGateCount c g)).card ≤ (∑ⱼ cⱼ)+1`, image `⊆ range(∑cⱼ+1)` — **boundary is the total weight `+1`, not `2^m`**); **`weightedSym_searchable`** (SAT-searchable `< 2^n` once `∑ⱼ cⱼ + 1 < 2^n`); **`weightedGateCount_cast_eq`** (over `ZMod p` with `cⱼ = (coeffⱼ).val`, `((weightedGateCount … : ℕ) : ZMod p) = ∑ⱼ coeffⱼ * (if gⱼ x then (1:ZMod p) else 0)` — the **coefficient-duplication identity**: the weighted count's residue is the `ZMod p` polynomial value, via `Nat.cast_sum`/`Nat.cast_mul`/`ZMod.natCast_rightInverse`). Closes the gap exactly: a `ZMod p`-linear combination of monomial-`AND`s IS a weighted-count `SYM∘AND` (the count-mod-`p` top over the duplicated family, `≤ (p-1)·∑_{i≤D}C(n,i)` gates). Honest: RS is still approximate; the exact `AC⁰[p]→SYM∘AND` across depth is still the wall | `…ACC0WeightedSymAnd` |
| **approximate vs exact (what RS approximation buys)** | `disagreeSet f g := Finset.univ.filter (fun x => f x ≠ g x)`; **`sat_card_le_of_disagree`** (`(univ.filter (f ·=true)).card ≤ (univ.filter (g ·=true)).card + (disagreeSet f g).card` — `{f=true} ⊆ {g=true} ∪ disagree`, via `card_le_card`+`card_union_le`; an approximating `g` bounds `f`'s **solution count**, not its satisfiability); **`exact_sat_iff`** (`disagreeSet f g = ∅ ⇒ (Satisfiable f ↔ Satisfiable g)` — only **exact** agreement transfers SAT). Pins the approximate/exact boundary: the searchable cash-out needs the **exact** `SYM∘AND` (the RS approximation gives only a sparsity/correlation bound; the correlation side is where RS lower bounds live, the exact side is the wall) | `…ACC0ApproxConsequence` |
| **YBT exact normal-form socket (structural wall + conditional cash-out)** | **`HasExactSymAndForm C := ∃ m (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool), eval C = symEval (fun j x => monoAND (mono j) x) h ∧ m+1 < 2^n`** (the exact YBT `SYM∘AND` normal form as a named socket); **`ybt_socket_searchable`** (`HasExactSymAndForm C ⇒ Satisfiable (eval C)` decided by a `< 2^n`-cell image search over `gateCount`, via `rw [heq]` + `lowDegreePoly_searchable`). The socket holding for **arbitrary** `ACC⁰` `C` (with `m` quasipolynomial) **is** the Yao–Beigel–Tarui theorem — a known classical result, **NOT** formalized (the open structural wall, cf. `MixedACCDepthReductionSocket`). The cash-out needs the **exact** form (an approximate one only bounds the solution count, per `…ACC0ApproxConsequence`); a small cell count is not a uniform algorithm | `…ACC0YBTSocket` |
| **YBT reduction core: `AC⁰[p]` circuit → `SYM∘AND`-bottom span (conditional on degree)** | **`acc0p_circuit_in_monoAND_span`**: for `c : BoolCircuitSyntax n` with `BoolCircuitSyntax.IsAC0Syntax c` and `(toPoly p c).totalDegree ≤ D`, the embedded Boolean function `(fun x => boolToZMod p (c.eval x)) ∈ Submodule.span (ZMod p) (range of degree-≤D monomial-`AND` indicators)`. Proof: Layer3's **exact** `toPoly_eval_AC0` (`eval (embed x) (toPoly p c) = boolToZMod p (c.eval x)`) rewrites the function to `x ↦ eval (embed x) (toPoly p c)`, then `lowDegPolyEval_mem_monoAND_span` (via `squarefreeEvalMonomial_eq_monoAND`) puts it in the monomial-`AND` (`SYM∘AND` bottom) span. **The degree bound IS the wall**: `toPoly` is EXACT but its degree is *uncontrolled* — an unbounded fan-in `∧` becomes a *product* of its inputs' polynomials, so degree grows with fan-in (and multiplicatively with depth); polylog degree is the *approximate* RS layer (`toAgree`, agreeing on `1-ε`), so the exact polylog-degree form for arbitrary `AC⁰[p]` is open. Honest: extracting the explicit `ZMod p`-combination from span membership and feeding `weightedSym_searchable` is the remaining mechanical glue; the degree bound is the genuine structural wall | `…ACC0YBTReduction` |
| **`toAgree` approximant in the bounded `SYM∘AND` span (degree bound DISCHARGED)** | **`acc0p_toAgree_in_monoAND_span`**: `(fun x => eval (fun i => boolToZMod p (x i)) (toAgree p t R C)) ∈ Submodule.span (ZMod p) (range of degree-≤((p-1)t)^{C.depth} monomial-`AND` indicators)` — **unconditional**, the degree bound is *proven* (`toAgree_totalDegree_le p t ht R C : (toAgree p t R C).totalDegree ≤ ((p-1)*t)^C.depth`) and fed into `lowDegPolyEval_mem_monoAND_span`. The difference from `…ACC0YBTReduction`: `toPoly` (exact) had *uncontrolled* degree so the membership was conditional; `toAgree` (the RS approximant) *has* the polylog degree bound, so the membership is unconditional — the approximant is genuinely a bounded `SYM∘AND` of quasipolynomial size (`∑_{i≤D}C(n,i)`, `D = ((p-1)t)^{depth}` polylog for constant depth + polylog `t`). Honest: the only remaining gap is **approximate vs exact** — `toAgree` agrees with the circuit on a `1-ε` fraction (Layer3), so this is the *approximant*'s `SYM∘AND` form; by `…ACC0ApproxConsequence` it bounds the circuit's solution count, not its SAT. The exact polylog-degree `SYM∘AND` for arbitrary `AC⁰[p]` (true YBT) is the open wall | `…ACC0ToAgreeDegree` |
| **symmetric-count exact trick (`AND`/`OR` are exactly symmetric, no approximation)** | **`gateCount_eq_card_iff`** (`gateCount g x = m ↔ ∀ j, g j x = true` — the count hits `m` iff every gate accepts, i.e. `AND`; via `Finset.sum_lt_sum` for `→`, `simp [h]` for `←`); **`gateCount_pos_iff`** (`1 ≤ gateCount g x ↔ ∃ j, g j x = true` — count positive iff some accepts, i.e. `OR`; via `ne_eq`+`Finset.sum_eq_zero_iff`+`push_neg`); **`and_exact_sym`** (`(fun x => decide (∀ j, g j x = true)) = symEval g (fun k => decide (k = m))` — `AND` is *exactly* the `SYM` count gate `[·=m]`, via `decide_eq_decide`); **`or_exact_sym`** (`(fun x => decide (∃ j, g j x = true)) = symEval g (fun k => decide (1 ≤ k))` — `OR` is *exactly* the `SYM` count gate `[1≤·]`); **`and_exact_searchable`/`or_exact_searchable`** (so `AND`/`OR` over `m` gates are SAT-searchable in `≤ m+1` cells, **exactly**, via `sym_searchable`). The Beigel–Tarui exact trick at the **gate level**: `AND`/`OR` (and `MOD`, already `modGate_eval_true_iff`) need *no* RS approximation — they are *exactly* symmetric count functions, the exactness coming from the `SYM` top reading the exact `gateCount`. Closes the approximate/exact gap **per gate**; the remaining step is composing these exact symmetric representations across constant depth while keeping the gate count quasipolynomial (the structural composition) | `…ACC0SymmetricExact` |
| **depth composition law (top over observed subcircuits → searchable)** | **`depth_compose_searchable`**: for `sub : Fin k → (Fin n → Bool) → Bool`, `stat : ∀ i, (Fin n → Bool) → S i` (`[∀ i, Fintype (S i)]`) with `∀ i, ObservedBy (subᵢ) (statᵢ)`, any `top : (Fin k → Bool) → Bool`, and `∏ᵢ Fintype.card (Sᵢ) < 2^n`: `(fun x => top (fun i => subᵢ x))` is SAT-searchable in `< 2^n` — joint statistic `fun x => fun i => statᵢ x` (the product), via `observed_top_pi` (composition) + `observed_sat_iff` + `observed_pi_cellCount_le` (`≤ ∏ᵢ card Sᵢ`). The depth-composition law in the observer framework — it iterates to any depth (each `subᵢ` may itself be such a composite). Honest: the boundary is the **product** `∏ᵢ |Sᵢ|`, *exponential* in the width `k` — the naive composition. The whole point of YBT is replacing this multiplicative blow-up by the **additive** degree composition of the polynomial method (degree adds across `∧`/`∨` ⇒ depth-`d` ⇒ polylog degree ⇒ quasipoly monomial-`AND`s, `…ACC0ToAgreeDegree`); that additive/quasipoly control is *approximate* (RS) and the *exact* quasipoly depth-composition (true YBT) is the open structural wall. (Needed `maxHeartbeats 1000000` for the dependent-Pi `Fintype.card_pi`; removed `[∀ i, DecidableEq]` so the image's `DecidableEq` matches `observed_pi_cellCount_le`'s Classical one) | `…ACC0DepthCompose` |
| **additive degree control (`AND` degree = sum of input degrees)** | `toPolyList_eq_map` (`toPolyList p cs = cs.map (toPoly p)`, induction); **`toPoly_andGate_totalDegree_le`**: `(toPoly p (andGate cs)).totalDegree ≤ (cs.map (fun c => (toPoly p c).totalDegree)).sum` — the `AND` gate's polynomial degree is the **sum** (not product) of its inputs' degrees, since `AND = ∏` and `MvPolynomial.totalDegree_list_prod` gives `totalDegree(∏) ≤ ∑ totalDegree`; **`toPoly_andGate_totalDegree_le_of_bounded`**: fan-in `cs.length ≤ w` and `∀ c ∈ cs, (toPoly p c).totalDegree ≤ D` ⇒ `(toPoly p (andGate cs)).totalDegree ≤ w * D` (one layer multiplies the degree by `≤` the fan-in, via `List.sum_le_card_nsmul`). This **additivity** is exactly why the polynomial method's gate count is *quasipolynomial* (degree adds across `∧`/`∨`, so a depth-`d` circuit has polylog degree `((p-1)t)^{depth}` — `toAgree_totalDegree_le` — hence quasipoly monomial-`AND`s) rather than the observer's *exponential* product boundary (`…ACC0DepthCompose`). Honest: this is the within-layer additive law; the full polylog-degree-across-depth is `toAgree_totalDegree_le` (proved, for the approximant); the exact quasipoly depth-composition (true YBT) is the open wall | `…ACC0AdditiveDegree` |
| **exact depth composition (Bool specialization)** | **`exact_depth_composes`**: for `sub : Fin k → (Fin n → Bool) → Bool` and any `top : (Fin k → Bool) → Bool`, once `2^k < 2^n`, `(fun x => top (fun i => subᵢ x))` is SAT-searchable in `< 2^n`, with the subcircuit-output vector `fun x => fun i => subᵢ x` as the cell statistic (boundary `2^k`). The **exact** side of composition (no approximation): the exact symmetric gates (`…ACC0SymmetricExact`: `AND`/`OR`/`MOD` *are* count functions) compose at any depth this way, but with the **exponential** `2^k` *product* boundary. Specializes `depth_compose_searchable` at `S = fun _ => Bool` (`Fintype.card_bool`, `Finset.prod_const`); the `DecidableEq (Fin k → Bool)` instance diverges from the Classical one baked into `depth_compose_searchable`, closed by `convert … using 2; congr!` (subsingleton instances). This makes the exact-vs-quasipoly tension precise as a *theorem*, not a missing lemma: exact composition ⇒ exponential `2^k` boundary; quasipoly composition (`…ACC0AdditiveDegree`/`…ACC0ToAgreeDegree`, additive degree) ⇒ only `1-ε`-*approximate*. Having *both at once* — an exact `SYM∘AND` of quasipolynomial size — is the Beigel–Tarui construction (exact ℤ-polynomial of polylog degree decoded by the symmetric top via CRT), the irreducible YBT wall | `…ACC0ExactCompose` |
| **the Williams `fastSat` ingredient, concrete + quantitative** | Grounds the abstract `fastSat`/`savings` `Prop` of `…ObserverWilliams`/`…WilliamsCashout` in the actual `SYM∘AND` combinatorics. `fastSatWork m := m+1` (count-cells examined). **`fastSat_savings_of_work_le`** (`work ≤ 2^{n−k} ⇒ 2^k·work ≤ 2^n` — savings `≥ 2^k`, via `SpeedupMargin.savings_ge_of_work_le`); **`fastSatWork_le_of_degree`** (degree-`≤D` injective monomial-`AND` family ⇒ `work ≤ (∑_{i≤D}C(n,i))+1`, via `monomial_count_le`); **`lowDegMonomialCount_le_pow`** (`∑_{i≤D}C(n,i) ≤ (D+1)·n^D` — quasipoly gate count, via `Nat.choose_le_pow`); **`symAnd_williams_fastSat`** (the headline: a degree-`≤D` injective `SYM∘AND` decides SAT by the count-cell image search, the cell count fits `2^{n−k}`, **and** the work delivers Williams savings `≥ 2^k`); **`symAnd_williams_fastSat_quasipoly`** (explicit regime `(D+1)·n^D+1 ≤ 2^{n−k} ⇒ savings ≥ 2^k`; `D` polylog ⇒ `k = n−polylog = Ω(n)`, the Williams margin, far above the `ω(log n)` the hierarchy needs). Makes the *combinatorial* `fastSat` a real counted procedure with an exact margin, not an assumed `Prop`. Honest — does NOT prove `NEXP ⊄ ACC⁰`; the two open links stay named and unfaked: (1) the YBT **exact** normal form for arbitrary `ACC⁰` (`MixedACCDepthReductionSocket`; method gives only the approximate form `…ACC0ApproxConsequence` and stops at prime-power `MOD`); (2) uniform TM realization (`UniformWilliamsRealizationSocket`, itself `NEXP ⊄ ACC⁰`-strength per `williams_socket_iff_separation`). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0WilliamsFastSat` |
| **the YBT exact normal-form socket — exact `SYM∘AND` closure by mixed-radix counting** | Discharges the **existence/decoding** half of the Yao–Beigel–Tarui socket `HasExactSymAndForm` (`…ACC0YBTSocket`) as a genuine theorem, via Beigel–Tarui's base-`(m+1)` merge, and isolates the irreducible remainder (the **size**). `HasSymAndForm f s` (`f` equals a `SYM` count gate over `≤ s` monomial-`AND`s, size-tracked); count algebra `saCount_sum_elim` (disjoint union → additive) and `saCount_prod_const`/`fin_sum_const_nat` (replicate `r×` → `r·count`); base cases `hasSymAndForm_const`/`_monoAND`/`_var`/**`_mod`** (`MOD_q` *is* a symmetric function of its support literals — exact, size `|S|`); `hasSymAndForm_not`; **`hasSymAndForm_combine`** — the headline mixed-radix merge, closed under *any* `comb : Bool→Bool→Bool` (merged count `C = c₁+(m₁+1)·c₂`, decode by `mod`/`div (m₁+1)`, size `s₁+(s₁+1)·s₂`) → `_and`/`_or`; **`acc0circuit_hasSymAndForm`** — *every* `ACC0Circuit` has an exact `SYM∘AND` form (structural recursion over `const`/`var`/`not`/`and`/`or`/`mod`), explicit size `symAndSize C`; **`acc0circuit_hasExactSymAndForm`** — the bridge (reindex to `Fin m` via `Fintype.equivFin`) yields the socket `HasExactSymAndForm C` whenever `symAndSize C + 1 < 2^n`. Honest — the **exactness is proved in full**; the **size is the wall**: `symAndSize` is *multiplicative* at every `AND`/`OR`, hence exponential in general, so the socket fires only when it stays `< 2^n` (not ordinary poly-size). A quasipolynomial-size exact `SYM∘AND` (true YBT) needs the polynomial method's *additive* degree (`…ACC0AdditiveDegree`), available only **approximately** (`…ACC0ApproxConsequence`) and only at prime-power `MOD` (`…ACC0ModPExact` barrier). So this converts the whole socket into the sharp residue **"exact + quasipolynomial size at once"** (the `…ACC0ExactCompose` wall). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0YBTExactCompose` |
| **splitting the uniform-Williams-realization socket into named sub-sockets** | The same surgery as the YBT socket, on the *other* open Williams socket. The monolith `UniformWilliamsRealizationSocket := (∀ n, MixedACCResidueSatSpeedup n) → NEXPnotACC0` (`…ACC0WilliamsCashout`) is **factored** into a named chain: **`EncodingSocket`** (S1 — cell search → machine procedure, *routine*), **`CostBridgeSocket`** (S2 — cell count `< 2^n` → runtime `2^{n−n^ε}`, *routine*; arithmetic core proved), **`UniformitySocket`** (S3 — per-`n` algorithms form a uniform family, *standard assumption*), **`TimeHierarchySocket`** (S4 — Williams' algorithmic method: uniform speedup ⇒ `NTIME` collapse ⇒ ⊥, **the deep content**). **`realization_socket_factors`** proves `S1∧S2∧S3∧S4 ⇒` the monolith; **`routine_reduce_to_timeHierarchy`** proves that given S1–S3 the socket reduces to S4 alone; **`timeHierarchy_socket_iff_separation`** is the self-audit — once a uniform speedup is established, S4 is *logically equivalent* to `NEXP ⊄ ACC⁰` (proved with **no axioms**, pure logic), so S4 carries the entire difficulty and S1–S3 carry none. The cost bridge's quantitative heart is **proved**: **`cell_count_savings`** (`steps ≤ 2^{n−k} ⇒ 2^k·steps ≤ 2^n`, via `SpeedupMargin`); and **`proved_speedup_is_trivial_savings`** makes explicit that the *currently proved* `steps < 2^n` is only the `k = 0` (factor-`>1`) savings — the super-polynomial `k = n^ε` Williams needs is supplied only by a **quasipolynomial** exact form, routing back to the `…ACC0YBTExactCompose` size wall. So the realization socket is now split: routine parts grounded, one deep separation-strength assumption (S4) named and isolated. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0WilliamsRealizationSplit` |
| **the `ACC⁰` frontier summary — the dependency graph as Lean theorems** | A single readable file re-stating the converged boundary map so the corpus is checkable at a glance. Re-exports of the proved pillars: **`ac0_approximation_quantitative`** (`approximable_full`), **`modp_exact_low_degree`** (`modp_exact_eval`), **`exact_symAnd_decoding`** (`acc0circuit_hasSymAndForm`), **`fastSat_quantitative`** (`symAnd_williams_fastSat`), **`timeHierarchy_is_the_separation`** (the realization self-audit). The headline **`williams_route_reduces_to_two_sockets`** assembles the *entire* Williams route into **one conditional theorem**: given **(A)** the exact-quasipolynomial `SYM∘AND` / depth-reduction socket and **(B)** the time-hierarchy socket — plus the *routine* realization sub-sockets — `NEXP ⊄ ACC⁰` follows (composes `residue_cashout_bundled` with `routine_reduce_to_timeHierarchy`). The only non-routine inputs are the two named walls; everything else is proved or routine. **Now also folds in the three restricted fragments** where the size wall is *crossed*: `restricted_exact_by_leaves` (`O(log n)` leaves), `restricted_exact_by_footprint` (footprint `< n` / bounded-overlap `MOD`), `restricted_exact_by_depth` (bounded binary depth) — all from the one `psize = ∏ leaf-bases` identity — plus `restricted_speedup_by_footprint`/`_depth` (super-polynomial count-cell `ACC⁰`-SAT savings on those fragments). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP`  **Now also folds in the N-Frame route**: `nframe_bridge` (collapse ⇒ low correlation, proved), `nframe_collapse_composes` (lift through a layer), `nframe_unconditional_disjoint` (discharged fragment), `nframe_lower_bound` (holonomy lower bound from ONE socket — N-Frame analogue of the Williams two-socket reduction, sharper since the bridge is proved).  **Also folds in the rank route** (the sharpened N-Frame route): `rank_bridge` (`2^{cellRank} < |L| ⇒` low correlation), `rank_subsumes_survivor` (`cellRank ≤ survivingCount`), `rank_fragment_equal_supports` (equal supports, any `k`, unconditional), `rank_random_restriction` (`p`-biased low-rank live set), `rank_whp` (two-event intersection on the rank tail, subsumes the survivor whp route) — open: `ACC0ForcesLowCellRank` = the rank-flavoured switching lemma. | `…ACC0FrontierSummary` |
| **restricted YBT — bounded-leaf `ACC⁰` has an exact *quasipolynomial* `SYM∘AND` form** | Genuine progress on the YBT *size* wall, for the natural restricted fragments. Engine: a clean multiplicative identity **`symAndSize_succ_eq_psize`** — writing `psize C := symAndSize C + 1`, the exact size is *exactly the product of leaf base sizes* (`const 1`, `var 2`, `not` id, `and`/`or` product, `mod |S|+1`; proved by induction + `ring`). Then **`psize_le`** (`psize C ≤ maxBase C ^ leafCount C`), **`restricted_acc0_has_exact_symAnd`** (`psize C < 2^n ⇒ HasExactSymAndForm C`), and the headline **`restricted_acc0_quasipoly`** (`leafCount C ≤ ℓ`, `maxBase C ≤ B`, `B^ℓ < 2^n ⇒ HasExactSymAndForm C`). For `ℓ = O(log n)`, `B = poly(n)`: `B^ℓ = 2^{O(log²n)}` (quasipolynomial) `< 2^n` — so **bounded-leaf, poly-`MOD`-support `ACC⁰` has an exact quasipolynomial `SYM∘AND` form**, the genuine restricted Beigel–Tarui. Honest — restricted: quasipoly only when the leaf count is *logarithmic*; full `ACC⁰` (poly-many leaves) gives `B^{poly} = 2^{poly}`, exponential, the wall unchanged. A real fragment, not the full theorem. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RestrictedYBT` |
| **bounded-overlap `MOD` — small support footprint ⇒ exact `SYM∘AND` form** | The *sharp* version of the restricted result, in the form that captures bounded-overlap / disjoint `MOD` gates. Define the **support footprint** `baseSum C` (`mod q S t → |S|`, `var → 1`, `const → 0`, `not`/`and`/`or` additive); then **`psize_le_two_pow_baseSum`** (`psize C ≤ 2^(baseSum C)`, since each base `b ≤ 2^{b−1}`) and **`acc0_exact_of_baseSum_lt`** (`baseSum C < n ⇒ HasExactSymAndForm C`) — *sharp*, as `baseSum = log₂ psize`. For an `AND` of a `MOD_q` list (`andOfModList`, footprint `= ∑|S_i|` via `baseSum_andOfModList`), **`boundedOverlap_mod_exact`** gives `∑|S_i| < n ⇒` exact form. And the structural fact **`disjoint_mod_footprint_le`** (`disjoint_foldr_union` → `sum_card_eq_card_union` → `sum_card_le_of_pairwise_disjoint`): pairwise-disjoint `MOD` supports have footprint `≤ n` (each variable counted once), so **`disjoint_mod_exact`** — pairwise-disjoint `MOD` gates not covering all `n` variables have an exact `SYM∘AND` form. Honest: the footprint criterion is *sharp* for the mixed-radix construction but caps at `< n` — it covers circuits reading `< n` literal-incidences (disjoint / bounded-overlap `MOD`, bounded total support); a general `ACC⁰` circuit reads all `n` variables many times over (footprint `≫ n`), so this precisely characterises the controllable fragment, untouched is the wall. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundedOverlapMOD` |
| **the restricted Williams speedup — small footprint ⇒ super-polynomial `ACC⁰`-SAT savings** | The *cash-out* of the restricted exact-form results into an actual Williams-style speedup theorem for the controllable fragments. **`restricted_acc0_searchable`** — every `ACC0Circuit` has its SAT decided by a count-cell search with cell count `≤ psize C` (the exact `SYM∘AND` size; via `acc0circuit_hasSymAndForm` + `observed_sat_iff` + the `saCount` range bound + `symAndSize_succ_eq_psize`). **`restricted_williams_speedup`** — if `baseSum C + k ≤ n` (footprint `≤ n−k`), SAT is decided by `≤ 2^(n−k)` cells with Williams savings `2^k · cells ≤ 2^n`. **`restricted_savings_by_footprint`** — the parametric form: the savings exponent is *exactly* the footprint deficit `n − baseSum C` (so footprint `= polylog` gives savings `2^{n−polylog}`, super-polynomial). **`boundedOverlap_mod_williams_speedup`** / **`disjoint_mod_williams_speedup`** — instantiated to an `AND` of `MOD_q` gates with bounded total support / pairwise-disjoint supports (`|⋃ Sᵢ| + k ≤ n ⇒` savings `2^k`). Honest: a *real* super-polynomial-savings `ACC⁰`-SAT algorithm in the count-cell model, but only for footprint-`< n` fragments (disjoint / bounded-overlap, where the exact form is below `2^n`); it **feeds** the realization split as a concrete instance of the `fastSat`/cost-bridge inputs on these fragments, and does **not** discharge the deep `TimeHierarchySocket` (separation-strength) nor the full-`ACC⁰` size wall. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RestrictedWilliamsSpeedup` |
| **the bounded-depth fragment — depth `d` ⇒ `≤ 2^d` leaves ⇒ polynomial exact `SYM∘AND` + speedup** | Controls the restricted fragment by **depth** (complementing leaf-count and footprint), again through the `psize` identity. **`leafCount_le_two_pow_depth`** (`leafCount C ≤ 2^(depth C)`: a depth-`d` binary circuit has `≤ 2^d` leaves). **`psize_le_of_depth`** (`depth C ≤ d`, `maxBase C ≤ B ⇒ psize C ≤ B^{2^d}` — *polynomial* for constant `d` and poly base). **`bounded_depth_exact`** (`B^{2^d} < 2^n ⇒ HasExactSymAndForm C`). The `psize`-parametric speedup **`restricted_williams_speedup_of_psize`** (`psize C ≤ 2^{n−k} ⇒` savings `2^k`), and the headline **`bounded_depth_williams_speedup`** (`depth C ≤ d`, `maxBase C ≤ B`, `B^{2^d} ≤ 2^{n−k} ⇒` SAT decided by `≤ 2^{n−k}` cells with savings `≥ 2^k`) — for constant `d` and poly `B`, `B^{2^d} = 2^{O(log n)}`, so `k = n − O(log n)`, super-polynomial. Honest: `depth` here is *binary* (`and`/`or` are 2-ary), so "depth 2" = `≤ 4` leaves (small balanced circuits); the classic *unbounded-fan-in* depth-2 `ACC⁰` circuit is a deep binary chain with only *linearly* many leaves, covered instead by the leaf-count (`O(log n)` leaves) and footprint fragments. A genuine complementary fragment, not the unbounded-fan-in model. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundedDepth` |
| **uniformity bookkeeping — the restricted constructions lift to uniform `ACC⁰` families** | Makes the *structural* half of the realization split's `UniformitySocket` concrete. A **uniform `ACC⁰` family** is a single Lean function `ACC0Family := (n : ℕ) → ACC0Circuit n` (manifestly uniform), with uniform-bound predicates `UniformFootprint`/`UniformLeaf`/`UniformBase`/`UniformDepth` (each bound a single `ℕ → ℕ`). Since every restricted theorem is applied *pointwise* by one structural recursion, a uniformly bounded family yields a uniform family of exact forms / speedups: **`uniform_symAndSize_bound`** (the *uniform `SYM∘AND` translation*: `symAndSize (F n) + 1 ≤ 2^(b n)`, exact-form size bounded by a single function of `n`); **`uniform_exact_of_footprint`** / **`uniform_exact_of_depth`** (the whole family has exact `SYM∘AND` forms); **`uniform_williams_speedup`** / **`uniform_depth_williams_speedup`** (the whole family gets the count-cell Williams speedup with a uniform savings exponent `k : ℕ → ℕ`). Honest: this is *structural* uniformity (one total function / one recursion over all `n`), which discharges that half of `UniformitySocket`; it does **not** define Turing machines, so it does **not** establish full *machine* uniformity (a single poly-time TM emitting the count cells) — that stays the socket's open content (`EncodingSocket`/`CostBridgeSocket`). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0UniformFamily` |
| **the N-Frame cell-collapse route — bridge proved, restriction lemma socketed** | States the N-Frame route to a full-`ACC⁰` correlation bound in the explicit *cell-collapse* vocabulary, isolating the single hard open statement. `CellCollapse supports L := 2^{#survivors} < |L|` (few gate-supports survive on a live set); `LowHolonomyCorrelation` (the predictor `g ∘ weightVec` agrees with some `fParity D` at most half the time on an off-diagonal axis). **`cell_collapse_implies_low_holonomy_correlation`** is the *bridge* — **proved**, a re-export of `ACCSwitchingPipeline.predictor_fails_of_survivors`. **`FullACC0ForcesCellCollapse`** is the *hard open socket* — that a full-`ACC⁰` predictor's supports force the collapse on some live set, the N-Frame analogue of a switching/restriction lemma (same `NP ⊄ ACC⁰`-strength content as `RestrictionTreeSwitch`). **`cell_collapse_of_survival`** reduces the socket to a concrete condition (`< m` survivors on a live set of size `≥ 2^m`), pinning the open target to "a restriction leaving `< log₂|L|` survivors on a large live set `L`". **`nframe_route`** is the composition (socket ▸ proved bridge ⇒ low correlation). Honest: the probabilistic half is proved (`exists_low_survival`); the quantitative switching bound for *full* `ACC⁰` is open and `NP ⊄ ACC⁰`-strength — not deliverable by naive leaf-switching, by the proved `MOD` no-go (`mod_gate_parity_nonconstant`). This pins the open target precisely; it does **not** prove it. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCollapseRoute` |
| **quantitative survival bound for bounded fragments — N-Frame route closed UNCONDITIONALLY** | Discharges the `FullACC0ForcesCellCollapse` socket for two bounded fragments, making the N-Frame route unconditional there. **`survivingCount_le_card`** (≤ k supports survive any live set, `card_filter_le`). **`bounded_gate_forces_cell_collapse`** (`2^k < n ⇒` collapse; live set `univ`, `2^survivors ≤ 2^k < n`). **`survivingCount_eq_zero_of_disjoint`** + **`small_footprint_forces_cell_collapse`** (footprint `+ 2 ≤ n ⇒` collapse; live set = complement of supports' union, `0` survivors, `|L| = n−|⋃| ≥ 2`; via `compl_eq_univ_sdiff`+`card_compl`). **`bounded_gate_low_holonomy_correlation`** / **`small_footprint_low_holonomy_correlation`** (compose with the proved bridge `nframe_route`: predictor does NOT correlate with the holonomy parity — UNCONDITIONAL, no socket). Honest: bounded fragments only (`k < log₂ n` gates, or footprint `≤ n−2`); full `ACC⁰` has poly-many wide supports ⇒ `survivingCount` large on any live set ⇒ collapse fails = the wall, unchanged. Real unconditional low-correlation bound FOR THE FRAGMENTS. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundedSurvival` |
| **bounded-overlap (disjoint-support) cell collapse — N-Frame route discharged again** | The bounded-overlap regime at its clean extreme (pairwise-disjoint supports, overlap 0); works even when supports cover all `n` variables (unlike small-footprint). **`disjoint_supports_forces_cellCollapse`** — pairwise-disjoint supports + some `|S_{j₀}| ≥ 3` ⇒ `FullACC0ForcesCellCollapse` (live set `S_{j₀}`; only it meets itself so `survivingCount = 1`, `2^1 = 2 < |S_{j₀}|`; survivor filter `= {j₀}` via `not_disjoint_iff` + `card_pos`). **`disjoint_supports_low_holonomy_correlation`** — compose with the proved bridge (`nframe_route`): predictor does NOT correlate with the holonomy parity, unconditionally, no socket. Honest: overlap-0 (disjoint) only; degree-`d` overlap (`d ≥ 2`) is NOT forced into collapse by the overlap bound alone (`≤ d·|L|` supports meet any `L` ⇒ `2^{d·|L|} < |L|` impossible) — `d ≥ 2` needs a probabilistic restriction (second-moment cell bridge, socketed in `bounded_overlap_acc0_low_correlation_whp`), the frontier. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0DisjointCollapse` |
| **the N-Frame ACC⁰ lower bound, stated beside Williams — one socket, bridge proved** | Packages the whole N-Frame route as ONE conditional theorem (Williams = two sockets; N-Frame = one, since collapse ⇒ low correlation is already proved). `PredictorClass ι n := ι → Σ k, Fin k → Finset (Fin n)`; **`NFrameCellCollapse sys`** = the hard open socket (every predictor's supports collapse on some live set); **`ACC0HolonomyLowerBound sys tops`** = the conclusion (every predictor fails to correlate with some holonomy parity). **`nframe_acc_lower_bound`** (HEADLINE, proved): `NFrameCellCollapse sys ⇒ ACC0HolonomyLowerBound sys tops` (one-socket reduction via `nframe_route` pointwise; N-Frame analogue of `williams_route_reduces_to_two_sockets`). **`nframe_lower_bound_disjoint`** — the socket DISCHARGED for disjoint-support classes ⇒ UNCONDITIONAL N-Frame lower bound (conditional not vacuous). Honest: the socket is the open `NP ⊄ ACC⁰`-strength content — discharged for bounded fragments, FALSE for arbitrary dense overlapping supports (the wall); genuine open statement = cell collapse for real `ACC⁰` under restriction (the switching lemma). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0NFrameLowerBound` |
| **`collapse_lifts_through_layer` — cell collapse composes under a survivor budget** | The composition direction of the N-Frame route: stacking a layer appends its supports (`Fin.append`). **`survivingCount_append`** — survivor counts ADD across the layer (`survivingCount (append supp₁ supp₂) L = survivingCount supp₁ L + survivingCount supp₂ L`; `finSumFinEquiv` + `Fintype.sum_sum_type` + `Fin.append_left/right` + `card_filter`). **`collapse_lifts_through_layer`** (`2^{s₁+s₂} < |L| ⇒ CellCollapse (append) L`). **`collapse_lifts_of_budget`** (controlled-parameter form: layer survivors `≤ δ`, base slack `2^{s₁+δ} < |L|` ⇒ lift). **`full_collapse_lifts`** (packaged as `FullACC0ForcesCellCollapse (append …)`). Honest: collapse composes ADDITIVELY in survivors (multiplicatively in cell count), so it lifts only when the new layer adds FEW survivors (budget `δ`, `s₁+δ < log₂|L|`); a wide `MOD` layer surviving on most of `L` blows the budget = the wall. Supplying the small budget for a real `ACC⁰` layer under restriction = the switching lemma (blocked for leaf-switching by the proved `MOD` no-go). Proves collapse composes + lifts under budget; does NOT supply the budget for full `ACC⁰`. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CollapseLift` |
| **rank-based cell collapse — the sharper collapse (rank, not survivor count)** | For overlapping supports many gates survive but induce few distinct cells; the cell count is governed by the `F₂`-RANK of the support incidence. **`incidenceVec`/`survivorIncidence`/`supportRank`** (`F₂` incidence vectors of surviving supports + dim of their span, `Set.finrank`). **`supportRank_le_survivingCount`** (rank ≤ #generators, via `finrank_span_finset_le_card` + `card_image_le`). `RankCellCollapse supports L := 2^{supportRank} < |L|` (sharp). **`cell_collapse_implies_rank_collapse`** (`CellCollapse ⇒ RankCellCollapse` — correct direction; rank ≤ survivors ⇒ rank collapse is WEAKER / more achievable; the rank→cell direction is the flip, false in general). **`FullACC0ForcesRankCollapse`** (weaker socket) + **`full_cell_collapse_implies_full_rank_collapse`** (survivor socket ⇒ rank socket). Honest: the rank route WEAKENS the open socket and is the correct cell count for `MOD₂`/overlapping supports (`#parity cells = 2^rank = parity_reachable_card`, `…ACC0ParityRankCardinality`). Genuine next target = sharp bridge `RankCellCollapse ⇒ low correlation` (pigeonhole with `#cells ≤ 2^rank`), NOT from composing the survivor bridge. Forcing `supportRank < log₂|L|` for real `ACC⁰` = the rank-flavoured switching lemma, open `NP ⊄ ACC⁰`-strength. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RankCollapseRoute` |
| **the sharp rank bridge: 2^rank < |L| ⇒ low holonomy correlation** | A GENUINE theorem (no socket) — the correlation bridge with the sharp RANK cell count, not the crude survivor count. `cellPatternVec supports v := fun j => if v∈supports j then 1 else 0` (column of incidence); **`sameCell_iff_pattern`** (`SameCell ⟺ cellPatternVec v = cellPatternVec w`); `cellSpan`/`cellRank` (F₂-span of cell patterns over L + its dim); **`cellPattern_image_card_le`** (#distinct cell patterns `≤ 2^cellRank` — patterns ⊆ span, `|span| = 2^finrank` via `Module.card_eq_pow_finrank` + `ZMod.card`, the `parity_reachable_card` technique); **`exists_sameCell_pair_of_rank`** (`2^cellRank < |L|` ⇒ two live coords share a cell, pigeonhole); **`rank_collapse_low_correlation`** (THE SHARP BRIDGE: `2^cellRank < |L| ⇒ LowHolonomyCorrelation`, via `CellWitness` + the proved `cellWitness_gives_low_correlation`). Strictly sharper than the survivor bridge: `cellRank` (column rank) `≤ survivingCount` (row count), far smaller for overlapping supports. Self-contained, no socket. Open content unchanged: FORCING `cellRank < log₂|L|` for real `ACC⁰` under restriction = the rank-flavoured switching lemma (`NP ⊄ ACC⁰`-strength). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP`  **Cleanup (proved): the rank bridge strictly subsumes the survivor bridge** — `cellPatternVec_mem_survivorSpan` (a cell pattern lies in the survivor-singles span, vanishing off survivors), `cellRank_le_survivingCount` (column rank ≤ row count, via `Submodule.finrank_mono` + `finrank_span_finset_le_card`), `survivor_collapse_implies_rank_collapse` (`2^survivingCount < |L| ⇒ 2^cellRank < |L|`). The full hierarchy is now machine-checked: few survivors ⇒ low rank ⇒ low cell count ⇒ same-cell witness ⇒ low holonomy correlation. | `…ACC0RankBridge` |
| **low-rank fragment of `acc0_restriction_forces_low_cellRank` — rank wins, survivors lose** | Discharges the rank socket for low-rank systems the survivor route cannot touch. `ACC0ForcesLowCellRank supports := ∃ L, 2^{cellRank} < |L|`; **`low_cellRank_low_correlation`** (socket ⇒ low correlation, ▸ the proved rank bridge); **`bounded_cellRank_univ_forces`** (`2^{cellRank univ} < n ⇒` socket); **`equal_supports_cellRank_le_one`** (equal supports ⇒ `cellRank ≤ 1`, patterns ∈ span{𝟙}, INDEPENDENT of gate count `k`); **`equal_supports_low_correlation`** (equal supports, any `k`, `n ≥ 3` ⇒ predictor fails to correlate, UNCONDITIONAL). Punchline: equal supports = all `k` gates survive (`survivingCount = k`, survivor route powerless), yet rank `≤ 1` so the rank route still gives the bound — proof the rank reformulation strictly strengthens. Honest: a fragment; general low-rank under restriction = open. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0LowRankFragment` |
| **random restriction toward low cell rank — probabilistic stepping stones** | Transfers the `p`-biased survivor concentration to cell RANK via pointwise `cellRank ≤ survivingCount`. **`expected_cellRank_le_expected_survivors`** (`Exp p (cellRank) ≤ Exp p (survivingCount)`, monotone expectation); **`randomRestriction_forces_low_cellRank`** (expected survivors `≤ B < a ⇒ ∃ L, cellRank < a`, via `exists_low_survival` + `cellRank ≤ survivingCount`). Honest: stepping stones — give `cellRank < a` (real threshold); the socket needs `2^{cellRank} < |L|` (`cellRank < log₂|L|` with `|L|` large simultaneously) = the open rank switching lemma. Supplies the probabilistic inputs (bounded-overlap `E[survivors]` bound ⇒ small `E[cellRank]` + low-rank `L`). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RandomRestrictionRank` |
| **bounded-fan-in instantiation: low-cell-rank live set + the exact |L|-balance gap** | Instantiates the probabilistic rank machinery with the proved first-moment bound `exp_survivingCount_le` (`Exp p (survivingCount) ≤ k·s·p`). **`boundedFanin_forces_low_cellRank`** (fan-in `≤ s`, `k·s·p < a` ⇒ `∃ L, cellRank supports L < a`); **`heavy_restriction_forces_rank_zero`** (`k·s·p < 1` ⇒ `∃ L, cellRank = 0`). Honest: supplies the LOW-RANK half of the socket unconditionally for bounded fan-in (`cellRank < a`, real); does NOT close `2^{cellRank} < |L|` — the gap is precise, the Markov live set is NOT guaranteed large (`L = ∅` has `survivingCount = 0`, `cellRank = 0`, but `|L| = 0`, so socket fails). Need `L` simultaneously low-rank AND large (`|L| > 2^{cellRank}`) — the heavy-vs-light restriction tension, requiring two-sided concentration (lower-tail on `|L|`, not yet in corpus) + the structural rank input for general `ACC⁰` = the open rank-flavoured switching lemma. Pins exactly that balance. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundedOverlapRank` |
| **the rank whp route — two-event intersection with the rank tail (subsumes survivor whp)** | The rank version of `bounded_overlap_predictor_fails_whp`, with strictly weaker feasibility. **`Pr_mono`** (`E ⊆ F ⇒ Pr E ≤ Pr F`, `sum_le_sum_of_subset_of_nonneg`); **`rank_predictor_fails_whp`** (`2^a ≤ b ∧ Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1 ⇒ LowHolonomyCorrelation`, via `exists_both_of_pr_add_lt_one` ⟶ `2^{cellRank} < |L|` ⟶ sharp rank bridge); **`rank_feasibility_le_survivor`** (`Pr[cellRank ≥ a] + Pr[|L| ≤ b] ≤ Pr[survivingCount ≥ a] + Pr[|L| ≤ b]`, since `{cellRank ≥ a} ⊆ {survivingCount ≥ a}`); **`rank_whp_of_survivor_feasible`** (survivor feasibility `< 1` ⇒ rank route fires — STRICTLY SUBSUMES the survivor whp theorem). The two-event intersection (low-rank ∧ large-`L`) now uses the *rank* tail. Honest: the feasibility `Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1` with `2^a ≤ b` is still the open balance for poly-many overlapping gates (bounding `Pr[cellRank ≥ a]` = the structural rank input). Sharpest whp reduction; does not close it. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RankWhp` |
| **structured case of ACC0ForcesLowCellRank — bounded distinct supports** | Discharges the rank socket for ≤ `d` distinct supports, regardless of gate count `k`. `classVec supports T := fun j => if supports j = T then 1 else 0` (support-class indicator); **`cellPatternVec_mem_classSpan`** (cell pattern ∈ span of the `≤ d` class indicators — constant on each support-class, `∑_T (v∈T)·classVec T` via `sum_eq_single_of_mem`); **`cellRank_le_distinct`** (`cellRank ≤ |image supports|`); **`bounded_distinct_forces_low_cellRank`** (`|image| ≤ d ∧ 2^d < n ⇒ ACC0ForcesLowCellRank`); **`bounded_distinct_low_correlation`** (⇒ predictor fails, unconditional, any `k`). Generalizes equal supports (`d=1`); survivor route powerless (`survivingCount = k`), rank route wins (`cellRank ≤ d`). Honest: a fragment — general `ACC⁰` has poly-many *distinct* wide supports (`d` large, `2^d > n`). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundedDistinctRank` |
| **low-dimensional support-span ⇒ low cell rank — the natural next N-Frame theorem** | Generalizes bounded-distinct by bounding cell rank via the `F₂`-DIMENSION of the support indicators. `SupportsInRankSpan supports r := ∃ B c, ∀ j i, (i ∈ supports j) = ∑_m c j m · B m i` (indicators are `F₂`-combos of `r` fixed vectors); **`cellRank_le_of_span`** (`SupportsInRankSpan r ⇒ cellRank ≤ r`; `cellPatternVec v = ∑_m (B m v)·(c_·m)` ∈ span of `r` coefficient vectors — the column-rank `≤` row-rank bound made CONSTRUCTIVE via explicit coefficients, no abstract row=col rank); **`supportSpan_forces_low_cellRank`** (`SupportsInRankSpan r ∧ 2^r < n ⇒ ACC0ForcesLowCellRank`); **`supportSpan_low_correlation`** (⇒ predictor fails, unconditional, any `k`). Sharpest structured rank fragment: caps `cellRank` by the support-family *dimension*, subsuming bounded-distinct (`r ≤ #distinct`) and equal supports (`r = 1`). Honest: a fragment — general `ACC⁰` indicators span high dimension (`r ~ poly`, `2^r > n`); bounding support-span dim under restriction = the open rank switching lemma. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0SupportSpanRank` |
| **rank growth through layers — `cellRank` is subadditive under `append`** | The depth-direction rank composition law. `embedFst`/`embedSnd` (`F₂`-linear inclusions `Fin k_i → Fin(k₁+k₂)` extending by zero; `map_add'`/`map_smul'` via `Fin.addCases` + `Fin.append_left/right`); `cellPatternVec_append_eq` (append pattern = `embedFst p₁ + embedSnd p₂`); **`cellRank_append_le`** (`cellRank (append supp₁ supp₂) L ≤ cellRank supp₁ L + cellRank supp₂ L`; `cellSpan(append) ≤ map embedFst cellSpan₁ ⊔ map embedSnd cellSpan₂`, `finrank_sup_add_finrank_inf_eq` + `Submodule.finrank_map_le`); **`rank_collapse_lifts_of_rank_budget`** (`2^{r₁+r₂} < |L| ∧ cellRank₁ ≤ r₁ ∧ cellRank₂ ≤ r₂ ⇒ 2^{cellRank(append)} < |L|`). Turns depth composition into RANK-budget accounting (vs survivor-budget): a layer adding only `r₂` observer degrees of freedom keeps composite rank `≤ r₁+r₂` — the sharpened analogue of the survivor `collapse_lifts_through_layer`. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP`  **(also re-exported in `…ACC0FrontierSummary` as `rank_append_subadditive` / `rank_collapse_lifts_budget`).** | `…ACC0RankComposition` |
| **direct cell-count collapse route — the sharpest observer collapse (cells, not rank)** | The collapse keyed on the actual number of observer cells, strictly generalizing the rank route. `cellPatternImage`/`cellPatternCount`; `CellCountCollapse supports L := cellPatternCount < |L|`. **`exists_sameCell_pair_of_count`** (bare pigeonhole, no rank bound); **`cellCountCollapse_implies_low_correlation`** (`CellCountCollapse ⇒ LowHolonomyCorrelation`); **`rank_collapse_implies_cellCount_collapse`** (`2^{cellRank} < |L| ⇒ CellCountCollapse`, since `cellPatternCount ≤ 2^{cellRank}` — SUBSUMES the rank route). Hierarchy: few survivors ⇒ low rank ⇒ few cells ⇒ same-cell witness ⇒ low correlation. Open target sharpens to `ACC0ForcesLowCellCount`. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCountRoute` |
| **chain (nested) supports — few cells even at full rank** | The class the rank route misses: nested supports `S_1 ⊆ … ⊆ S_k` have FULL rank but `≤ k+1` cell patterns. `ChainSupports`/`suppSet`; **`suppSet_comparable`** (chain membership sets pairwise comparable, by_contra + chain comparability); `oneSet_eq_suppSet`/`cellPatternVec_eq_of_suppSet` (pattern↔membership dictionary); **`chain_cellPatternCount_le`** (`ChainSupports ⇒ cellPatternCount ≤ k+1`; card map injective on comparable patterns via `card_le_card_of_injOn` + `eq_of_subset_of_card_le`); **`chain_low_correlation`** (`ChainSupports ∧ k+1 < |L| ⇒ LowHolonomyCorrelation`, regardless of rank). The honest correction: for nested/laminar, cell COUNT (not rank) is the right observer invariant. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0ChainCellCount` |
| **clustered supports — `cellRank ≤ d + r` (corollary of support-span)** | Clustered = `d` cluster centers + `r`-dim variation: `(i∈supports j) = ∑ cc·center + ∑ cv·V`. **`ClusteredSupports`**; **`clustered_supports_in_span`** (⇒ `SupportsInRankSpan supports (d+r)`; `B = append center V`, `c = append cc cv`, `finSumFinEquiv` sum-split + `Fin.append_left/right`); **`clustered_supports_low_rank`** (`cellRank ≤ d+r` via `cellRank_le_of_span`); **`clustered_low_correlation`** (`2^{d+r} < n ⇒` low correlation, any `k`). Caps observer rank by `#clusters + variation rank`; subsumes bounded-distinct (`r=0`) and equal supports (`d=1,r=0`). A cheap genuine corollary. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0ClusteredRank` |
| **cell-count composition — `cellPatternCount` submultiplicative under `append`** | The cell-count analogue of rank composition. **`cellPatternVec_append`** (append pattern = concatenation `Fin.append (cPV A v)(cPV B v)`); **`cellPatternCount_append_le`** (`cellPatternCount (append A B) L ≤ cellPatternCount A L * cellPatternCount B L`; concatenation injective ⇒ `image ⊆ (img_A ×ˢ img_B).image append`, `card_image_le` + `card_product`); **`cellCount_collapse_lifts`** / **`cellCount_collapse_of_budget`** (`c₁·c₂ < |L| ⇒ CellCountCollapse (append A B) L`). Depth composition MULTIPLIES cell counts (vs additive survivor, subadditive rank). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCountComposition` |
| **full cell-count switching socket — `FullACC0ForcesLowCellCount ⇒ holonomy LB`** | The SHARPEST (weakest, most achievable) N-Frame switching socket. **`FullACC0ForcesLowCellCount supports := ∃ L, cellPatternCount supports L < \|L\|`** (the open socket); **`nframe_cellcount_route`** (socket ⇒ `LowHolonomyCorrelation`, proved bridge); **`cellCollapse_implies_lowCellCount`** (survivor socket ⇒ cell-count socket, since `cellPatternCount ≤ 2^cellRank ≤ 2^survivingCount` — it is the WEAKEST socket); **`NFrameLowCellCount`** / **`nframe_cellcount_lower_bound`** (over a predictor class, socket ⇒ `ACC0HolonomyLowerBound`); **`nframe_lowCellCount_of_cellCollapse`** (survivor class-socket ⇒ cell-count class-socket — NOT vacuous, every disjoint/bounded discharge carries over). The official final target. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCountSwitching` |
| **low VC dimension ⇒ few observer cells (Sauer–Shelah)** | The cell patterns ARE the gate-membership sets `{suppSet v : v ∈ L} ⊆ 2^(Fin k)`, so cell count = set-family size, bounded by Sauer–Shelah. The common generalization of bounded-distinct/clustered/laminar — *few observer patterns, not low rank* (the N-Frame observer idea). **`cellVCdim supports L`** := `(L.image (suppSet supports)).vcDim`; **`patternFamily_card`** (`\|{suppSet v}\| = cellPatternCount`, one-set bijection + `card_image_of_injOn`); **`lowVC_cellPatternCount_le`** (`cellVCdim ≤ d ⇒ cellPatternCount ≤ ∑_{i≤d} C(k,i)`, Mathlib Pajor `card_le_card_shatterer` + Sauer–Shelah `card_shatterer_le_sum_vcDim`); **`lowVC_cellCountCollapse`** / **`lowVC_low_correlation`** (`∑_{i≤d} C(k,i) < \|L\| ⇒` collapse ⇒ low corr). Converts `ACC0ForcesLowCellCount` to "bound observer VC under a restriction" for wide overlapping `MOD`. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0VCCellCount` |
| **laminar (nested-or-disjoint) supports — `≤ k+1` cells** | Generalizes chains: any two supports nested OR disjoint, still `≤ k+1` cells despite possibly full rank. **`LaminarSupports`**; **`chain_isLaminar`** (chains ⊂ laminar); **`laminar_suppSet_eq`** (for `⊆`-minimal-card `j∈suppSet v`, `suppSet v = {i : supports j ⊆ supports i}` the up-set); **`laminar_cellPatternCount_le`** (every pattern is an up-set indicator or `∅`, `≤ k+1`; `card_le_card_of_injOn` into `insert ∅ (univ.image U)`, `exists_min_image`); **`laminar_low_correlation`** (`k+1 < \|L\|` ⇒ low correlation, regardless of rank). A genuine strengthening — the cardinality-injection trick of chains fails (laminar `suppSet`s not pairwise comparable). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0LaminarCellCount` |
| **block-product supports — cell count is the PRODUCT of per-block counts** | `m` blocks of `b` gates (`supports : Fin m → Fin b → Finset (Fin n)`); cell count multiplies. **`blockCellCount`** / **`flatSupports`** (flattened to `Fin (m·b)` via `finProdFinEquiv`); **`blockCellCount_le_prod`** (`≤ ∏ i, cellPatternCount (supports i) L`; tuple map ↪ `Fintype.piFinset`, `Fintype.card_piFinset`); **`blockCellCount_le_pow`** (each block `≤ c` ⇒ `≤ cᵐ`); **`cellPatternCount_flat_eq`** (flattening = gate relabelling, `finProdFinEquiv` bijection ⇒ same cells); **`block_product_low_correlation`** (`∏ < \|L\|` ⇒ low correlation). The `m`-fold generalization of `cellPatternCount_append_le`. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BlockProductCellCount` |
| **boundary-observer control — the boundary selects the observer (dynamic N-frame unification)** | Formalizes "observer is not a fixed mechanism; the boundary/context selects it", routing the proved routes by gate boundary, each grounded in a proved fact. **`GateKind`** (andOr/mod q/symmetric), **`BoundaryContext`** (absorbing/linearResidual/polynomialSpan/countingState), **`boundarySelect`**; **`boundarySelect_andOr_iff_absorbing`** (absorbing ⟺ AND/OR); **`andOr_boundary_absorbing`** (AND has absorbing value); **`mod_boundary_not_absorbing`** (MOD constant iff support fully fixed); **`mod_observer_reduces_to_membership`** (linearResidual = membership, bounded); **`mod_polynomial_observer_separates`** (polynomialSpan separates the MOD target); **`counting_state_cashes_out`** (countingState → Williams cash-out). Unification/routing layer, NOT new hard content. The countingState observer is realised concretely in `…ACC0OracleControl` (`oracle_control_over_mod_searchable`: few-MOD fragment SAT-searchable `< 2ⁿ`); open rung `random_restriction_makes_control_shallow` = the state-shrinkage. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0BoundaryObserverControl` |
| **Williams cash-out from the polynomial method (CONDITIONAL, representation half discharged)** | Williams' `ACC⁰`-SAT algorithm = representation (sparse `SYM∘AND`) + counting (sub-`2ⁿ`). **`RSMonoANDRepresentation`** / **`rsMonoANDRepresentation_proved`** — the representation half (1) DISCHARGED by the polynomial method (re-export of `lowDegPolyEval_mem_monoAND_span`: degree-`≤D` poly eval ∈ monoAND span). **`williams_cashout_skeleton`** — the Williams skeleton with representation factored out. **`williams_cashout_from_polynomial`** — same chain with `hrep` SUPPLIED by the polynomial method, leaving only the **counting** socket (rep ⇒ sub-`2ⁿ` SAT, Beigel–Tarui/Williams algorithmic heart), the **Williams** collapse, and the **time hierarchy** as inputs. Proves the IMPLICATION, NOT the separation; faithful account of which inputs close `NEXP ⊄ ACC⁰` and which the polynomial method supplies. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0WilliamsCashoutFromPolynomial` |
| **PIVOT to the polynomial method — exact effective-dimension separation** | Lands the polynomial method on the SAME target the observer route could not collapse (`fParity univ`). **`lowDegree_poly_ne_holonomy_parity`** (NEW): a polynomial of total degree `< n` cannot equal the holonomy parity `x ↦ ∏ᵢ pmOne(xᵢ)` on the cube — its evaluation `∈ V_D` (`eval_mem_lowDegSpan`), which the holonomy parity escapes (`holonomy_parity_not_lowDegEval`, effective dim `≥ n`). The DIMENSION analogue of the observer's swap-invariance — and unlike the observer route it bites on `MOD`. **`holonomy_parity_escapes_lowDegSpan`** (re-export); **`observer_route_no_escape_for_mod`** (re-export: the ceiling bypassed). Quantitative `AC⁰[p]` size `2^{Ω(n^{1/2d})}` = `…Layer3NFrameParityRS.nframe_parity_target_size_lower_bound`. Honest `F_p` ceiling: real `PARITY/MOD_p ∉ AC⁰[p]`; composite/general = Williams. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0PivotToPolynomialMethod` |
| **MOD gate semantics + residual observer reduces to membership (the ACC⁰ battlefield)** | Grounds the `MOD` no-go in gate SEMANTICS and proves the residual observer can't escape. Part A: **`effVal`/`parityVal`/`ParityConstant`**; **`parity_constant_iff_support_fully_fixed`** (a parity gate is constant under `ρ` IFF support entirely fixed — forward = the no-absorbing-value statement); **`and_constant_of_absorbing`** (contrast: `AND` deactivated by one fixed-`false` input — `AND` has an absorbing value, parity has none = why `AC⁰` switches, `ACC⁰` doesn't). Part B: **`residualSignature`** (free summand iff free ∧ in support); **`residual_eq_membership_of_free`** (free coord: residual signature = membership pattern); **`residual_merge_iff_sameCell`** (free coords merge under residual observer IFF share membership cell); **`residualPatternCount_eq_membership_on_free`** (residual count = membership count); **`residual_no_escape_in_hardRegime`**. CONCLUSION: a coordinate's affine contribution to a linear gate IS its membership ⇒ residual observer = membership observer on free coords ⇒ inherits the hard-regime ceiling ⇒ the ENTIRE observer/merging programme is membership-bounded for `MOD` ⇒ `ACC⁰` needs the polynomial method. NEGATIVE/localization result. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0MODResidualObserver` |
| **MOD no-go — variable-fixing merging is INERT for symmetric gates** | A `MOD` gate has NO absorbing value (constant iff support ENTIRELY fixed), so **`MODGateActive ρ supports j := ∃ i ∈ supports j, ρ i = none`** (active iff it reads a free input). **`mod_separating_gate_active`** (a gate separating two FREE coords contains one of them ⇒ always active ⇒ can never be deactivated); **`modRefined_eq_membership_of_free`** (free coord: `MOD`-refined pattern = membership pattern — no gate drops out); **`mod_refined_merge_iff_sameCell`** (two free coords share a `MOD`-refined cell IFF a membership cell — NO merging gain); **`mod_no_collapse_in_hardRegime`** (distinct free coords never merge). Proves the `AND`/`OR` absorbing-value merging that powers the refined route is inert for `MOD` — exactly why `AC⁰` switches but `ACC⁰` does not. Pins the obstruction to `MOD`'s lack of an absorbing value. A NEGATIVE/localization result, NOT an `ACC⁰` lower bound. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0MODNoGo` |
| **richer variable-fixing observer model — restriction CAN merge** | The model the membership ceiling demanded. `Restriction n := Fin n → Option Bool` (`none`=free); `AND`-of-positive-literal gates become CONSTANT when an input is fixed-`false`, so a gate drops out even while reading a free coord — the merge membership couldn't do. **`Restriction`/`freeSet`/`GateActive`** (no fixed-false input ∧ has free input)/**`refinedCellPatternVec`** (membership over ACTIVE gates only)/**`refinedCellPatternCount`/`RefinedCellCollapse`**; **`exists_sameRefinedCell_of_collapse`** (pigeonhole); **`refined_merge_of_inactive_separators`** (THE new power: coords separated only by inactive gates merge); **`refined_strictly_beats_membership`** (concrete `n=3,k=1`, gate `{0,2}`, fix coord 2 false: `¬ CellCountCollapse` membership ∧ `RefinedCellCollapse` refined — strict gain over the proved ceiling). **`refinedWeightVec`** (support-count on active gates, 0 on inactive); **`refined_mem_of_eq`** (equal refined patterns ⇒ membership agrees on active gates); **`refinedWeightVec_pairSwap`** (refined-same-cell swap preserves the statistic); **`RefinedLowCorrelation`** / **`refinedCellCollapse_implies_refinedLowCorrelation`** (the CORRELATION BRIDGE, via the generic `low_correlation_of_pres`). OPEN (the genuine ACC⁰ wall): `MOD`/symmetric gates have NO absorbing value (constant only when support fully fixed) ⇒ this AND/OR-style merging is weak for `MOD` (AC⁰ switches, ACC⁰ doesn't). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RefinedObserverModel` |
| **EXACT characterization of the cell-count socket — false in the hard regime** | `cellPatternVec` is `L`-INDEPENDENT, so two live coords collapse iff their FULL patterns are equal, and any separating gate contains one of them so always SURVIVES ⇒ a restriction CANNOT merge patterns (only drops coords). **`globalCellCount_le_n`** (`≤ n`); **`forcesLowCellCount_iff_global_lt`** (`FullACC0ForcesLowCellCount ↔ globalCellCount < n`); **`forcesLowCellCount_iff_not_injective`** (`↔ ¬ Injective (cellPatternVec supports)`); **`not_forcesLowCellCount_of_hardRegime`** (`HardRegime univ ⇒ ¬ FullACC0ForcesLowCellCount`, since hard ⇒ `globalCellCount = n` = injective). HONEST CEILING: the route fires EXACTLY when two coords already share a global pattern (`2^k<n` pigeonhole / structured fragments force it); FALSE in the hard regime. `StructuredOverlappingMOD ⇒ collapse` is a FALSEHOOD for genuinely-hard families. Restriction-merging needs a RICHER model (fixing vars ⇒ gates constant). NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCountCharacterization` |
| **sunflower (common-core) supports — wide overlap, `≤ k+2` cells** | `supports j = core ∪ petal j` with pairwise-disjoint petals: every pair OVERLAPS in the core (NOT laminar — `supports i ∩ supports j = core ≠ ∅`, neither nested). **`SunflowerSupports`**; **`sunflower_suppSet_core/_petal/_empty`** (patterns are `univ`, `{j₀}`, or `∅`); **`sunflower_cellPatternCount_le`** (`≤ k+2`; image `⊆ insert univ (insert ∅ (univ.image singleton))`); **`sunflower_low_correlation`** (`k+2 < \|L\| ⇒` low corr, regardless of rank/survivors). Genuine wide-overlap-⇒-few-patterns fragment outside laminar/low-rank. General overlapping `MOD` need not be sunflower-structured (can shatter) = the wall. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0SunflowerCellCount` |
| **hard-regime reduction — exactly where the open lemma lives** | **`HardRegime supports L`** := `\|L\| ≤ 2^{survivingCount L} ∧ \|L\| ≤ globalCellCount` (both general collapse bounds fail). **`collapse_of_not_hardRegime`** (outside ⇒ `CellCountCollapse`, via survivor route ∨ global route); **`full_of_hardRegime_resolved`** (`HardRegime univ → Full ⇒ Full`: the hard regime is the ONLY obstruction); **`hardRegime_univ_of`** (the realistic regime `n ≤ 2^{surv univ}`, `n ≤ globalCellCount` IS hard). A reduction isolating the open content (`cellPatternCount L < \|L\|` while both bounds fail = the merged-count concentration on surviving gates), not a resolution. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0CellCountHardRegime` |
| **direct cell-count concentration — not via `2^{survivors}`** | `cellPatternVec` is INDEPENDENT of `L` (ranges over all gates), so cell count = distinct patterns among live coords, monotone in `L`, bounded by restriction-independent `globalCellCount := cellPatternCount supports univ ≤ 2^k`. **`cellPatternCount_le_card`** (`≤ \|L\|`); **`cellPatternCount_mono`** / **`cellPatternCount_le_global`** / **`globalCellCount_le_two_pow_gates`**; **`Pr_cellPatternCount_ge_le_size_tail`** (`Pr[≥a] ≤ Pr[\|L\|≥a]`, no `2^surv`); **`Pr_cellPatternCount_ge_eq_zero_of_global_lt`**; **`expected_cellPatternCount_le_global`** (`Exp ≤ globalCellCount`, direct first moment); **`low_global_cellCount_collapse`** / **`low_global_forces_lowCellCount`** / **`few_gates_forces_lowCellCount`** (deterministic: `globalCellCount<\|L\|`, resp `<n`, resp `2^k<n` ⇒ collapse, NO probability). HONEST WALL: `globalCellCount` is restriction-independent, generically `=n` for `k≫log n`; the restriction's real power is MERGING patterns among surviving gates (`cellPatternCount L ≪ globalCellCount`), and bounding that merged count below both `2^surv` and `\|L\|`/`globalCellCount` is the open structural-concentration content. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0DirectCellConcentration` |
| **random restriction in cell-count language — first moment, Markov, sharp whp, the precise wall** | The cell-count analogue of the rank random-restriction/whp files, on `ACC0ForcesLowCellCount`. **`cellPatternCount_le_two_pow_cellRank`/`_survivingCount`** (monotone bounds); **`expected_cellPatternCount_le_expected_pow_survivors`** (`Exp[cellPatternCount] ≤ Exp[2^surv]`); **`Pr_cellPatternCount_ge_le_markov`** (`Pr[≥a] ≤ Exp/a`); **`Pr_cellPatternCount_ge_le_pow_survivor`** (proxy `≤ Exp[2^surv]/a`); **`randomRestriction_forces_low_cellCount`** (`Exp ≤ B < a ⇒ ∃ L, cellPatternCount < a`); **`cellCount_predictor_fails_whp`** (two-event balance, needs only `a ≤ b` — SHARPER than rank's `2^a ≤ b`); **`cellCount_whp_subsumes_rank`** (rank feasibility `2^a≤b` ⇒ cell-count fires — broadest whp); **`expected_cellPatternCount_le_of_bound`** + **laminar (`≤k+1`)** + **bounded-distinct (`≤2ᵈ`)** + **block-product (`≤cᵐ`)** discharges. HONEST WALL: first moment closes only for deterministic-bound structures; general wide overlapping `MOD` has only the exp-weak `Exp[2^surv]` handle — closing the gap needs structural concentration on the distinct-pattern count = the open switching lemma. NOT `NEXP ⊄ ACC⁰`, NOT `P ≠ NP` | `…ACC0RandomRestrictionCellCount` |
| **integer-polynomial CRT decode (the exact *back half* of Beigel–Tarui)** | The integer count polynomial is `gateCount g x` (`…ACC0SymmetricObserver`: the exact `ℕ`-valued count of accepting sub-gates). For a pairwise-coprime family `qs : List ℕ` with `M = qs.prod`: **`count_crt_iff`** (`gateCount g x ≡ t [MOD qs.prod] ↔ ∀ i, gateCount g x ≡ t [MOD qs.get i]`, the Chinese Remainder Theorem for the count, via `Nat.modEq_list_prod_iff`); **`modCount_factors_through_resVec`** (the exact `MOD_{qs.prod}` count decision `decide (gateCount ≡ t [MOD qs.prod])` equals a fixed `G (countResVec qs g x)` where `countResVec qs g x i = (gateCount g x : ZMod (qs.get i))` — CRT collapses the modulus, `ZMod.natCast_eq_natCast_iff` turns each `≡ t [MOD q_i]` into a residue equation); **`modCount_observed`** (so the decision is `ObservedBy` the residue vector); **`countResVec_card_le`** (`|image(countResVec)| ≤ qs.prod`, landing in `∏_i ZMod (qs.get i)` of card `∏_i qs.get i = qs.prod` via `List.prod_ofFn`/`List.ofFn_get` + `ZMod.card`); **`count_crt_sat_speedup`** (`qs.prod < 2^n ⇒` SAT of the decision decided by a `< 2^n` residue-cell search); **`mod6_count_crt_speedup`** (the concrete `M = 6 = 2·3` split, `[2,3]`, searchable in `≤ 6` cells). This is the Beigel–Tarui CRT decode generalised from the fixed `mod6_eq_mod2_and_mod3` (`…Layer3MixedModulus`) to an arbitrary squarefree `M = ∏ q_i`, and attached to the **count polynomial** rather than one `MOD`-gate's support count. Honest: this is the **exact back half only** — CRT decodes from the *exact* count `gateCount`; it does **NOT** turn *approximate* RS residues (each correct on `1-ε` over its own prime field) into an exact decision (the CRT combination is correct only where all approximants are, still approximate). So it does *not* close the approximate/exact gap; that gap is the *front half* — **Wall 1**, `ACC⁰ → exact low-degree integer polynomial across depth` (`MixedACCDepthReductionSocket`/`HasExactSymAndForm`). A `< 2^n` cell count is still not a uniform algorithm (Wall 2) | `…ACC0IntegerPolynomialCRT` |
| **toy *exact-and-quasipolynomial* `SYM∘AND` (depth-2 bounded-fan-in DNF)** | The single restricted fragment where *exact* and *quasipolynomial* hold **simultaneously** — the property the general `ACC⁰` wall (Wall 1) provably cannot have. For a depth-2 `OR ∘ AND_w` DNF (`mono : Fin m → Finset (Fin n)` injective, `∀ j, (mono j).card ≤ w`): **`dnf_exact_symAnd`** (`(fun x => decide (∃ j, monoAND (mono j) x = true)) = symEval (fun j x => monoAND (mono j) x) (fun k => decide (1 ≤ k))` — the DNF **is** the symmetric count gate `[count ≥ 1]` over its bottom `AND`s, *exactly*, via `or_exact_sym`); **`dnf_bottom_count_le`** (`m ≤ ∑_{i≤w} C(n,i)` — distinct bottom `AND`s of fan-in `≤ w` are distinct degree-`≤w` monomials, `n^{O(w)}`, quasipoly for `w = polylog n`, via `monomial_count_le`); **`dnf_exact_quasipoly_searchable`** (**both at once**: the exact `SYM∘AND` identity *and*, once `(∑_{i≤w} C(n,i)) + 1 < 2^n`, SAT-searchable in `< 2^n` cells via `or_exact_searchable`, since `m + 1 ≤ (∑_{i≤w}C(n,i)) + 1 < 2^n`). Why the wall lifts *here* and exactly here: a bottom `AND` of fan-in `≤ w` (`monoAND`) **is** the degree-`≤w` monomial — a *genuine* `AND` gate, no approximation, so bounded fan-in keeps the degree bounded *exactly*; the top `OR` is *exactly* `[count ≥ 1]`. Honest: this holds **only** for the depth-2 bounded-fan-in `DNF` fragment. It does not extend to *unbounded* fan-in `AND` (degree = fan-in, up to `n`), the `MOD` layer (needs the RS *approximation* for low degree), or *arbitrary depth* (degree multiplies) — those are exactly where exactness forces exponential size (the front half of Beigel–Tarui, Wall 1). Still the cell/observer model; `< 2^n` cells is not a uniform algorithm (Wall 2) | `…ACC0ExactQuasipolyDepth2` |
| **exact-quasipoly fragment + one `MOD` top (`MOD_M ∘ AND_w`)** | Pushes the exact-quasipoly fragment one step toward the YBT normal form: replace the `OR` top with a `MOD_M` top (a genuine `SYM ∘ AND_w` with a modular count top), `M = qs.prod` over pairwise-coprime `qs`. **`modAnd_bottom_count_le`** (bottom `AND_w` quasipoly: `m ≤ ∑_{i≤w} C(n,i)`, `monomial_count_le`); **`modAnd_exact_observed`** (the `MOD_M ∘ AND_w` decision `modCountDecision qs t (monoAND ∘ mono)` factors *exactly* through `countResVec` — the top `MOD_M` is CRT-decoded on the integer count `gateCount`, `…ACC0IntegerPolynomialCRT`, **no approximation**); **`modAnd_exact_quasipoly_searchable`** (both: `m ≤ ∑_{i≤w}C(n,i)` *and* `∃ G`, SAT-searchable in `< 2^n` residue cells once `M = qs.prod < 2^n` — the modular top *compresses* the count to `M` classes, independent of the bottom count); **`mod6_and_exact_quasipoly_searchable`** (`M = 6 = 2·3` concrete, `[2,3]`). Both layers stay **exact**: the bottom `AND` of fan-in `≤ w` *is* the degree-`≤w` monomial (genuine gate), and `MOD` is *exactly* symmetric — it needs no RS approximation, unlike a low-degree polynomial over a single field. So the exact-and-quasipolynomial fragment *does* extend to one `MOD` layer. Honest — exactly where it stops: this is still depth 2 over a **bounded-fan-in** bottom. It does not reach the general YBT normal form (arbitrary `ACC⁰` bottom: unbounded fan-in / interleaved `MOD` / arbitrary depth), where exactness forces exponential size — the front half, **Wall 1**. The exact `MOD` top buys nothing there; it is the *bottom* `AND_w → exact low-degree polynomial across depth` that breaks. Cell/observer model; `< 2^n` cells is not a uniform algorithm (Wall 2) | `…ACC0ExactQuasipolyModTop` |
| **depth-3 exact composition over `MOD_M ∘ AND_w` (the "across depth" clause of Wall 1)** | Tests directly whether exactness survives *one composition step*: a top gate over `k` middle `MOD_M ∘ AND_w` gates (depth 3, bounded fan-in below). **`depth3_middle_exact`** (each middle `MOD_M ∘ AND_w` gate is decoded *exactly* by its count-residue vector — CRT, no approximation, `modCount_factors_through_resVec`); **`depth3_modAnd_compose_searchable`** (both: every middle bottom layer is quasipolynomial `m ≤ ∑_{d≤w} C(n,d)` via `monomial_count_le`, *and* the depth-3 circuit `top ∘ (MOD_M ∘ AND_w)^k` is SAT-searchable in `< 2^n` cells once `2^k < 2^n`, observed *exactly* by the `k`-bit middle-output vector via `exact_depth_composes`). **Answer: exactness survives the extra composition step — at the *product* cost `2^k`.** Honest — the cost *is* the wall: `2^k` is quasipolynomial only for `k = polylog`, exponential for unbounded top fan-in; and pushing the exact intermediate residues up instead multiplies the per-gate `M` cells to `M^k` — the same product blow-up. The general YBT normal form needs an *arbitrary* `ACC⁰` bottom across *arbitrary* depth, where this product is genuinely exponential — the front half, **Wall 1** (it is the *bottom* `AND_w → exact low-degree polynomial across depth` that breaks, not the symmetric top, which composes exactly here). Cell/observer model; `< 2^n` cells is not a uniform algorithm (Wall 2) | `…ACC0ExactQuasipolyDepth3` |
| **the anti-product trick — a *symmetric* top avoids the `2^k` blow-up** | The smallest case where the depth-3 *product* wall is genuinely avoided. Entry `…ACC0ExactQuasipolyDepth3`'s *arbitrary* top costs `2^k` because it reads the full `k`-bit middle-output vector; a *symmetric* top (a count / `MOD` / threshold over the `k` middle gates) reads only the **count** of accepting middle gates — `k+1` states. **`antiproduct_count_card_le`** (`(image (gateCount (middleGate …))).card ≤ k + 1`, via `sym_count_card_le` — the product `2^k` collapses to linear); **`antiproduct_sym_modAnd_searchable`** (every middle bottom layer quasipolynomial `m ≤ ∑_{d≤w}C(n,d)` *and* the depth-3 circuit with a *symmetric* top `symEval (middleGate qs mono t) h` is SAT-searchable in `≤ k+1` cells once `k+1 < 2^n`, via `sym_searchable`). So two symmetric layers — an outer `SYM` over `k` inner `MOD_M ∘ AND_w` gates (themselves `SYM ∘ AND`) — compose with *linear* `k+1` observer state, not the product `2^k`/`M^k`. Honest — why this genuine trick is still not YBT: (1) it needs the circuit *pre-grouped* as a single symmetric layer over `k` nice middle gates (reducing arbitrary `ACC⁰` to that shape is the open problem); (2) the count of accepting middle gates is symmetric in the *middle outputs*, not the *inputs*, so it cannot be iterated to flatten arbitrary depth; (3) the bottom `AND` degree must still stay polylog (Wall 1). This *is* the YBT `SYM` top being tractable (`…ACC0SymmetricObserver`: a symmetric function is observed by its count, `m+1` not `2^m`), made concrete one layer up — it avoids the product at *one* symmetric layer; reducing arbitrary `ACC⁰` to one `SYM ∘ AND` of quasipoly width with polylog bottom degree remains the front half, Wall 1. Cell/observer model; `< 2^n` cells is not a uniform algorithm (Wall 2) | `…ACC0AntiProductSym` |
| **bottom-clause no-go — exact unbounded-fan-in `OR`/`AND` needs full degree = fan-in** | Attacks Wall 1's *bottom clause* head-on at the gate level and proves the obstruction is **real** (the exact counterpart to the proved *approximate* side `toAgree_totalDegree_le`). Over `F₂` every Boolean function has a *unique* multilinear (ANF) representation via the subset-sum transform `anf` (`…MajorityAlgebraicImmunity`, `anf_involutive : anf (anf g) = g`). Computing the **top ANF coefficient** of the unbounded-fan-in gates: **`anf_andFn_univ`** (`anf andFn univ = 1` — `AND` is literally the single full monomial); **`anf_orFn_univ`** (`anf orFn univ = 1` for `n ≥ 1` — `OR`'s full monomial is present, via the parity of the `2ⁿ−1` nonempty subsets, computed with `Finset.sum_boole` + `filter_ne'`/`card_erase_of_mem` + `((2ⁿ−1 : ℕ) : ZMod 2) = 1`); **`or_exact_degree_full`**/**`and_exact_degree_full`** (`∃ S, |S| = n ∧ anf · S ≠ 0` — a nonzero coefficient at the full set, so exact degree `= n`); **`or_not_anf_degree_lt`**/**`and_not_anf_degree_lt`** (the no-go: `¬ ∀ S, n ≤ |S| → anf · S = 0`, i.e. **no exact `F₂` representation of degree `< n`**). So an exact unbounded-fan-in `OR`/`AND` has `F₂` degree exactly `n` = the fan-in, hence its exact monomial-`AND` (`SYM∘AND` bottom) representation needs `2^n` monomials — *exponential*, not quasipolynomial. This is the precise reason the bottom clause is hard: the **naive route — one exact low-degree polynomial per `ACC⁰` gate — is impossible** for unbounded fan-in (exactness forces degree = fan-in). The only escape is the *approximate* low-degree polynomial (RS `toAgree`, degree polylog, agrees `1-ε`) converted back to an *exact* decision by the symmetric/count top, keeping degree polylog — exactly the irreducible Beigel–Tarui analytic core, **Wall 1**. This file proves the gate-level exact-vs-approximate gap that makes that conversion *necessary*; it does **not** perform the conversion (does not cross Wall 1). Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ExactDegreeNoGo` |
| **the BT approximate→exact conversion — socket + the proven decoding mechanism** | The route left after the no-go: recover the *exact* value from several *approximate* low-degree representations by a **symmetric/count decoder**. (1) The socket **`ApproxToExactSymmetricDecode D r f`** := `∃ g decoder, (∀ i, IsLowDegreeGate D (g i)) ∧ f = symEval g decoder` — the missing Beigel–Tarui theorem made *explicit*, where `IsLowDegreeGate D g := ∃ mono, (∀ j, (mono j).card ≤ D) ∧ g = symEval (monoAND ∘ mono) h`. **Crucially non-trivial only via the low-degree clause**: without it, `r` copies of `f` satisfy it (`f = symEval (const f) decoder`); *with* it, the socket holding for an arbitrary `ACC⁰` `f` (with `r` quasipoly, `D` polylog) **is** Wall 1. **`socket_searchable`** (the socket ⇒ `f` is the exact symmetric decode of `r` gates ⇒ SAT-searchable in `≤ r+1` cells once `r+1 < 2^n`, via `sym_searchable`). (2) The decoding mechanism **`majority_decode`** (TOY, *proved*): if at every point a strict majority of the `r` approximants agree with `f` (`∀ x, r < 2·#{i : g i x = f x}`), then `f x = decide (r < 2·gateCount g x)` *exactly* — error-corrected threshold-count decoding (proof: `gateCount = #(=1)` via `sum_boole`, `#(=1)+#(=0)=r` via `card_filter_add_card_filter_not`, then `omega` per `f x` case); **`majority_decode_symmetric`** (`f = symEval g (fun k => decide (r < 2k))` — `f` is *exactly* a symmetric threshold-count of the approximants); **`majority_decode_gives_socket`** (low-degree **and** majority-correct approximants ⇒ the socket). Honest decomposition: the *decoding* half is genuinely proved (symmetric threshold count recovers exact `f` under controlled error); the **open** part is producing `r =` quasipoly **low-degree** approximants that are majority-correct at *every* one of the `2^n` points — the irreducible Beigel–Tarui/Yao probabilistic construction, **Wall 1**, which this file does **not** perform. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ApproxToExactDecode` |
| **the balancedness seed of the RS/BT probabilistic `OR` (attacking the construction)** | Attacks the open construction (Wall 1) at its genuine analytic atom — the random `F₂` linear form, the building block of the Razborov–Smolensky / Beigel–Tarui probabilistic polynomial. **`pv v S := ∑_{i∈S} (v_i : ZMod 2)`** (the form `L_S(v) = ⊕_{i∈S} v_i`); **`tog j S := S △ {j}`** with **`tog_tog`** (involution) and **`pv_tog`** (toggling a coordinate `j` with `v_j = 1` flips the form's parity: `pv v (tog j S) = pv v S + 1`); **`pv_false`** (on the all-`0` input the form is `0` for every `S` — *one-sided*: a random form never gives a false positive when `OR = 0`); **`pv_balanced`** — *the seed*: for `v` with some bit set, exactly `2^{m-1}` of the `2^m` subsets give form value `1`, i.e. **a uniformly random linear form predicts `OR = 1` correctly with probability exactly `1/2`** (proved by the parity-flipping toggle involution pairing the parity-`0` and parity-`1` subsets via `Finset.card_bij'`, then `card filter + card filter¬ = 2^m` and `2^m = 2·2^{m-1}`). This is the genuine analytic reason a random parity is an unbiased `OR`-predictor — the atom on which the whole BT construction rests. Honest scope — what remains (not faked): **(1) degree-`t` boosting** (`OR` of `t` independent forms is correct with probability `1 - 2^{-t}`, `> 1/2` for `t ≥ 2` — a product/independence count over `pv_balanced`); **(2) quasipoly sampling** (Chernoff + a union bound over the `2^n` inputs to extract `r = O(n)` boosted forms majority-correct *everywhere*, giving the quasipoly low-degree family the socket needs). Plus a basis caveat: these parity forms are low *polynomial* degree but high *monomial-`AND`* degree, whereas `IsLowDegreeGate` is monomial-`AND`-based — the `AND`/`XOR` translation is part of the RS argument. Steps (1)–(2) + that bridge are the remaining Beigel–Tarui analytic work, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ProbabilisticForm` |
| **degree-`t` boosting — the full `t`-tuple form family is majority-correct everywhere** | Step (1) above, done: the `OR` of `t` independent forms `q_{(S_1,…,S_t)}(v) = ⋁_k L_{S_k}(v)` is wrong only when *all* `t` forms vanish. **`pv_zero_card`** (for `v ≠ 0`, exactly `2^{m-1}` subsets give form `0` — complement of `pv_balanced`); **`boost_wrong_card`** (the all-zero `t`-tuples number `(2^{m-1})^t`, by coordinatewise independence: the filter `{σ | ∀ k, pv v (σ k) = 0}` is `Fintype.piFinset (const (filter (=0)))`, card `= (2^{m-1})^t` via `Fintype.card_piFinset_const`); **`boost_total`** (`(2^m)^t` tuples via `Fintype.card_fun`/`card_finset`); **`boost_correct_card`** (correct tuples `= (2^m)^t - (2^{m-1})^t`, the complement); **`boost_predict_zero`** (on the all-`0` input the boosted predictor fires for *no* tuple — one-sided, no false positive); **`boost_majority_nonzero`** (for `t ≥ 2` and `v ≠ 0`, `total < 2 · correct` — a *strict* majority of `t`-tuples are correct, since `(2^m)^t = 2^t·(2^{m-1})^t > 2·(2^{m-1})^t`). So **the full family of `t`-tuples (`t ≥ 2`) is majority-correct at every input** (all tuples on `v = 0`, a `1 - 2^{-t} > 1/2` fraction on `v ≠ 0`) — this **discharges the "majority-correct" clause** of the socket `ApproxToExactSymmetricDecode` for `OR`: a family of low-(polynomial-)degree gates majority-correct everywhere genuinely exists. Honest — the sole remaining gap: the family *size* is `(2^m)^t`, *exponential*, whereas the socket needs `r =` quasipolynomial. Shrinking it (Chernoff concentration + a union bound over the `2^n` inputs to sample `r = O(n)` boosted forms keeping majority-correctness) is the probabilistic-method *sampling* step — that, plus the parity-vs-`monoAND` basis bridge, is the last of the Beigel–Tarui front half, **Wall 1**, not faked. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ProbabilisticBoost` |
| **self-contained finite Chernoff (the sampling concentration engine, route B)** | The last gate of the BT front half needs concentration; Mathlib's Chernoff/Hoeffding (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` etc.) are measure-theoretic, so this proves a **purely combinatorial** Chernoff lower-tail bound staying in `Finset`/`ℕ`/`ℝ` — no measure theory, no `exp`. **`finite_chernoff_lower`**: for any real `c ≥ 1`, sampling `σ : Fin r → P` with a good set `G ⊆ P`, the *minority-good* samples are bounded — `(#{σ | 2·#{i | σ i ∈ G} ≤ r} : ℝ) ≤ ((|G|/c) + c·(|P| − |G|))^r`. Proof = the classical Markov-on-a-product (Chernoff) argument in finite form: bound the count by `∑_σ c^r·d^{good σ}` (`d = (c²)⁻¹`, each minority term `≥ 1` via `pow_le_pow_right₀`), then the engine **`∑_{σ:Fin r→P} ∏_i w(σ i) = (∑_x w x)^r`** (`Finset.sum_prod_piFinset` + `Fintype.piFinset_univ` — the finite analogue of independence `E[∏] = ∏ E`), collapsing to `(c·(|G|·d + |P|−|G|))^r = (|G|/c + c(|P|−|G|))^r`. **`finite_chernoff_majority`**: the clean `c = 2`, good-fraction-`≥ 3/4` case (`3|P| ≤ 4|G|`) gives `≤ (7|P|/8)^r` — *geometric* decay, base `7/8 < 1` relative to `|P|`, exactly what the union bound consumes. Honest scope: this is the concentration **engine**, self-contained and proved. The finished sampling step still needs **(1)** instantiating `P` as the boosted form-tuples, `G` as the per-input correct set (`|G| ≥ 3|P|/4` from `…ACC0ProbabilisticBoost`); **(2)** the **union bound** over the `2^n` inputs (`∑_v #{bad at v} ≤ 2^n·(7|P|/8)^r < |P|^r` for `r = O(n)` ⇒ a sample correct everywhere by pigeonhole); plus the parity-vs-`monoAND` basis bridge — the remaining Wall 1 assembly, routine given this bound but not done here, not faked. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0FiniteChernoff` |
| **union-bound sampling existence (abstract — closes the sampling gate)** | The probabilistic-method existence argument on top of the finite Chernoff, finite and self-contained. **`exists_sample_majority_correct_all`** — abstract over input set `X`, predictor pool `P`, good sets `Good : X → Finset P`: given `∀ x, 3·|P| ≤ 4·|Good x|` (every input's good set has density `≥ 3/4`), `0 < |P|`, and `(|X| : ℝ)·(7/8)^r < 1`, there is a *single* sample `σ : Fin r → P` with `∀ x, r < 2·#{i | σ i ∈ Good x}` — a strict majority of the `r` coordinates land in `Good x`, **for every input `x` simultaneously**. Proof = union bound + pigeonhole: the global bad set `B = {σ | ∃ x, minority-good at x}` is `⊆ ⋃_x {minority-good at x}`, so `|B| ≤ ∑_x |minority-good at x| ≤ ∑_x (7|P|/8)^r = |X|·(7|P|/8)^r` (`card_biUnion_le` + `finite_chernoff_majority`); then `|X|·(7|P|/8)^r = |X|·(7/8)^r·|P|^r < |P|^r` (from the hypothesis, `mul_lt_mul_of_pos_right`), so `|B| < |P|^r = |{all samples}|`, hence `B ≠ univ` and a non-bad `σ` exists (`by_contra` + `card_le_card`). Deliberately **abstract** — not yet tied to parity forms. Intended instantiation (next step): `X = Fin m → Bool`, `P =` the boosted `t`-tuples of parity forms (`…ACC0ProbabilisticBoost`), `Good x =` the boosted forms correct on `x` (density `≥ 3/4` for `t ≥ 2` by `boost_majority_nonzero`); with `|X| = 2^m` the bound `2^m·(7/8)^r < 1` holds at `r = O(m)`, yielding the quasipolynomial-size form family majority-correct everywhere — exactly the open clause of the socket `ApproxToExactSymmetricDecode`. After that, the parity-vs-`monoAND` basis bridge is the final piece of the Beigel–Tarui front half, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0SamplingExistence` |
| **instantiation to parity forms — the quasipolynomial majority-correct family EXISTS** | Plugs the boosted parity forms into the abstract union-bound lemma, closing the sampling gate *concretely*. `X = Fin m → Bool` (`|X| = 2^m`), `P = Fin t → Finset (Fin m)` (boosted `t`-tuples), **`boostCorrect v σ := (∃ k, pv v (σ k) = 1) ↔ (∃ i, v i = true)`** (the boosted `OR`-prediction matches `OR(v)`), **`boostGood v := univ.filter (boostCorrect v)`**. **`card_pool`** (`|P| = (2^m)^t`); **`pv_all_false`** (form vanishes on the all-`0` input); **`boostGood_card_ge`** — *every input's good set has density `≥ 3/4`*: `3·|P| ≤ 4·|boostGood v|` for `t ≥ 2` (nonzero `v`: `boostGood v` = the firing tuples, card `(2^m)^t − (2^{m-1})^t` by `boost_correct_card`, and `4·(2^{m-1})^t ≤ (2^m)^t` since `2^t ≥ 4`; zero input: every tuple correct, `boostGood v = univ`); **`exists_quasipoly_majority_correct_forms`** — for `t ≥ 2` and `2^m·(7/8)^r < 1` (so `r = O(m)`), `∃ σ : Fin r → (Fin t → Finset (Fin m)), ∀ v, r < 2·#{i | σ i ∈ boostGood v}` — a single sample of `r = O(m)` boosted parity forms is **majority-correct at every one of the `2^m` inputs**, by `exists_sample_majority_correct_all`. This is exactly the quasipolynomial majority-correct family the socket `ApproxToExactSymmetricDecode` needs — **its open clause, now discharged for the parity-form construction**. The **one remaining piece** of the Beigel–Tarui front half is the *basis bridge*: these forms are low *polynomial* (`F₂`) degree but high *monomial-`AND`* degree, while the socket's `IsLowDegreeGate` is monomial-`AND`-based (the `AND`/`XOR` RS translation) — that last step is **Wall 1**, not done here. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0SamplingForms` |
| **the basis bridge — parity forms ARE low monomial-`AND` degree** | Resolves the `F₂`-poly-vs-`monoAND` mismatch. **Framing decision: the correct low-degree notion is `F₂`-polynomial total degree.** A linear form `L_S = ∑_{i∈S} X_i` has *polynomial* degree `1` — it is the *sum*, not the *product*, regardless of how large `S` is. So the boosted predictor `q_σ = 1 − ∏_k (1 − L_{σ k})` is a polynomial of total degree `≤ t`, and a degree-`≤t` `F₂` polynomial's Boolean-cube evaluation lies in the span of monomial-`AND`s of fan-in `≤ t`. There was no real mismatch — the "wide set" lives in the *linear* (degree-1) part, and only `t` forms multiply. **`linForm`** (`∑_{i∈S} X_i`), **`boostPoly`** (`1 − ∏_k (1 − L_{σ k})`), **`linForm_totalDegree_le`** (`≤ 1`, via `totalDegree_finsetSum_le` + `totalDegree_X`), **`boostPoly_totalDegree_le`** (`≤ t` — the crux, via `totalDegree_sub` + `totalDegree_finset_prod` + `oneSubLin_totalDegree_le`); **`eval_linForm`** (`eval (boolToZMod 2 ∘ v) (linForm S) = pv v S`), **`eval_boostPoly_eq`** (`= boolToZMod 2 (boostPredict σ v)` — the polynomial genuinely computes `⋁_k L_{σ k}`, by cases on `∃ k, pv = 1` with `prod_eq_zero`/`prod_eq_one`); **`boostPredict_mem_monoAND_span`** — *the bridge*: `(fun v => boolToZMod 2 (boostPredict σ v)) ∈ Submodule.span (ZMod 2) (range of degree-≤t monomial-`AND` indicators)`, via `lowDegPolyEval_mem_monoAND_span 2 t (boostPoly σ)`. So the probabilistic-method parity-form family (`…ACC0SamplingForms`) genuinely lives in the low-monomial-`AND`-degree world the socket wants. Honest scope: this resolves the bridge **for the `OR`-gate construction** (turning span membership into the exact `symEval`-`IsLowDegreeGate` packaging is the proved coefficient-duplication step, `…ACC0PolyToSymAnd`). What it does **not** do: the *full* Beigel–Tarui front half is the construction for an *arbitrary `ACC⁰` circuit across constant depth* (`(log s)^{O(d)}` degree, `MOD` layers, depth composition) — the single unbounded-fan-in `OR` handled here is one gate; the depth composition over all of `ACC⁰` remains **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0BasisBridge` |
| **the `AND`-gate BT front half, via `OR`-duality** | `AND(v) = ¬ OR(¬v)`, so the `OR` construction dualizes directly. The linear form `L_S = ∑_{i∈S} X_i` becomes the **affine** form `A_S = ∑_{i∈S}(1 + X_i)` (which evaluates to `L_S(¬v)` on the negated input — `eval_affForm`), and `boostPoly` becomes `andPoly = ∏_k (1 − A_{σ k})`. Since `1 + X_i` is *still degree 1*, `AND` inherits `OR`'s exact degree profile. **`affForm_totalDegree_le`** (`≤ 1`), **`andPoly_totalDegree_le`** (`≤ t`); **`eval_andPoly_eq`** (`= boolToZMod 2 (andPredict σ v)`, by cases with `prod_eq_one`/`prod_eq_zero`); **`andPredict_eq_not_boostPredict`** — the duality `andPredict σ v = ¬ boostPredict σ (¬v)` (via `(∀ k, pv (¬v) (σ k) = 0) ↔ ¬ ∃ k, pv (¬v) (σ k) = 1` + `decide_not`), so the `OR` family's majority-correctness (`…ACC0SamplingForms`) transfers to `AND` under the input-negation bijection; **`andPredict_mem_monoAND_span`** — the `AND` basis bridge: the boosted `AND` predictor's `F₂`-embedding lies in the span of the degree-`≤t` monomial-`AND` indicators, via `lowDegPolyEval_mem_monoAND_span 2 t (andPoly σ)`. So the unbounded-fan-in `AND` gate has low-monomial-`AND`-degree majority-correct approximants too — the **second of the three `ACC⁰` gate types** (after `OR`; `MOD` next). Honest scope: this is the `AND`-gate front half; the `MOD` gate and the **depth composition** of these approximants through a constant-depth circuit (degree `(log s)^{O(d)}`) plus assembly into `SYM∘AND` are the rest of the Beigel–Tarui/Yao front half, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0AndBasisBridge` |
| **one-layer composition of BT approximants — degree multiplies by `t`, not exponentially** | The Razborov–Smolensky depth-composition step. The basis bridge built the boosted `OR` out of the input variables `X_i`; composing through a layer is the *same* construction with the `X_i` replaced by the `k` **subgate approximant polynomials** `P_j`. **`compLinForm P S = ∑_{j∈S} P_j`** (the linear form over subgate *outputs*), **`compPoly P σ = 1 − ∏_l (1 − ∑_{j∈σ l} P_j)`** (the boosted `OR` over the subgates). **`compLinForm_totalDegree_le`** (`≤ d` if each `P_j` has degree `≤ d`) and **`compPoly_totalDegree_le`** — *the crux*: `(compPoly P σ).totalDegree ≤ t · d`, i.e. **the degree multiplies by the boosting parameter `t` per layer**, so across constant depth `D` the degree is `≤ t^D · (base) = (log s)^{O(D)}` — polynomial-in-`log`, *not* exponential (the Razborov–Smolensky degree-composition phenomenon). **`eval_compPoly`** (the composed polynomial evaluates to the boosted `OR` over the subgate values `eval … P_j`); **`compPoly_eval_mem_monoAND_span`** (the composed approximant lies in the degree-`≤ t·d` monomial-`AND` span, via `lowDegPolyEval_mem_monoAND_span 2 (t*d)`). The basis bridge (`…ACC0BasisBridge`) is the special case `P_j = X_j`, `d = 1` (so `t·d = t`). Honest scope: this is **one `OR`-layer** of the depth composition (subgate degree `d` → composed degree `t·d`, staying low). The `AND`-layer is the affine dual, `MOD` its own case; iterating through a whole constant-depth `ACC⁰` circuit — tracking *error accumulation* across layers (each boosted approximant is only majority-correct, errors compound), discharging `MOD`, and assembling the final `SYM∘AND` — is the rest of the Beigel–Tarui/Yao front half, **Wall 1**. This file supplies the degree-composition step, not the full inductive assembly. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0LayerCompose` |
| **across-depth error accumulation — composed error grows *linearly* in the gate count** | The *error* counterpart to `…ACC0LayerCompose`'s degree composition; together they are the RS depth composition. The composite approximant errs at `x` only if *some* gate errs at `x` (correctness composes: where every gate is correct, the composite is correct), so the composite error set is contained in the union of per-gate error sets. **`error_union_bound`** (`(univ.biUnion Err).card ≤ Fintype.card G * e` when each `(Err g).card ≤ e`, via `card_biUnion_le` + `sum_le_sum` + `sum_const`); **`composite_error_subset`** (`{x | comp x ≠ target x} ⊆ ⋃_g Err g`, given `hcomp`: comp correct wherever no gate errs — `by_contra` + `push_neg`); **`composite_error_bound`** (`|composite error| ≤ Fintype.card G * e`); **`exists_majority_correct_composite`** — if `2·(Fintype.card G * e) < Fintype.card X` (total error `< 1/2`), then `Fintype.card X < 2·|{x | comp x = target x}|` (the composite agrees with the target on a *strict majority* of inputs; via `card_filter_add_card_filter_not` + `omega`). **Linear-in-`s` error (not exponential) is exactly why constant depth works**: a depth-`d`, size-`s` circuit has `s` gates, total error `≤ s·e`, so taking the per-gate error `e < |X|/(2s)` — achievable with the boosting at polylog degree — keeps the whole-circuit composite *majority-correct*. Combined with `…ACC0LayerCompose` (degree `(log s)^{O(d)}`, polylog), this is the Razborov–Smolensky depth composition: linear error, polylog degree. Honest scope: this is the abstract union-bound error-accumulation mechanism over arbitrary per-gate error sets. The full RS composition also needs discharging `hcomp` for the actual gate substitution (per-point composition), the per-gate boosting that makes `e` small (`…ACC0ProbabilisticBoost`, `e = 2^{-t}·|X|`), and the `MOD` layer; iterating into the `ACC⁰ → SYM∘AND` normal form is the rest of the Beigel–Tarui/Yao front half, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ErrorAccumulation` |
| **per-point composition — the composed polynomial computes the gate of the subgate values** | Discharges the `hcomp` hypothesis of `…ACC0ErrorAccumulation` for an `OR` layer. **`boost_formula`** (`1 − ∏_l (1 − pv w (σ l)) = boolToZMod 2 (boostPredict σ w)`, both sides `= eval (boostPoly σ)` at `w`); **`eval_compPoly_of_subgates`** — if each subgate poly `P_j` computes its Boolean subgate `h_j` at `x` (`eval (P_j) x = boolToZMod 2 (h_j x)`), then `eval (compPoly P σ) x = boolToZMod 2 (boostPredict σ (fun j => h_j x))`: the composed polynomial computes the boosted `OR` of the subgate *values*. This is the bridge tying the *degree* composition (`…ACC0LayerCompose`) and *error* composition (`…ACC0ErrorAccumulation`) to the actual Boolean computation. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0CompositionCorrect` |
| **the `MOD₂` gate is *exactly* degree 1 (error 0)** | Where `OR`/`AND` have no exact low-degree polynomial (`…ACC0ExactDegreeNoGo`) and need the probabilistic boosting, `MOD₂` (parity) over `F₂` simply **is** the linear form `⊕_i x_i = ∑_i X_i`. **`mod2_exact_eval`** (`eval (linForm univ) x = boolToZMod 2 (parityBool x)` — exact, no approximation), **`mod2_totalDegree_le`** (`≤ 1`), **`mod2_mem_monoAND_span`** (in the degree-`≤1` monomial-`AND` span, exactly). So `MOD₂` composes with degree `d = 1`, error `e = 0`. Honest scope — and the real barrier: this is `MOD₂` only (`AC⁰[2]`). The Razborov–Smolensky polynomial method works over `F_p` for **prime-power** moduli; for **composite** `m` with two distinct prime factors (e.g. `MOD₆`) there is *no* known low-degree representation over any single field — exactly why `ACC⁰` lower bounds are hard and why the only known result (`NEXP ⊄ ACC⁰`, Williams) uses a different, algorithmic method. The `MOD` part genuinely stops at prime-power moduli; composite-`MOD` `ACC⁰` is the open barrier, **Wall 1** at its strongest. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0Mod2Exact` |
| **the `MOD_p` gate is *exactly* degree `p−1` over `F_p` (Fermat) — the `AC⁰[p]` ingredient** | The prime-`p` generalisation of `…ACC0Mod2Exact`. By **Fermat's little theorem** (`ZMod.pow_card_sub_one_eq_one`: `a^{p−1}=1` for `a≠0`, `0^{p−1}=0`), over `F_p` the count-`≡0` indicator is `MOD_p(x) = [∑_{i∈S} x_i ≡ 0 (mod p)] = 1 − (∑_{i∈S} X_i)^{p−1}` *exactly*. **`modpPoly`/`modpBool`** (the `F_p` polynomial and the gate), **`modp_exact_eval`** (`eval (modpPoly p S) x = boolToZMod p (modpBool p S x)` — exact, error 0, via Fermat + `set s`/case-split on `s=0`), **`modpPoly_totalDegree_le`** (`≤ p−1`, via `totalDegree_pow` on the degree-1 linear form), **`modp_mem_monoAND_span`** (in the degree-`≤(p−1)` monomial-`AND` span over `F_p`, via `lowDegPolyEval_mem_monoAND_span` at prime `p`). So a `MOD_p` gate composes into the RS machinery with degree `p−1`, error `0`; prime powers reduce to `F_{p^k}` by the same argument, giving the full `AC⁰[p^k]` picture. Honest scope — the barrier: this is **prime** `p` only. For composite `m=p·q`, Fermat pins the exponent to the chosen field's order (`p−1`, not `m−1`), so `a^{m−1}` is no `{0,1}`-indicator over `F_p` and fails symmetrically over `F_q` — **no single field sees `MOD_m` low-degree** (`mod6_eq_mod2_and_mod3`, `modq_residue_image_not_subspace`). That is why `NEXP ⊄ ACC⁰` needed Williams' algorithmic method. Classical `AC⁰[p]`-level; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0ModPExact` |
| **a single small-error boosted form, by averaging — the per-gate error input** | Error accumulation (`…ACC0ErrorAccumulation`) needs each gate to have a *single* approximant with a small error set; the boosting (`…ACC0ProbabilisticBoost`) gives a majority-correct *family*. This extracts a single good form by averaging (first moment). **`errSet σ = {w | (∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0}`** (the boosted-`OR` error, one-sided) with **`errSet_eq`** (it equals the actual `boostPredict`-vs-`OR` error, via one-sidedness `pv = 1 → ∃ j, w_j` and `(∀l, pv=0) ↔ ¬∃l, pv=1`); **`sum_errSet_card_le`** (`∑_σ |errSet σ| ≤ 2^k · (2^{k-1})^t` — the Fubini double-count `∑_σ |errSet σ| = ∑_w #{σ : σ errs on w}`, each nonzero `w` err'd by exactly `(2^{k-1})^t` forms via `boost_wrong_card`); **`exists_small_errSet`** (averaging + pigeonhole via `card_nsmul_le_sum` + `exists_min_image`: `∃ σ, (2^k)^t · |errSet σ| ≤ 2^k · (2^{k-1})^t`, i.e. error fraction `≤ 2^{-t}`). This is the per-gate small-error form that feeds `…ACC0ErrorAccumulation`. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0SmallErrorForm` |
| **circuit datatype + approximation invariant + base cases (the depth-induction scaffolding)** | Sets up the datatype and invariant for the Razborov–Smolensky depth induction. **`Circ n`** — an *unbounded-fan-in* Boolean circuit (`inp`/`const`/`not`/`or : List (Circ n)`/`and : List (Circ n)`; unbounded fan-in is the whole point of the polynomial method); **`Circ.eval`** and **`Circ.size`** (the `or`/`and` recursions over the `List` use `cs.attach` + a `sizeOf` termination argument with a two-pass `decreasing_by`). **`errCard P C`** — the number of inputs on which the `F₂` polynomial `P` disagrees with the circuit `C`'s value (under the `boolToZMod` embedding); **`Approximable C D E := ∃ P, P.totalDegree ≤ D ∧ errCard P C ≤ E`** — the approximation invariant. **`errCard_eq_zero_of_exact`** (exact computation ⇒ error 0). Base cases PROVEN: **`approximable_inp`** (`P = X i`, `D=1, E=0` — the variable is computed exactly), **`approximable_const`** (`P = C (boolToZMod 2 b)`, `D=0, E=0`), **`approximable_not`** (`P ↦ 1 − P`, preserves `D` and `E` — `1 − ·` is an `F₂` bijection flipping the value, proved via `(∀ u v : ZMod 2, (1 − u ≠ 1 − v) ↔ (u ≠ v))`). Honest scope — the inductive step that remains: for `OR`/`AND`, "subcircuits `Approximable` with degree `≤ D`, errors `≤ E_i` ⇒ `Circ.or cs` `Approximable` with degree `≤ t·D`, error `≤ (∑ E_i) + 2^{-t}·2^n`" — degree from `…ACC0LayerCompose`, the error split from per-point composition (`…ACC0CompositionCorrect`) + union bound (`…ACC0ErrorAccumulation`) over subgate errors plus the gate's own boosting error (`…ACC0SmallErrorForm`, input-space variant). Assembling that step, iterating to `degree ≤ t^d` / `error ≤ size·2^{-t}`, and handling `MOD` (prime-power only — composite `MOD` is the genuine open barrier) is the rest of the Beigel–Tarui/Yao front half, **Wall 1**. This file is the scaffolding (datatype, invariant, base cases). Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0CircuitApprox` |
| **input-space small-error averaging — the per-gate error for the circuit induction** | `…ACC0SmallErrorForm` averaged the boosted error over the *subgate-output* space `Fin k → Bool`; but in the circuit induction the gate's inputs are the *circuit* inputs `x` and the subgate values are `v(x) = (c_1(x), …, c_k(x))`, with `x ↦ v(x)` **not** measure-preserving — so this averages over the *input* space directly, for an arbitrary value map `v : X → (Fin k → Bool)`. **`boostError_iff`** (the boosted `OR`-predictor errs at output vector `w` iff `(∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0`, via one-sidedness `pv = 1 → ∃ j`); **`errSetV v σ`** (the inputs where the form errs on `v(x)`) with **`errSetV_eq`** (it equals the actual `boostPredict (v x) ≠ OR (v x)` error set); **`vanish_card_le`** (for fixed `w`, `≤ (2^{k-1})^t` forms vanish on it, via `boost_wrong_card`); **`sum_errSetV_card_le`** (`∑_σ |errSetV v σ| ≤ |X|·(2^{k-1})^t` — Fubini `∑_σ |{x : errs}| = ∑_x |{σ : errs on v(x)}|`, each input contributing `≤ (2^{k-1})^t`); **`exists_small_errSetV`** (averaging + pigeonhole: `∃ σ, (2^k)^t · |errSetV v σ| ≤ |X|·(2^{k-1})^t`, i.e. the form errs on `≤ 2^{-t}` fraction of *inputs*). This is the per-gate small-error form *over the circuit inputs* — the input needed for the `OR`/`AND` inductive step of `…ACC0CircuitApprox`; it generalizes `…ACC0SmallErrorForm` (the case `X = Fin k → Bool`, `v = id`). Honest scope: plugging it into the inductive step (gate boosting error over inputs) + per-point composition (`…ACC0CompositionCorrect`) + union bound (`…ACC0ErrorAccumulation`) gives one layer; iterating it, and handling `MOD` (prime-power only — composite `MOD` is the genuine open barrier), is the rest of the front half, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0InputSmallError` |
| **the `OR`/`AND` inductive step, assembled** | Assembles one `OR`/`AND` layer of the Razborov–Smolensky depth induction from all the pieces. `perr P f` = the error set of polynomial `P` against Boolean function `f`. **`or_step`** — for subgates `h_i` with degree-`≤D`, error-`≤E` approximants `P_i`, there exist `Q` (`= compPoly P σ`) and a gate-error budget `Eg` with `Q.totalDegree ≤ t·D`, `(perr Q (OR-of-h)).card ≤ k·E + Eg`, and `(2^k)^t·Eg ≤ 2^n·(2^{k-1})^t` (gate error `≤ 2^{-t}` fraction). **The crux is the error containment** `perr(compPoly P σ, OR(h)) ⊆ (⋃_i perr(P_i, h_i)) ∪ errSetV v σ`: at any input where *every* subgate approximant is correct (so `eval (compPoly) = boolToZMod (boostPredict (v x))` by `eval_compPoly_of_subgates`) *and* the gate's boosting is correct on `v(x)` (so `boostPredict (v x) = OR(v x)` by `errSetV_eq`), the composed polynomial computes the gate exactly — hence it errs only via a subgate error or the gate's own boosting error. Counting (`card_union_le` + `card_biUnion_le` + `∑_i E = k·E`) gives `≤ k·E + |errSetV v σ|`, and `exists_small_errSetV` (input-space averaging) makes the gate term `≤ 2^{-t}` fraction; degree is `compPoly_totalDegree_le`. **`and_step`** — the dual, `AND = ¬OR¬`: apply `or_step` to the negated subgates `¬h_i` (with approximants `1 − P_i`, whose error sets are unchanged by `perr_not_eq`) and negate the result, using `andTarget_eq` (`andTarget w = !(orTarget (¬w))`); same degree and gate-error bounds. Honest scope: this is one `OR`/`AND` layer over a `Fin k`-indexed family — the genuine content of the inductive step. Threading it through the `Circ` datatype (`…ACC0CircuitApprox`'s `List`-to-`Fin` packaging), iterating to the depth-`d` bounds (`degree ≤ t^d`, `error ≤ size·2^{-t}`), and handling `MOD` (prime-power only — composite `MOD` is the genuine open barrier) is the rest of the Beigel–Tarui/Yao front half, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0OrStep` |
| **the depth induction — every `MOD`-free circuit is approximable (the `AC⁰` case, closed)** | Closes the Razborov–Smolensky depth induction for the `MOD`-free (`AC⁰`) fragment, end to end. **`or_eval_bridge`** / **`and_eval_bridge`** — the `List`-to-`Fin` packaging: `Circ.eval x (or cs) = orTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))` (and the `and`/`andTarget` dual), via `List.any_eq_true`/`all_eq_true` + `List.mem_iff_get` + `Bool.eq_iff_iff`. `errCard_eq_perr` (definitional). **`approximable_exists`** — `∀ C : Circ n, ∃ D E, Approximable C D E`: *every* `MOD`-free circuit has a low-degree `F₂` approximant, by well-founded recursion on `sizeOf` (the `or`/`and` recursive calls decrease by `List.sizeOf_lt_of_mem (List.get_mem cs i)`), with base cases `approximable_inp`/`approximable_const`/`approximable_not` and the inductive step `or_step`/`and_step` — bridged from the `List` fan-in to the `Fin`-indexed family using `choose` (for the per-subgate approximants) and `Finset.sup` (for the uniform degree/error bounds). **Honest scope — this is classical and not new:** the result is `AC⁰`/`AC⁰[2]`-level (the corpus's Tier 1/2: `PARITY ∉ AC⁰`, `MOD ∉ AC⁰[p]`), a clean from-scratch Razborov–Smolensky construction, **not new mathematics and not progress toward `P ≠ NP`**. The bounds are existential (`∃ D E`); the quantitative `degree ≤ t^depth`, `error ≤ size·2^{-t}` follow by tracking `sup`/`size` through the same recursion. Extending to `MOD` works only for **prime-power** moduli (`mod2_mem_monoAND_span` is the `MOD₂` case); **composite `MOD_m` has no low-degree representation over any single field** — the genuine `ACC⁰` barrier, **Wall 1**, which the polynomial method *cannot* cross (the reason `NEXP ⊄ ACC⁰` required Williams' algorithmic method, not the polynomial method). Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0DepthInduction` |
| **quantitative degree bound — every `MOD`-free circuit is approximable at degree `≤ t^depth`** | Sharpens the `AC⁰` depth induction to the Razborov–Smolensky *degree* form. **`cdepth`** (circuit depth: `OR`/`AND` add a layer, `NOT` free, leaves `0`); **`le_foldr_max`** (list element `≤ foldr max`); **`cdepth_or_get_lt`**/**`cdepth_and_get_lt`** (a subcircuit's depth is *strictly less* than its `OR`/`AND` parent's, via `le_foldr_max` + `omega`); **`Approximable.mono_deg`** (weaken the degree bound). **`approximable_quant`** — for `t ≥ 1`, `∀ C : Circ n, ∃ E, Approximable C (t ^ cdepth C) E`: every `MOD`-free circuit has an `F₂` approximant of total degree `≤ t^depth`. By well-founded recursion: base cases via `simp [cdepth, pow_zero]` / `mono_deg`; the `OR`/`AND` step applies `or_step`/`and_step` with the *uniform* subgate-degree bound `D = t^(depth − 1)` (each subgate degree `≤ t^cdepth(child) ≤ t^(depth−1)` by `Nat.pow_le_pow_right` + child-depth `<` parent-depth) and then `t · t^(depth−1) = t^depth` (`← pow_succ'` + `congr` + `omega`). So each `OR`/`AND` layer multiplies the degree by `t`, giving `t^depth = (log s)^{O(d)}` for `t = polylog`, constant depth — the RS degree bound. Honest scope: still **classical** `AC⁰`/`AC⁰[2]`-level (Tier 1/2), not new mathematics, not `P ≠ NP`; the *error* bound stays existential (accumulates `≤ k·E + 2^{-t}` per layer, `…ACC0OrStep`); composite `MOD_m` is the genuine barrier, **Wall 1**. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0QuantDegree` |
| **quantitative error bound — approximant at degree `≤ t^depth` AND error `≤ size·2^{-t}` (the finished `AC⁰` package)** | Completes the quantitative Razborov–Smolensky package for the `MOD`-free (`AC⁰`) fragment. **`gate_bound`** — a boosted form whose error is `≤ 2^{-t}` of the inputs: `∃ σ, 2^t·|errSetV v σ| ≤ 2^n` (cancels the `(2^{k-1})^t` factor for `k ≥ 1` via `Nat.le_of_mul_le_mul_right`; the empty-gate `k = 0` case has `errSetV = ∅`, `Fin 0` empty). **`or_step_quant`/`and_step_quant`** — the `OR`/`AND` step in *sum* form: degree `≤ t·D`, error `≤ (∑ subgate errors) + Eg`, and the gate bound `2^t·Eg ≤ 2^n`. `sum_get_eq` — the `Fin`↔`List` sum bridge (`(cs.attach.map (g ∘ ·.1)).sum = ∑ i, g (cs.get i)`, via `List.ofFn`/`map_ofFn`/`sum_ofFn`). **`approximable_full`** — for `t ≥ 1`, `∀ C : Circ n, ∃ Q, Q.totalDegree ≤ t^cdepth C ∧ 2^t·(perr Q ⟦C⟧).card ≤ size C · 2^n`: every `MOD`-free circuit has an `F₂` approximant of **degree `≤ t^depth` *and* error `≤ size·2^{-t}`** (count form `2^t·error ≤ size·2^n`). By well-founded recursion: each `OR`/`AND` gate contributes a `2^{-t}`-fraction boosting error (`gate_bound`) and errors accumulate *additively* across the `size` gates (union bound, `or_step_quant`'s `∑`); the degree multiplies by `t` per layer. So the error stays `≤ size·2^{-t}` — for `t = log(2·size)` and constant depth, degree `(log s)^{O(d)}` (quasipoly) and error `< 1/2` (the function is exactly computed on a majority). Honest scope: this **finishes the quantitative `AC⁰` RS construction** (degree `t^depth`, error `size·2^{-t}`) — still **classical** (`AC⁰`/`AC⁰[2]`-level, Tier 1/2), **not** new mathematics, **not** `P ≠ NP`. `MOD` extends only to prime-power moduli (`MOD₂` done); composite `MOD_m` is the genuine `ACC⁰` barrier, **Wall 1**, which the polynomial method cannot cross. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` | `…ACC0QuantError` |

#### The exact-quasipoly fragment boundary (the four probes, as one localized result)

The four entries above (`…ACC0IntegerPolynomialCRT`, `…ACC0ExactQuasipolyDepth2`, `…ACC0ExactQuasipolyModTop`,
`…ACC0ExactQuasipolyDepth3`) are not four separate facts — they are **one result probed from four sides**, mapping
exactly the boundary of where an *exact-and-quasipolynomial* `SYM∘AND` is achievable, and isolating the single clause
that fails in general (Wall 1).  Read together:

| probe | fragment | exact? | size / cell cost | what it isolates |
|---|---|---|---|---|
| **back half** (`…IntegerPolynomialCRT`) | a `MOD_M` *top* on the integer count, `M = ∏ q_i` | **exact** (CRT, no approx) | `M` residue cells | the *symmetric/modular top* is exactly decodable — for free |
| **top kind** (`…ExactQuasipolyDepth2`) | `OR ∘ AND_w` (DNF) | **exact** | `≤ ∑_{i≤w}C(n,i)` bottom | a *bounded-fan-in* `AND` *is* a degree-`≤w` monomial, exactly |
| **one MOD layer** (`…ExactQuasipolyModTop`) | `MOD_M ∘ AND_w` | **exact** | bottom quasipoly, top `M` cells | the modular top *composes onto* the exact bottom, still exact |
| **one depth step** (`…ExactQuasipolyDepth3`) | `top ∘ (MOD_M ∘ AND_w)^k` | **exact** | **product** `2^k` (or `M^k`) | composition survives exactly — at a *product* cost |

The invariant across all four: **exactness is never the obstruction.**  Every symmetric top (`OR`, `MOD`, threshold)
is *exactly* a count/CRT-decoded gate, and every *bounded-fan-in* `AND` is *exactly* a bounded-degree monomial — no
Razborov–Smolensky approximation is needed anywhere in this fragment.  What is bounded — and the only thing that must
be bounded — is the **fan-in / degree of the bottom `AND` layer**, which controls both the monomial count
(`∑_{i≤w}C(n,i)`, quasipoly for `w = polylog`) and the composition cost (`2^k`/`M^k`, quasipoly for `k = polylog`).

So the fragment boundary is sharp and one-dimensional: the exact-and-quasipolynomial `SYM∘AND` holds **iff the bottom
`AND` degree stays polylog**, and the symmetric/modular structure above it is irrelevant to exactness.  The general
Yao–Beigel–Tarui normal form is precisely the case where the bottom degree is *not* given bounded — an arbitrary
`ACC⁰` subcircuit (unbounded fan-in / interleaved `MOD` / arbitrary depth) whose *exact* low-degree representation
across depth is the open analytic core.  The four probes thus localize **Wall 1 entirely to the bottom**:
`ACC⁰ → exact low-degree integer polynomial across depth`.  Nothing in this fragment is `NEXP ⊄ ACC⁰` or `P ≠ NP`;
it is the precise map of how far exactness reaches before that one clause stops it.

#### The two remaining YBT walls (what is *not* proved, and exactly why)

The YBT cash-out lane above is **fully assembled** in the cell/observer model: every link from the `SYM∘AND` normal
form onward is proved sorry-free (`circuit → poly` exact via Layer3 `toPoly`; `poly → SYM∘AND`-span given degree via
`acc0p_circuit_in_monoAND_span`; degree discharged for the approximant via `acc0p_toAgree_in_monoAND_span`;
coefficient-duplication count-mod-`p` via `weightedGateCount_cast_eq`; `SYM` count observer via `sym_searchable`;
exact gate symmetry via `…ACC0SymmetricExact`; exact depth composition via `exact_depth_composes`; additive degree
via `…ACC0AdditiveDegree`). What remains are **two named walls**, each *not* a missing lemma but a known
research-grade theorem, documented here so the boundary is explicit and never silently crossed.

**Wall 1 — the exact–quasipoly tension (the Beigel–Tarui analytic core).**  This is now a *theorem*, not a
suspicion: `exact_depth_composes` together with `…ACC0AdditiveDegree`/`…ACC0ToAgreeDegree` pins the obstruction
exactly.  There are two ways to compose an `ACC⁰` circuit into a searchable normal form, and they are mutually
exclusive with the tools in hand:

* **Exact composition** (`exact_depth_composes`, `…ACC0SymmetricExact`): the gates `AND`/`OR`/`MOD` *are* exact
  symmetric count functions, so they compose at any depth with **no approximation** — but the boundary is the
  *product* `2^k` (or `∏ᵢ|Sᵢ|`, `depth_compose_searchable`), **exponential** in the width.  Exact ⇒ exponential.
* **Quasipolynomial composition** (`toAgree_totalDegree_le`, `…ACC0AdditiveDegree`): polynomial degree composes
  *additively* (`toPoly_andGate_totalDegree_le`: `AND` degree = sum, not product, of input degrees), so a
  constant-depth circuit has polylog degree `((p-1)t)^{depth}` and hence only **quasipolynomially** many
  monomial-`AND`s (`∑_{i≤D}C(n,i)`).  But the polylog-degree representation is the Razborov–Smolensky **approximant**
  (`toAgree`), which agrees with the circuit on only a `1-ε` fraction (`…ACC0ApproxConsequence` shows an approximate
  `SYM∘AND` bounds the *solution count*, not SAT).  Quasipoly ⇒ approximate.

  Having **both at once** — an *exact* `SYM∘AND` of *quasipolynomial* size — is the Beigel–Tarui construction: an
  exact integer-valued polynomial of polylog degree whose value is decoded by the symmetric top gate via CRT
  (`MOD`-counting modulo several primes simultaneously).  That construction is the irreducible analytic core of the
  Yao–Beigel–Tarui normal-form theorem.  It is a *known classical result* but is **NOT** formalized here, and it
  cannot be obtained by gluing the two proved halves (each provably gives up the property the other needs).  Socketed
  as `MixedACCDepthReductionSocket` / `HasExactSymAndForm`; the socket holding for arbitrary `ACC⁰` with `m`
  quasipolynomial **is** the YBT theorem.  *The CRT-decode **back half** is now formalized* (`…ACC0IntegerPolynomialCRT`):
  given the *exact* integer count polynomial, the exact `MOD_M` decision is recovered from its residues modulo the
  prime factors of `M` (`count_crt_iff`, `modCount_factors_through_resVec`).  This sharpens the wall to the **front
  half** alone — producing the *exact* low-degree integer polynomial from an `ACC⁰` circuit across depth — since CRT
  decodes only from an *exact* count and cannot upgrade approximate RS residues to an exact decision.

**Wall 2 — Williams uniform realization (the algorithmic / separation-strength step).**  Even granted an exact
quasipoly `SYM∘AND` normal form (Wall 1), a *small cell count is not a uniform algorithm*.  Turning the
normal-form/observer structure into the actual `2^{n-n^ε}`-time `ACC⁰`-SAT algorithm — and running it through
Williams' connection to get `NEXP ⊄ ACC⁰` — is the `UniformWilliamsRealizationSocket` step
(`…ACC0WilliamsCashout`, `…WilliamsNEXP_ACC0`, `…NFrameACC0Speedup`).  This is **separation-strength** and is
deliberately **untouched** (per the HAL guidance: do not attack the uniform-realization cash-out, which is
equivalent to the separation itself).  The self-audit theorems `williams_socket_iff_separation` /
`realization_socket_iff_separation` prove each cash-out socket is *logically equivalent to the separation* — so they
reduce nothing; they honestly mark where the `NEXP ⊄ ACC⁰`-strength content lives.

**Net honest position.**  Everything reducible in the cell/observer model is discharged sorry-free with clean axioms
`[propext, Classical.choice, Quot.sound]`.  The lane bottoms out at exactly these two named walls — Wall 1 (the
Beigel–Tarui exact-quasipoly normal form, a known but unformalized classical theorem) and Wall 2 (Williams uniform
realization, separation-strength).  Nothing here is, or claims to be, `NEXP ⊄ ACC⁰` or `P ≠ NP`.

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
