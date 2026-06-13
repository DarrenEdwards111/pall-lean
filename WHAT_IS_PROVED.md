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
low‑degree resistance — is thereby **resolved**: Majority does both, with no remaining hypothesis. The single
gap that remains is resistance against **all** polynomial‑time inverters, which appears in five equivalent forms,
all `= P ≠ NP`, and which a proved gap theorem shows the action/space machinery cannot by itself reach.

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

## 4″. The time‑axis wall, consolidated (`…TimeAxisWall`)

With the space axis closed (separating boundary exactly `r`), the wall is relocated to the time axis and stated
as its own file. `space_axis_settled` (separator at `r`, none below); `ResidualSeparatorRequiresSuperpolyTime`
(the named missing bridge: the *existing* boundary‑`r` separator's decision time is super‑poly);
`timeAxis_wall` (the bridge + super‑poly threshold ⇒ family ∉ `P`); `space_machinery_cannot_supply_bridge`
(the gap — an action/debt bound of any size is hit by a poly‑time single‑step trajectory, so the space‑exact
machinery yields *no* time bound). The one missing theorem is a pure time lower bound on realizing the
boundary‑`r` separator — for an NP‑complete family, exactly `P ≠ NP`.

## 4‴. Restricted time models — bounded‑width branching programs (`…BoundedWidthBPTime`)

The first restricted *time* model after space‑tightness.  `BProg`/`BProg.run` formalize a layered branching
program (width `W`, length `L`); `bp_width_no_separator` proves a width‑`W` BP with `W < 2^r` carries debt
`≥ 2^r − W > 0` against the dimension‑`r` residual — **for every length `L`**.  So time (length) cannot
compensate for bounded width in *realizing* the separator; a poly‑*size* BP (width `≤ poly`, boundary
`O(log n) < r`) cannot realize it either.  Honest caveat: this is the realization/classifier bound, not a
`1`‑bit decision lower bound — the decision‑vs‑separation gap is the time‑axis bridge (the open step).

## 4⁗. The cash‑out on the decision axis — unconditional, by counting (`…RestrictedCashout`)

A Williams‑style cash‑out that bites on the `1`‑bit *decision* axis, with no conjecture: `cheap ⇒ enumerable`
(a bounded‑resource decider has a short description — the proved speedup `…NFrameSpeedupBridge` quantifies this)
and the contradiction by counting/diagonalization (`exists_uncomputed_of_card_lt`).  `card_boolFun`
(`|BoolFun n| = 2^{2^n}`); `cheap_class_misses_function` (a class `Fin N → BoolFun n` with `N < 2^{2^n}` misses
some function); `restricted_cashout` (a cheap enumerable class is *not surjective* onto all Boolean functions).
This is a genuine, unconditional **decision** lower bound (some function escapes every cheap decider) — distinct
from the separator/classifier bounds.  Honest limitation: it is the *existence* (Shannon) form — it gives *some*
hard function, not an *explicit* family; pinning it to an explicit NP family is the `P ≠ NP`‑strength step.

## 5. The exact missing theorem — where everything converges

Every route terminates at the **same** wall, in five equivalent forms (all `= CookLevinFrontierHyp = P ≠ NP`):

| form | statement | provable half | open half |
|---|---|---|---|
| decision‑holonomy | every correct SAT trajectory has super‑poly decision time | — | the time bound |
| `AdaptiveResidualNonCollapse` | every cheap adaptive decomposition keeps `2^{Ω(n)}` outcomes | one fixed decomposition | the `min` over **all** |
| `DimensionGapHard` | `d_res(SAT) − d_obs ≥ Ω(n)` for *every* poly observer | a fixed observer carries debt | the `min` over **all** |
| global SPDP bridge | every poly‑time observer has poly SPDP rank | restricted `K` | all of `P` |
| `(Goldreich)InversionHardness` | the family resists fast inversion (OWF / local‑PRG security) | the four classes of §2 | all poly inverters |

In every form the **provable half is geometric/pointwise** (a fixed low‑`d_obs` observer, a fixed class) and the
**open half is universal** (the quantifier over *all* poly observers / *all* cheap decompositions / *all* poly
inverters). The gap theorem `distinguishability_debt_not_time_lower_bound` proves *why* the debt machinery — an
*action/space* bound — cannot by itself cross from the pointwise to the universal: that crossing is exactly
`P ≠ NP`.

**Bottom line.** The optimal predicate is identified and proved optimal; it unconditionally defeats every
restricted inverter class the programme expresses; the binding pair (low‑degree ∧ `AC⁰[p]`) is realized on that
single predicate with no hypothesis; the complementarity that blocked this is resolved; the false routes are
retired; and the separation is reduced to one named statement, shown equivalent to `P ≠ NP` and shown
*unreachable* by these methods. Everything reducible is discharged. The one irreducible step — universal
quantification over all polynomial‑time machines — is `P ≠ NP` itself, and nothing here claims to take it.
