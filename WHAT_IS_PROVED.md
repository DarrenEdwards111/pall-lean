# WHAT IS PROVED — an honest audit

A single ledger of the observer‑boundary / Goldreich programme: what holds **unconditionally**, what holds
**for restricted classes**, what is **conditional on a named conjecture**, which routes are **retired as
false/dead**, and the **exact missing theorem**. All "proved" entries are Lean 4 / Mathlib, `sorry`‑free, axioms
`[propext, Classical.choice, Quot.sound]` (some pure‑`Nat`/`decide` lemmas use a subset; `native_decide` uses
are flagged, not present in the load‑bearing results). Branch `razborov-recoverRho-wip`.

**This is not a proof of `P ≠ NP`.** It is a formalized restricted lower‑bound theory plus a precise reduction
of the separation to one named statement.

---

## 1. Proved unconditionally

- **Dynamical debt accounting.** `debtCount`, conservation (`debt_conservation_varying`, `merge_pay`,
  `correct_needs_action`), and the mechanism `foolingSet_forces_debt` (`debt ≥ K − 2^B`). The core engine.
- **Observer‑boundary invariant.** Fooling‑set principle: `K` non‑mergeable sectors ⇒ boundary `≥ log₂ K`.
- **Gauge invariance of debt.** `debtCount_relabel_invariant` (lossless frame change preserves debt);
  no gauge transformation lowers debt.
- **The `F₂` Möbius / ANF inversion** (Mathlib lacks it): `anf_involutive` (subset‑sum transform is its own
  inverse over `F₂`), from the interval count `card_filter_subset_between`.
- **Growing algebraic immunity — two‑sided & optimal.** `AI(Maj_{2t-1}) = ⌈n/2⌉`
  (`majority_AI_optimal`): lower bound `≥ t` (`majority_algebraic_immunity_two_sided`, via the inversion +
  degree‑preserving complement symmetry `degreeLt_compl`) and the matching upper bound `AI(f) ≤ ⌈n/2⌉` for
  **every** `f` (`algebraic_immunity_le_ceil`, by pigeonhole + complement‑symmetry counting). No `decide`;
  scales with arity.
- **AI ⇒ separator resistance.** `majority_defeats_low_degree_separator`: no nonzero degree‑`<t` function
  annihilates `Maj`/`¬Maj` — the low‑degree‑annihilator / linearization attack provably fails against Majority.
- **The conditional cash‑out chains (pure logic, no axioms).** `williams_cashout`, `ravel_wedge`,
  `observer_centric_williams`, `goldreich_observer_williams`, `majority_observer_williams` (the explicit
  four‑step chain `low‑action ⇒ separator∈K ⇒ fast inversion ⇒ collapse ⇒ ⊥`).
- **`Majority ∉ AC⁰[p]` — UNCONDITIONAL** (`…ModqReducesMajority`): the full `MOD_q ≤_{AC⁰[p]} Majority`
  reduction circuit is formalized (`thresholdCirc` via `padInputs`, `modqCirc = ⋁([#ones=k])`, with eval‑
  correctness, `AC⁰[p]`, constant depth, polynomial size, and a from‑scratch `IsPolyBounded` closure), discharging
  `AC0pReduction` ⇒ `majority_not_in_AC0p`.  Hence **`majority_simultaneous_resistance`**: `majorityF2`
  unconditionally satisfies **both** binding resistances (low‑degree *and* `AC⁰[p]`), realizing
  `SimultaneousAlgAC0pResistance` on a single predicate with **no remaining hypothesis**.
- **The simultaneous‑resistance wall, made formal** (`…UnifiedInverterFrontier`): `ResistsLowDegree`/`ResistsAC0p`
  on a common carrier; `majority_resists_lowDegree`, `parity_resists_AC0p`/`modq_resists_AC0p` (witnesses), and
  **`parity_not_resists_lowDegree`** — the *complementarity theorem*: the `AC⁰[p]`‑resisting parity is affine
  (`AI ≤ 1`), so it provably **fails** low‑degree resistance. `SimultaneousAlgAC0pResistance` names the open
  conjunction (one family with both). Turns "no single predicate resists everything" into a theorem.
- **The geometric core of the gap.** `dimension_gap_forces_debt` / `positive_gap_forces_debt`: a low‑`d_obs`
  observer of a high‑`d_res` residual carries debt `≥ 2^{d_res} − 2^{d_obs}`.

## 2. Proved for restricted classes `K` (genuine restricted lower bounds)

- **Proof‑space.** Expander‑Tseitin blackboard refutations: total space `≥ c·t`
  (`tseitin_totalSpace_lower_bound`), via the width kernel — no Atserias–Dalmau, no locking lemma.
- **Boundary–time tradeoffs.** `bounded_boundary_tradeoff` (`|P| ≤ (T+1)·2^B`), average/burst variants, an
  explicit `2^n` witness, and a switch‑cost lower bound.
- **The decomposition ladder** (each = "effective boundary `< r` ⇒ debt", from expansion): read‑set, `F₂`‑linear
  (`finrank_map_ker_ge`), bounded‑locality/junta, holonomy/curvature, many‑loop amplification.
- **Crossing‑sequence bridge.** `crossingSequence_no_separator`: a width‑`w` crossing‑sequence observer over `q`
  states cannot separate a dimension‑`r` residual once `q^w < 2^r` — *non‑circular, by counting*. Discharges
  `restrictedBridge` for the one‑tape/oblivious model.
- **Restricted `InversionHardness` — unconditional, by class** (`…RestrictedInversionHardness`): the global
  inversion conjecture is a *theorem* for concrete inverter classes. `no_low_degree_algebraic_inverter` (no
  degree‑`<t` annihilator of `Maj` ⇒ the linearization/Gröbner attack fails, from `AI(Maj)=t`),
  `boundedCrossing_not_correct_inverter` (a width‑`w` crossing observer is not a separator once `q^w<2^r`),
  `boundedLocality_not_correct_inverter` (a `|W|`‑variable junta view is not a separator once `2^{|W|}<2^r`).
- **`AC⁰[p]` / approximate inverter — unconditional, via Razborov–Smolensky** (`…AC0pInverterHardness`):
  `no_AC0p_inverter_modq` / `no_AC0p_inverter_parity` — no constant‑depth, poly‑size `AC⁰[p]` family decides
  `MOD_q` (`q≠p`) or `PARITY` (`p` odd), reusing the assembled RS chain (`Layer3` approximation + `Layer4`
  no‑approximation core `mod_q_indicators_false` + `Layer7` family lower bounds). Clean axioms.
- **Calibrations** (re‑derive known bounds through the invariant): AC⁰[p] = Razborov–Smolensky
  (`mod_q_indicators_false`), Nečiporuk `n²/log n`, deterministic communication rectangles.

## 3. Conditional on a named conjecture (the observer‑Williams / Goldreich route)

`majority_observer_williams` proves *no low‑action observer inverts the Majority‑Goldreich family*, given four
ingredients bundled in `MajorityGoldreichHardness`:

| ingredient | status |
|---|---|
| `raveling` (low‑action ⇒ in `K`) | **provable for restricted `K`** (the debt corpus, crossing‑sequence) |
| `separatorSpeedup` (`K`‑separator ⇒ fast inversion) | framework‑supplied (DP engine, abundant margin) |
| `fastInversionImpliesCollapse` (fast inversion ⇒ collapse) | Williams‑style, standard |
| **`noCollapse` / `InversionHardness`** | **the open conjecture** — local‑PRG security, `P ≠ NP`‑strength (but **proved for restricted inverter classes**: low‑degree, bounded‑crossing, bounded‑locality — see §2) |

Also conditional: `p_ne_np_from_bridge` (the SPDP bridge `PObserverLowSPDP` ⇒ separation) and
`restricted_bridge_gives_separation` (its provable restricted shape).

## 3′. Option A — NOW UNCONDITIONAL (the reduction is proved)

`Majority ∉ AC⁰[p]` would merge the algebraic and `AC⁰[p]` faces onto one predicate.  Razborov–Smolensky gives
`MOD_q ∉ AC⁰[p]`; Majority follows from the classical `MOD_q ≤_{AC⁰} Majority` reduction (`MOD_q ∈ TC⁰`).
Formalized (`…MajorityAC0pScope`): given `AC0pReduction (modqLang q) majorityLang p`,
`majority_not_AC0p_of_reduction` (Majority ∉ AC⁰[p]), `majority_resists_AC0p_of_reduction`, and
**`majority_witnesses_simultaneous_of_reduction`** — `majorityF2` then satisfies *both* binding resistances, so
`SimultaneousAlgAC0pResistance` holds.  The wall's binding pair collapses onto Majority **modulo a known,
non‑conjectural reduction** (the only cost is building the padded‑threshold circuit, `padInputs`/`padTrue`
supplied) — qualitatively unlike the `P ≠ NP`‑strength `InversionHardness`.

## 4. Retired routes (proved false or proved dead — not merely abandoned)

- **`P_ne_NP_unconditional` (old).** Parked `P`‑side content in unproved sockets; retired — replaced by honest
  conditionals.
- **The `B < r` / brute‑force escape.** `hypercube_brute_force_escape`: a full‑boundary view resolves the `2^n`
  geometry with **zero debt**. The fooling‑debt mechanism is *empty* above boundary `≈ n` — a realized barrier.
- **Time ⇒ boundary.** `action_unbounded_by_time`: poly *time* yields **no** boundary/action bound. "P‑time ⇒
  cheap observer" is *false*, not open. (Holds only *given a space bound*: `subcritical_of_lowspace`.)
- **Proof‑hard ≠ decision‑hard.** `tseitin_unsat_of_odd_charge`: expander‑Tseitin is proof‑hard but
  **decision‑easy** (one parity bit). The hard instances of the lower‑bound theory do not transfer to decision
  hardness.
- **The AND gadget.** `AI = 1` (degree‑1 annihilator) — filtered out; superseded by TSA (`AI=2`) then Majority
  (`AI=⌈n/2⌉`).
- **Diagonal SPDP / `χ_φ` lower bound.** Disproved (`rk ≪ #SAT`); the SPDP‑bridge's load‑bearing lower bound is
  false on the diagonal route and barriered (short of `VP` vs `VNP`) on the permanent route.
- **The HM / metacomplexity socket.** Proved *vacuous* by its own iff (`nonempty_…iff_MCSPMINKTHardness`):
  repackaging does not reduce `P ≠ NP`‑strength.

## 5. The exact missing theorem

Every route above terminates at the **same** wall, in equivalent forms (all `= CookLevinFrontierHyp = P ≠ NP`):

- **decision‑holonomy** — every correct SAT trajectory has super‑poly decision time;
- **`AdaptiveResidualNonCollapse`** — every cheap adaptive decomposition keeps `2^{Ω(n)}` residual outcomes;
- **`DimensionGapHard`** — `d_res(SAT) − d_obs ≥ Ω(n)` for *every* poly observer (the `min`‑over‑observers half);
- **global SPDP bridge** `PObserverLowSPDP` — every poly‑time observer has poly SPDP rank;
- **`InversionHardness`** — the Majority‑Goldreich family resists fast inversion (local‑PRG security).

The provable half is always the *geometric/pointwise* one (a fixed low‑`d_obs` observer carries debt). The open
half is always the *universal* one (the `min` over **all** poly observers / **all** cheap decompositions). The
gap theorem `distinguishability_debt_not_time_lower_bound` proves *why* the debt machinery — an *action/space*
bound — cannot by itself reach the *time/universal* statement: that crossing is exactly `P ≠ NP`.

**Complementarity (the precise shape of the wall).** The proved restricted classes are *mutually
incomparable*: `Majority` resists the low‑degree algebraic attack (optimal AI) but `MOD_q` — which resists
`AC⁰[p]` — is `F_q`‑linear (algebraically trivial). No single explicit predicate is proved to resist *all*
inverter classes simultaneously. That simultaneous resistance over one family is exactly the global
`InversionHardness` (`P ≠ NP`‑strength): each restricted class is a theorem; their conjunction is the open
problem.

**Bottom line.** The predicate is provably optimal, the algebraic attack provably fails, the restricted bridges
are theorems, the false routes are retired — and the separation is reduced to one named statement
(`InversionHardness` / decision‑holonomy), proved equivalent in strength to `P ≠ NP`. Closing it is the open
problem; nothing here claims to.
