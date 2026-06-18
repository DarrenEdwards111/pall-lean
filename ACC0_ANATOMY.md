# An N-Frame–driven machine-checked anatomy of `NEXP ⊄ ACC⁰`

**Status: not a proof of `NEXP ⊄ ACC⁰` and not a proof of `P ≠ NP`.**  This document writes up what the arc *did*
achieve: a machine-checked (Lean 4 / Mathlib), sorry-free **conditional decomposition** of Williams' `NEXP ⊄ ACC⁰`
route, and — driven as a proof-search by the N-Frame dynamic-observer framing — a **localization of the
composite-`ACC⁰[m]` wall to a single, precise, classical open object**: the per-field `SYM∘AND` representation of
composite `MOD_m` gates with cross-field mixing handled (equivalently, the Razborov–Smolensky lower bound in its
operative form).  Every reducible part of the route is *proved* or *refuted*; the irreducible core is *named*, not
faked.

All theorems cited below build with clean axioms (`[propext, Classical.choice, Quot.sound]` or tighter) and **no**
`sorryAx`, in namespace `PallLean.Paper93.DeepMath.PathB`.  See `WHAT_IS_PROVED.md` and `ACC_THEOREM_MAP.md` for the
per-theorem ledger, and `ComputationalDepthACC0FrontierSummary.lean` for the consolidated `#print axioms` audit.

---

## 1. What this is, and what it is not

**Is:** a faithful, machine-checked map of Williams' 2011 `NEXP ⊄ ACC⁰` proof and the Beigel–Tarui (BT) /
Razborov–Smolensky (RS) machinery underneath it, with each classically-proved theorem either *proved* in Lean or
isolated as an honestly-labelled named socket; and an exhaustive, conservative anatomy of *where* the composite-`ACC⁰`
barrier actually lives.

**Is not:** a proof of any separation.  The deep classical theorems that the route depends on (e.g. `MIP = NEXP`, the
IKW easy-witness lemma, the NW/IW hardness–randomness tradeoff, and the composite-`ACC⁰` lower bound) are isolated as
named sockets; the *operative* irreducible one is a known open problem.  Nothing here claims to take it.

**Discipline.**  No socket is ever discharged by a false closure.  When a step was not provable conservatively, it was
named, not faked.  Two self-corrections during the arc (a false `ChernoffPerInput`, a wrong dichotomy `iff`) were caught
and fixed transparently — evidence the no-faking discipline was load-bearing, not decorative.

---

## 2. The two-route Williams/BT architecture (decomposed)

Williams' result factors as: `ACC⁰ ⇒` a single quasipoly `SYM∘AND` representation `⇒` a faster-than-trivial SAT
algorithm for `ACC⁰` circuits `⇒` (with the nondeterministic time hierarchy + Karp–Lipton/IKW collapse) `NEXP ⊄ ACC⁰`.
The arc decomposes both sides:

- **BT side (`ACC⁰ ⇒ SYM∘AND`).**  Two routes formalised: a direct low-degree (quasipoly) route, and a
  majority-amplification route shown to be *exponential* (honestly: that terminus does not give quasipoly).  The RS
  probabilistic polynomial method is driven to combinatorial proofs with **no measure theory** (involution-based
  per-point detection, Fermat indicators, binomial-tail Chernoff).
- **Williams side (collapse + hierarchy).**  The Karp–Lipton chain is fully decomposed: `NEXP ⊆ ACC⁰ ⟹ NEXP = MA = NP`
  contradicting the nondeterministic time hierarchy.  Proved pieces include the Cantor and lazy-diagonalization kernels,
  the clocked-NTM time-class placement, and the **sum-check engine** of `MIP = NEXP` (the round-reduction identity
  `scSum g = roundPoly g 0 + roundPoly g 1`, the recursion, and the base case), plus arithmetization-as-counting and a
  Schwartz–Zippel soundness bound.  The genuinely deep ingredients (`MIP = NEXP` arithmetization+soundness, the IKW
  easy-witness lemma, `NW/IW ⇒ PRG`, `PRG ⇒ MA ⊆ NP`) are isolated as named sockets; the IKW small-prover socket is
  shown to *bottom out at the circuit lower bound* (its other horn is a hard function).

The single load-bearing irreducible input on the BT side is the **exact low-degree representation of `ACC⁰[m]` circuits
for composite `m`** — the socket `ApproxToExactCount` (file `…ACC0ApproxToExact`).  The rest of this document is the
anatomy of that one wall.

---

## 3. The composite-`ACC⁰[m]` wall, triaged

The N-Frame framing reads a circuit through an **observer** (a low-complexity statistic of the computation) and asks
when the observer is *faithful* (recovers the decision) and *cheap* (low-degree, quasipoly).  Used as a proof-search,
this drove the `ApproxToExactCount` wall down to its components.  Each row is a Lean file; every "OK / proved / refuted"
is sorry-free with clean axioms.

| Component of the wall | Verdict | Key proved theorem(s) | File |
|---|---|---|---|
| Easy direction: exact unit-count ⇒ `LowDegRep` | **proved** | `lowDegRep_of_exactUnitCount` | `…ACC0ApproxToExact` |
| Carry seam, qualitative (field power-indicator) | **proved** | `powerIndicator_of_prime`, `not_powerIndicator_primePow`, `field_observer_blind_to_carry`, `crt_residue_observer_suffices` | `…ACC0CarryInvariant` |
| Carry seam, quantitative (Kummer carry count) | **proved** | `carryCount_digits_identity`, `carryCount_eq_zero_iff_not_dvd`, `carryCount_pos_iff_dvd` | `…ACC0KummerCarry` |
| Composite CRT carry profile | **proved** | `carryProfileTrivial_iff_coprime`, `carryProfile_mul` | `…ACC0CRTCarryProfile` |
| Crossing condition named + scaffolded | **proved scaffold** | `fieldObs_carry_blind`, `lowDegRep_of_observer`; socket `CarryRefinementCrossing` | `…ACC0CarryCrossing` |
| Observer **state count** — is it the obstruction? | **No (quasipoly)** | `faithful_iff_le`, `exists_faithful` | `…ACC0CarryObserverSize` |
| **Decode** (count → boolean) — is it the obstruction? | **No (realisable over a field)** | `prime_realizes`, `pointIndicator_eval` | `…ACC0CarryRealization` |
| Single-field full-count degree | **`Θ(N)` — too expensive** | `faithful_decode_degree_ge`, `prime_indicator_natDegree_eq` | `…ACC0CompositeCountDegree` |
| Per-prime layers — low-degree? | **Yes (degree `≤ p-1`, independent of `n`)** | `modpIndicator_totalDegree_le`, `modpIndicator_eval` | `…ACC0LayeredCarryDegree` |
| Cross-field combination — structural root | **incompatible characteristics** | `no_common_char`, `reduction_blind_to_other_prime` | `…ACC0CrossFieldCombination` |
| Single-field route to a non-native `MOD_q` | **NO-GO (Smolensky, already in-arc)** | `crossField_modq_fieldRoute_nogo` `= Layer4.mod_q_indicators_false` | `…ACC0SmolenskyLowerBound` |
| Multi-sorted product-field observer — exists? | **Yes (faithful)** | `modm_iff_modp_and_modq`, `prod_field_iso`, `prodObs_bijective` | `…ACC0MultiSortedObserver` |
| Multi-sorted fast-SAT — counting budget | **OK (composes, quasipoly)** | `jointCells_le_pow`, `multiSorted_savings` | `…ACC0MultiSortedFastSAT` |

Reading the table: the obstruction is **not** the observer's state count (quasipoly), **not** the decode (realisable
over a field), **not** the per-prime layer degree (low), and **not** the multi-sorted counting budget (composes).  The
single-field route is a **proved no-go** (Smolensky, already assembled in the arc as `Layer4.mod_q_indicators_false`).
The multi-sorted product-field observer genuinely *exists and is faithful*.  Everything reducible is settled.

---

## 4. The localization result

> **The composite-`ACC⁰[m]` route reduces, with everything else proved or refuted, to one object:**
> the **per-field `SYM∘AND` representation of the circuit's composite `MOD_m` gates with cross-field mixing handled** —
> equivalently, the Razborov–Smolensky composite lower bound in its operative form.

Precisely:

1. A faithful, cheap (quasipoly) observer for `MOD_m` **must** be multi-sorted — it cannot collapse to a single field
   `F_p`, because a non-native `MOD_q` (`q ≠ p`) is not low-degree over `F_p` (`crossField_modq_fieldRoute_nogo`, the
   in-arc Smolensky bound), and no field carries two prime characteristics at once (`no_common_char`).
2. The multi-sorted observer **exists** and faithfully decomposes `MOD_m = ⋀ᵢ MOD_{pᵢ}` over `∏ᵢ F_{pᵢ}`
   (`modm_iff_modp_and_modq`, `prod_field_iso`, `prodObs_bijective`), with each component low-degree over its own field
   (`modpIndicator_totalDegree_le`), and its fast-SAT **counting budget composes and stays quasipoly**
   (`jointCells_le_pow`, `multiSorted_savings`).
3. The **only** thing not built is the per-prime `SYM∘AND` representation of the circuit's `MOD_m` gates: a single
   `MOD_m` gate cannot live over one `F_{pᵢ}`, and downstream gates **mix** the per-field computations.  This
   **cross-field mixing inside the circuit** (not the readout) is the irreducible core — the open `ACC⁰[composite]`
   wall.

So the N-Frame search did not weaken the wall; it *located* it exactly, and proved that the surrounding program (size,
decode, layer degree, observer faithfulness, counting budget) is *not* where the difficulty lies.

**Further localization (the MOD₆ laboratory, `…ACC0ProductFieldMixing`).**  A *single layer* of mixed `MOD_2`/`MOD_3`
gates feeding a Boolean combiner composes **without collapse**: the output is determined by the product observer state
`(count mod 2, count mod 3) = count mod 6` (`mixedOut_determined`, no axioms; `mixedOut_determined_by_mod6`), with `≤ 6`
cells — the gate outputs are bits and the combiner is Boolean, touching no field arithmetic.  So the obstruction is
**not** single-layer mixing; it is **depth ≥ 2 nesting** — a `MOD_q` gate *fed by* a non-native `MOD_p` output, which
forces arithmetizing `MOD_p` over `F_q` (Smolensky-blocked).  The irreducible core is therefore pinned to the depth
composition of different-modulus `MOD` gates.

---

## 5. What is proved vs. socketed vs. open

- **Proved (sorry-free, clean axioms):** the entire decomposition glue on both routes; the RS combinatorial pipeline;
  the sum-check engine, arithmetization-as-counting, Schwartz–Zippel soundness, multilinear extension; the lazy/Cantor
  diagonalization kernels and clocked time-class placement; and the full carry/observer anatomy of §3 — including the
  in-arc Razborov–Smolensky lower bound `Layer4.mod_q_indicators_false` (`MOD_q ∉ AC⁰[p]` for `q ∤ p`) and
  `Layer3.parity_function_lower_bound`.
- **Socketed (named, honest, decomposed as far as composition allows):** `MIP = NEXP` (arithmetization + multi-prover
  soundness), the IKW easy-witness lemma (shown to reduce to a hard function), `NW/IW ⇒ PRG`, `PRG ⇒ MA ⊆ NP`, and the
  universal-simulation cost of the lazy diagonal.  These are proved classical theorems requiring infrastructure absent
  here; none is faked.
- **Open (the irreducible core):** the per-field `SYM∘AND` representation of composite `MOD_m` gates with cross-field
  mixing handled — the operative form of the composite-`ACC⁰` / Smolensky-strength lower bound.  This is a genuine open
  problem; crossing it requires a new mathematical idea about cross-field circuit mixing, not present here.

A subtlety worth stating plainly: the in-arc Smolensky bound bounds `AC⁰[p]` (single prime, where `MOD_q` is the
*forbidden* gate).  It is **not** `NEXP ⊄ ACC⁰`, which concerns `ACC⁰[m]` with the `MOD_m` gate *available* — Williams'
open territory.  The localized core is exactly the gap between these.

---

## 5b. Refined conclusion — the wall is *algebraic*, not cut (entries 251–256)

Pushing the localized core (§4) further produced a clean separation of two notions, both machine-checked:

* **Cut-expansion governs *DP tractability* exactly.**  Disjoint (overlap rank 1, `…ACC0CrossFieldCountCore`),
  block-diagonal (bounded local overlap, `…ACC0BlockOverlapCount`), and bounded-treewidth (separator conditioning,
  `…ACC0TreewidthCount` `separator_factor`) incidence ⇒ the cross-field count factors by an N-Frame observer DP.  The
  positive side is proved up the parametrized-complexity ladder.
* **Cut-expansion is *not* count-hardness.**  The full-support family (`…ACC0ExpanderFamilies` `fullSupport_expander`)
  is a separator-expander (no small separator) whose count is easy when its gates are redundant.  So no-small-separator
  is necessary for DP-failure but **not sufficient** for the count lower bound.
* **The correct hypothesis is *algebraic expansion*.**  `AlgExpander` (`…ACC0AlgebraicExpansion`) = the gate-indicator
  functions are *linearly independent over the field* `F` (high gate-function rank).  This is about the gate functions,
  not the cut; it rules out the redundant-gate degeneracy (`not_algExpander_of_duplicate`).

> **Refined wall.**  Bounded separator/treewidth incidence is tractable by N-Frame observer factorization (proved).
> The remaining `ACC⁰[composite]` wall is **algebraically-independent cross-field fire-counting**: *linearly-independent
> `F_p`-gate indicators ⇒ the mod-`q` fire-count needs superpolynomial resources* — the Razborov–Smolensky theorem in
> its sharpest form, socketed as `AlgExpanderCountObstruction`.

## 5c. The corrected bridge — the `ACC⁰[composite]` wall, precisely (entries 256–261)

Counterexample-driven refinement (the framework breaking its own weak invariants) produced the correct, validated
hardness hypothesis.  The wall is **not** mere graph expansion, **nor** indicator independence alone:

> **`ACC⁰[composite]` wall = cross-field fire-counting for gate families that are both (a) *non-redundant* —
> linearly-independent indicators (`AlgExpander`, `…ACC0AlgebraicExpansion` / `…ACC0IndicatorRank`) — and (b)
> *co-firing-rich* — many distinct, large simultaneous fire-patterns (`CoFiringRich` / `PatternRich`,
> `…ACC0CoFiring` / `…ACC0FirePatternRichness`).**

Each clause is validated by a *proved* separating example: the full-support family (cut-expander, redundant ⇒ easy,
`…ACC0ExpanderFamilies`) and the parallel-affine family (`AlgExpander` but disjoint/no co-firing ⇒ fire-count `≤ 1`,
easy, `…ACC0AffineHyperplaneLowerBound`).  The corrected socket is

> `AlgExpander gates → CoFiringRich gates → CrossFieldCountHard gates`,

non-vacuous with a **proven hard instance**: the dictator/`MOD_q` family satisfies both and its mod-`q` fire-count is
`MOD_q`, hard in `AC⁰[p]` by the in-arc Razborov–Smolensky theorem `Layer4.mod_q_indicators_false`.  The general socket
is Smolensky-strength (the open core); the implication `CrossFieldCountHard ⇒ ACC⁰[composite] lower-bound component`
(upstream of Williams `NEXP ⊄ ACC⁰`) is the named bridge.

## 5d. A second proved family + the real lower-bound target and its RS attack (entry 262)

To move from cataloguing invariants to *connecting the stack to a lower bound*, the program now (a) exhibits a **second**
genuinely-different family satisfying both hardness clauses, (b) names the single missing theorem, and (c) names its
Razborov–Smolensky attack invariant — all in `…ACC0VaryingAffinePatterns`.

* **Second proved family — varying-direction affine hyperplanes.**  `varGate a b i x := decide (⟨a i, x⟩ = b i)`: each
  gate `i` is the affine hyperplane with its *own* direction `a i` (vs the parallel family's one fixed all-ones
  direction).  Under **general position** (`dotEval a : x ↦ (⟨a i, x⟩)ᵢ` *surjective* — for `n = s` the direction
  matrix is invertible), every subset is realized as a fire-pattern, giving `PatternRich (2^s)`
  (`varyingAffine_patternRich`), all gates co-firing on one input `CoFiringRich s` (`varyingAffine_coFiringRich`), and
  linear independence `AlgExpander` via private witnesses (`varyingAffine_algExpander`) — all PROVED.  The **parallel**
  family is the degenerate easy subcase: its all-fire pattern is never realized, so general position fails
  (`parallel_pattern_image_ne_univ`).
* **The single named missing theorem.**  `PatternRichCrossFieldLowerBound`: `AlgExpander → PatternRich (2^s) →
  CrossFieldCountHard`.  This replaces the prose "general socket" with one named target.
* **The RS attack invariant.**  `NonNativeDegreeLowerBound` factors the target through *non-native polynomial degree
  over `F_q`* (`q ≠ p`) — the measure closest to Razborov–Smolensky: `(AlgExpander ∧ PatternRich ⇒ HighNonNativeDegree)
  ∧ (HighNonNativeDegree ⇒ CrossFieldCountHard)`.  `patternRich_lb_of_nonNativeDegree` (PROVED) shows this route
  suffices for the target.
* **Wiring it in.**  `varyingAffine_ACC0_chain` (PROVED): *given* the lower-bound socket and the §5c bridge
  `crossFieldHard_to_ACC0Component`, the varying-affine family yields the `ACC⁰[composite]` component **with
  `AlgExpander` and `PatternRich` discharged** for this family.  Two proved families (dictator/`MOD_q`, varying-affine)
  now reach the antecedent; only the two named sockets (the lower bound + the bridge) remain open.

## 5e. A third proved family — Reed–Muller / low-degree polynomial gates, closest to RS (entry 263)

The third family is the one closest to Razborov–Smolensky, obtained by a clean reduction (`…ACC0ReedMullerGates`):

> **A low-degree polynomial gate is an affine gate in the monomial feature space.**

Gate `i` is a degree-`≤ d` polynomial `Pᵢ` over `ZMod p`, firing iff `Pᵢ(x) = bᵢ`.  Writing `Pᵢ = ∑_m coeffᵢ,m · m`
and letting `φ(x)_m := m(x)` (the monomial feature map, `m` over degree-`≤ d` monomials — `RM(d,n)` is the span), we get
`Pᵢ(x) = ⟨coeffᵢ, φ(x)⟩`, so `rmGate = varGate ∘ φ`.

* **Reduction made exact.**  `rmGate_degree_one_eq_varGate` (PROVED): the degree-1 features `feat m x = x_m` give
  `rmGate = varGate` — the §5d varying-affine family is the degree-1 special case.
* **Inheriting the invariants.**  Under **feature general position** (`rmEval feat coeff : x ↦ (Pᵢ(x))ᵢ` *surjective* —
  Reed–Muller non-degeneracy / large code distance), all of §5d lifts: `rmGate_patternRich` (`PatternRich (2^s)`),
  `rmGate_coFiringRich` (`CoFiringRich s`), `rmGate_algExpander` (`AlgExpander`) — all PROVED.
* **Wiring it in.**  `rmGate_ACC0_chain` (PROVED): given the §5d lower-bound socket and the §5c bridge, Reed–Muller
  yields the `ACC⁰[composite]` component with `AlgExpander`/`PatternRich` discharged.  The RS attack invariant
  `NonNativeDegreeLowerBound` applies verbatim (non-native degree over `F_q` = Reed–Muller distance — the literal RS
  measure).

**Net:** three proved families (dictator/`MOD_q`, varying-affine, Reed–Muller) now reach the count-hardness antecedent,
validating `AlgExpander ∧ PatternRich` across three distinct geometries; the wall is localized to the single named
`PatternRichCrossFieldLowerBound` with an RS-flavoured attack route.

## 5f. Attacking the wall — the Smolensky counting engine, PROVED; the target reduced to one analytic socket (entry 264)

The direct attack on `PatternRichCrossFieldLowerBound` along the non-native degree route (`…ACC0NonNativeDegree`).  The
route factors into two halves:

* **(B) richness ⇒ high non-native degree** — Smolensky's *counting* argument;
* **(A) small resources ⇒ low non-native degree** — the *polynomial-method* approximation of `AC⁰[p]` circuits.

This file **proves the entire (B) engine** — the mechanism by which the route works — and reduces the target to the
*single* named analytic socket (A).

* **The counting engine (PROVED).**  `lowDegreeDim n D := ∑_{i≤D} C(n,i)` is the dimension of the non-native
  degree-`≤ D` function space; `lowDegreeDim_lt_two_pow` proves `D < n ⇒ lowDegreeDim n D < 2^n` (the low-degree space
  is strictly smaller than the full space — why low-degree polynomials cannot compute rich functions).
* **The rank pigeonhole (PROVED).**  `exists_notMem_of_finrank_lt` (a family spanning more than `finrank W` escapes
  `W`) and `algExpander_forces_high_degree`: an `AlgExpander` family of `s` gates with `lowDegreeDim n D < s` must
  contain a gate of non-native degree `> D`.  *Too many independent gates cannot all be low-degree* — this is the actual
  Smolensky lower-bound mechanism, machine-proved.
* **The count is `MOD_q` (PROVED).**  `crossFieldCount_eq_firePattern_card_mod`: the cross-field count is `|firing
  pattern| mod q` = `MOD_q` on the pattern indicator, the function hard by the in-arc `Layer4.mod_q_indicators_false`.
* **The reduction (PROVED, modulo one socket).**  `nonNativeDegreeLowerBound_via_counting` builds a concrete
  `NonNativeDegreeLowerBound` with the (B) half *proved* by the engine and the (A) half = the socket
  `PolynomialMethodApproximation` (the probabilistic polynomial method, `AC⁰[p] ⇒` low-degree approximation — the
  genuine open RS core, instances = in-arc `Layer3`/`Layer4`).  `patternRichCrossFieldLowerBound_via_nonNativeDegree`
  feeds it through §5d's `patternRich_lb_of_nonNativeDegree` to the target.

**Net:** the Smolensky *counting + rank* mechanism — the part that makes the non-native degree route work — is now
machine-proved as reusable kernels, and the entire open target `PatternRichCrossFieldLowerBound` is reduced to *two*
named sockets: the analytic `PolynomialMethodApproximation` and the secondary `LowDegreeDimensionIdentity`.

## 5g. Discharging the dimension socket — the multilinear basis over `F` (entry 265)

The secondary socket `LowDegreeDimensionIdentity` (`finrank W = lowDegreeDim n D`) is now **discharged completely** by
building the multilinear monomial basis over an arbitrary field `F` (`…ACC0MultilinearBasis`) — the `F`-analogue of the
in-arc `anf_involutive` (which did this over `F₂`).

* **The basis (PROVED).**  `mlMon S x := ∏_{i∈S} (xᵢ : F)` over the Boolean cube.  The key is the *triangular
  evaluation* `mlMon_eval`: `χ_S(e_T) = [S ⊆ T]` at `e_T(i) = [i ∈ T]` (the unitriangular subset/zeta matrix).
  `mlMon_linearIndependent` then proves the `2ⁿ` monomials independent over `F` by Möbius/strong induction on the subset
  lattice (`∑_{S ⊆ T} c_S = 0 ∀T ⇒ c_T = 0`) — a genuine general-field generalisation of `anf_involutive`.
* **The dimension (PROVED).**  `card_subtype_card_le`: `#{S : S.card ≤ D} = lowDegreeDim n D` (partition by
  cardinality); `lowDegreeSubmodule_finrank`: `span {χ_S : |S| ≤ D}` has dimension exactly `lowDegreeDim n D`.
* **Socket discharged (PROVED).**  `lowDegreeDimensionIdentity_discharged` gives `LowDegreeDimensionIdentity
  (lowDegreeSubmodule n D) n D`; `patternRichCrossFieldLowerBound_no_dimSocket` then shows that for Boolean gate
  families the open target rests on the **single** remaining socket `PolynomialMethodApproximation`.

**Net:** after entries 264–265, the open target `PatternRichCrossFieldLowerBound` is reduced to the *one* analytic
socket `PolynomialMethodApproximation` — the probabilistic polynomial method (`AC⁰[p] ⇒` low-degree approximation).  Both
the Smolensky counting/rank engine *and* the multilinear-basis dimension identity are machine-proved.  That last socket
is the genuine open Razborov–Smolensky core; its concrete instances are already in-arc (`Layer3`/`Layer4`), but the
general form is exactly the `ACC⁰[composite]` wall and is not faked.

## 5h. Into the last socket — the single-gate polynomial method (entry 266)

The first rung *inside* `PolynomialMethodApproximation`: how one gate is represented/approximated by a polynomial over
`F` (`…ACC0AndGateApprox`).  The genuinely-provable algebraic substrate is built; the probabilistic boosting is the one
open ingredient.

* **The Fermat engine (PROVED).**  `fermat_indicator`: over `F_p`, `y^{p-1} = [y ≠ 0]` (Fermat's little theorem) — the
  degree-`p-1` device that turns a *sum* of literals into a `0/1` value, *independent of fan-in*.
* **Exact monomials (PROVED).**  `andExact` (`AND_n = ∏ᵢ xᵢ`) and `orExact` (`OR_n = 1 − ∏ᵢ(1 − xᵢ)`), both degree `n`.
* **The clause indicator (PROVED).**  `clauseIndicator`: `1 − (∑_{i∈S} xᵢ)^{p-1} = [∑_{i∈S} xᵢ = 0]`, degree `p-1`
  *regardless of `|S|`* — the RS building block.
* **Landing in the framework (PROVED).**  `andIndicator_mem_lowDegree`: the AND indicator is `mlMon univ` (§5g), hence
  lies in `lowDegreeSubmodule n n`.  `and_exact_is_zeroError_approximation` witnesses the approximation socket at the
  exact endpoint `(D = n, k = 0)`.
* **The open ingredient.**  `RandomizedLowDegreeApproximation F n D k` (a degree-`≤ D` polynomial agreeing with `AND_n`
  except on `≤ k` inputs).  The RS content — `D ≪ n` with `k ≤ ε·2ⁿ` via random restriction + boosting of the clause
  indicators — is the single-gate base case of `PolynomialMethodApproximation`, and is left as the named socket.

**Net:** the polynomial method's *per-gate algebra* is now machine-proved (Fermat indicator, exact AND/OR, the
fan-in-free clause indicator, membership in the degree-`≤ n` submodule), with a proved zero-error endpoint.  The single
remaining open step is the *low-degree* probabilistic approximation — the irreducible analytic core of Razborov–Smolensky
(`ACC⁰[composite]`, entry-238 `CarryRefinementCrossing`).  Not faked, not a separation.

## 5i. The boosting step — error reduction to `2^{-k}` (entry 267)

The mechanism that turns one weak clause indicator into a good approximator (`…ACC0Boosting`).  A single Fermat clause
indicator is correct with probability `≥ 1/2` on each nonzero input; **boosting** combines `k` of them.

* **The boosted polynomial (PROVED).**  `boostPoly e x := 1 − ∏ⱼ (1 − eⱼ x)` is the *OR* of the `k` approximators:
  `boostPoly_eq_one` (some `eⱼ` fires ⇒ `1`), `boostPoly_eq_zero` (all silent ⇒ `0`), degree `k·(p-1)`.
* **Agreement (PROVED).**  `boost_correct`: boost equals the Boolean target under the good event.
* **The error-reduction core (PROVED).**  `boost_correct_off_iInter`: boost agrees with the target on every input
  *outside the intersection* of the `k` error sets — `bad(boost) ⊆ ⋂ⱼ bad j`.  This is exactly the boosting step.
* **The probabilistic ingredients (sockets).**  `SingleSubsetAgreement` (per-clause `≥ 1/2`, provable over `F₂` by the
  parity-toggle involution) and `IndependentIntersectionBound` (independence ⇒ `|⋂ⱼ bad j| ≤ ∏ⱼ |bad j|/2^{n(k-1)}`).
  Composed with the proved boosting they drive `|bad(boost)| ≤ 2ⁿ·2^{-k}`.

**Net:** the boosting *algebra* (OR-of-approximators, error-set intersection `bad(boost) ⊆ ⋂ⱼ bad j`) is machine-proved.
What remains inside `PolynomialMethodApproximation` is now reduced to two sharply-named probabilistic facts — the
per-clause `≥ 1/2` agreement and the independence of the random subsets — which together with the proved per-gate and
boosting algebra would complete the single-gate low-degree approximation.  Those two are the residue of the open
Razborov–Smolensky core.  Not faked, not a separation.

## 5j. The per-clause `1/2` — discharging `SingleSubsetAgreement` over `F₂` (entry 268)

The first of the two probabilistic residues is now *proved* over `F₂` (`…ACC0SingleSubsetF2`), and there it is *exactly*
`1/2`, by a clean parity-toggle involution.

* **The toggle (PROVED).**  For a nonzero input `x`, fix `j` with `xⱼ = true`.  `tog j S := S △ {j}` is an involution
  (`tog_tog`, `tog_injective`) that *flips* the clause parity: `par_tog` proves `parF2 x (tog j S) = parF2 x S + 1`
  over `F₂` (the `j`-term contributes `1`).
* **Equinumerous fibers (PROVED).**  `tog j` therefore bijects `{S : par = 0} ↔ {S : par ≠ 0}`, so the two parity
  fibers have equal cardinality; as they partition the `2ⁿ` subsets, each is `2ⁿ⁻¹`.
* **The bound (PROVED).**  `singleSubsetAgreement_two`: `2ⁿ ≤ 2·#{S : par x S ≠ 0}` — i.e. `SingleSubsetAgreement 2 n x`.
  The clause fires correctly on exactly half the subsets.

**Net:** the per-clause `≥ 1/2` agreement — the *base probabilistic primitive* of the polynomial method — is now
machine-proved over `F₂`.  Of the entire Razborov–Smolensky chain, the **only** ingredient still socketed for the
single-gate low-degree approximation is `IndependentIntersectionBound` (independence of the random subsets).  Every other
layer — counting, rank pigeonhole, multilinear dimension, per-gate Fermat/exact reps, boosting error-reduction, and now
the per-clause `1/2` — is proved.  Not faked, not a separation.

## 5k. Independence — the joint `2^{-k}` bound (entry 269)

The second probabilistic residue is now proved (`…ACC0Independence`), in the honest model where the `k` random subsets
are *independent*: the **product space `∀ j, Y j`** of the `k` draws.

* **Independence factorization (PROVED).**  Each clause's bad event is a cylinder (depends only on its own draw), so the
  joint bad event `⋂ⱼ bad j = {y : ∀ j, y j ∈ B j}` is the product box `Fintype.piFinset B`, and `jointBad_card` gives
  `|⋂ⱼ bad j| = ∏ⱼ |B j|`.
* **The `2^{-k}` bound (PROVED).**  With each clause bad on at most half its draws (`2·|B j| ≤ |Y j|`, the per-clause
  `1/2` of §5j), `independent_intersection_bound` / `joint_error_le` give `2^k·|jointBad| ≤ |∀ j, Y j|` — joint failure
  on at most a `2^{-k}` fraction of the randomness space.

**Net:** both probabilistic residues of `PolynomialMethodApproximation` are now machine-proved — the per-clause `1/2`
(§5j) and the independence `2^{-k}` (§5k).  Composed with the proved boosting (§5i, `bad(boost) ⊆ ⋂ⱼ bad j`) and the
proved per-gate algebra (§5h), the **entire single-gate low-degree approximation is assembled from proved parts**.  The
only ingredient still socketed is the *structural* lifting from a single gate to a circuit to an observer
(`PolynomialMethodApproximation` proper) — combinatorial bookkeeping over the gate graph, not a new analytic idea.  Every
analytic layer of Razborov–Smolensky — counting, rank, multilinear dimension, Fermat indicator, exact reps, boosting,
per-clause `1/2`, independence `2^{-k}` — is now proved.  Not faked, not a separation.

(Note: there is also a *concrete `F₂` circuit* development of the same structural lifting in the repository — an
independent arc `…ACC0{CircuitApprox, ErrorAccumulation, SmallErrorForm, LayerCompose, CompositionCorrect, OrStep,
DepthInduction}` (committed, sorry-free): a `Circ` datatype, `MvPolynomial`/`totalDegree` approximants, `error_union_bound`,
`or_step`/`and_step`, and the depth induction `approximable_exists` for **MOD-free** circuits.  It converges with the
abstract kernel here on the same wall — composite `MOD`.)

## 5l. The `MOD_p` gate — native easy, non-native hard (entry 270)

The third `AC⁰[p]` gate, completing the per-gate kernel beyond `AND`/`OR` (`…ACC0ModpGate`).  `MOD_p` fires iff the
Hamming weight is `≡ 0 mod p`.

* **Exact native representation (PROVED).**  `modp_native_repr`: `1 − (∑ᵢ xᵢ)^{p-1} = [MOD_p]` over `F_p`, via the
  Fermat indicator (§5h) — degree `p-1`, *fan-in-free*.  `MOD_p` is *easy over its own field*: constant native degree.
* **`MOD_p` is the `SYM`/count object (PROVED).**  `modpGate_fires_iff`: `MOD_p ⇔ p ∣ #{true inputs}` — the
  weight-divisibility / cross-field-count gate (§3, entry 251), the `SYM` of Beigel–Tarui `SYM∘AND`.
* **The dichotomy.**  Native (`F_p`) is degree `p-1` (easy, proved); *non-native* (`F_ℓ`, `ℓ ≠ p`) is high degree — the
  Razborov–Smolensky obstruction `ModpNonNativeHardOverOtherField`, whose mechanism is the proved counting/rank engine
  (§5f, `algExpander_forces_high_degree`) and whose *composite-modulus* form is the open wall (§3, entry 238).

**Net:** all three `AC⁰[p]` gate types now have their per-gate polynomial behaviour proved — `AND`/`OR` (§5h) and `MOD_p`
(§5l) — and the native/non-native split is made precise: every gate is *low-degree native*, and the entire difficulty is
concentrated in the *non-native composite-`MOD`* lower bound, which is the single open wall.  Not faked, not a separation.

## 5m. The native/non-native bridge — split made theorem-level (entry 271)

The assembly step (`…ACC0NativeNonNativeBridge`): the native/non-native split, hitherto stated as commentary, is now a
*theorem*, with `MOD_p` wired to the `PatternRich`/cross-field socket via the **dictator family** `gᵢ(x) := xᵢ`.

* **Native (PROVED).**  `modp_native_easy`: over `F_p`, `MOD_p` has the exact degree-`(p-1)` representation (§5l) —
  the native side is easy.
* **The cross-field identity (PROVED).**  `modp_iff_dictator_crossFieldCount_zero`: `MOD_p` fires iff the dictator
  cross-field count mod `p` is `0` — `MOD_p` *is* the entry-251 cross-field-count object (`modpGate_fires_iff` +
  `Nat.dvd_iff_mod_eq_zero`).
* **The non-native target (PROVED antecedent).**  `dictator_meets_patternRich_socket`: the dictator family is
  `AlgExpander ∧ PatternRich (2^s)` (§5c–§5d) — it satisfies the antecedent of `PatternRichCrossFieldLowerBound` (§5d).
  So the non-native hardness of `MOD_p`'s cross-field count over `F_q` *is* that central socket.
* **The split (PROVED).**  `native_nonnative_split` packages both: native exact `F_p` rep + cross-field identification.

**Net:** the path from here is pure assembly.  The split is theorem-level; the non-native object is identified with the
central socket `PatternRichCrossFieldLowerBound`, whose antecedent is provably met and which §5f already reduced to the
single `PolynomialMethodApproximation` ingredient — for which §5f–§5l supply the entire proved RS analytic kernel.  The
one open theorem is the non-native (composite-`MOD`) lower bound itself — the wall.  Not faked, not a separation.

## 5n. The polynomial-method bridge — `small AC⁰[p] ⇒ low-degree approximation` (entry 272)

Roadmap step 3, a *bridge file* (`…ACC0PolynomialMethodApproximation`) connecting the abstract `F_p` kernel (§5f–§5m)
and the concrete `F₂` circuit arc (the committed `…ACC0{CircuitApprox, OrStep, DepthInduction, ...}`) **without
re-proving either**.

* **The notions coincide (PROVED).**  `LowDegreeApprox f D E` (an `F₂`-poly of degree `≤ D` erring on `≤ E` inputs) is
  the common notion; `approximable_iff_lowDegreeApprox` (`Iff.rfl`) shows Codex's `Approximable` *is* it.
* **The bridge direction (PROVED).**  `small_AC0p_observer_implies_lowDegreeApprox`: every `MOD`-free `AC⁰` circuit's
  function has a low-degree approximant — re-exporting the committed `approximable_exists`.
* **The contradiction (PROVED).**  `polynomial_method_contradiction`: a degree-`≤ D` approximant *and* a high-degree
  requirement give `False`.
* **The two quantitative sockets.**  `QuantitativeDepthBound` (size/depth → `(D,E)`, threading the committed
  `or_step`/`and_step` + boosting `t`) and `SmolenskyNonNativeLowerBound` (`¬ LowDegreeApprox` for the non-native target
  — the wall, mechanism §5f, composite §3/entry 238).

**Net:** the two parallel RS developments are now formally bridged, the "small observer ⇒ low-degree approximation"
direction is re-exported and proved, and the final contradiction is assembled.  What remains is exactly the two
quantitative inputs — the size/depth → degree refinement (assembly of committed pieces) and the Smolensky lower bound
(the wall).  Supplying both completes the *prime*-`MOD` lower bound; the *composite* case feeds `ACC0CompositeComponent`
→ Williams and is the single open barrier.  Not faked, not a separation.

## 5o. The quantitative depth bound — the clean per-layer step (entry 273, roadmap (A))

Roadmap step (A), built *on top of* the committed `or_step`/`and_step` (`…ACC0QuantitativeDepthBound`).  The committed
steps left the gate-boosting error in the awkward form `(2^k)^t·Eg ≤ 2ⁿ·(2^{k-1})^t`; this entry extracts the clean
fraction.

* **The clean per-gate bound (PROVED).**  `gate_error_le`: that awkward bound (with `1 ≤ k`) cancels to `2^t·Eg ≤ 2ⁿ` —
  each gate's boosting error is at most a `2^{-t}` fraction of the inputs, *independent of fan-in*.
* **The clean per-layer step (PROVED).**  `or_layer_quant`/`and_layer_quant`: `or_step`/`and_step` repackaged with that
  clean bound (degree `≤ t·D`, error `≤ k·E + Eg`, `2^t·Eg ≤ 2ⁿ`).
* **The degree closed form (PROVED).**  `pow_depth_degree`: `(·t)` iterated `d` times on `D₀` is `t^d·D₀` — depth-`d`
  approximant degree `≤ t^d·D₀`.

**Net:** the quantitative per-layer ingredient — the part `or_step` left awkward — is now clean and proved (the gate
error is a transparent `2^{-t}` fraction), and the degree closed form `t^d·D₀` is in hand.  The remaining piece of
`QuantitativeDepthBound` is the structural iteration over the committed `Circ` (apply the layer step gate-by-gate,
accumulating degree `t^d`, error `size·2ⁿ·2^{-t}`) — the quantitative refinement of `approximable_exists`, which lives in
the committed circuit arc.  Of roadmap (A), the clean analytic content is done; only that structural iteration and the
Smolensky wall (B) remain.  Not faked, not a separation.

## 5p. The quantitative iteration — the recurrence solved in closed form (entry 274, roadmap step 1)

The iteration math (`…ACC0QuantitativeIteration`), on top of entry 273.  The per-layer estimates become the full
closed-form bound.

* **Error accumulation (PROVED).**  `error_accumulation`: the per-gate `2^{-t}` errors (entry 273) sum, via the
  committed union bound (`E ≤ ∑ᵢ Eg i`), to `2^t·E ≤ m·2ⁿ`; `error_accumulation_size` gives `2^t·E ≤ size·2ⁿ` — the
  total error is a `size·2^{-t}` fraction.
* **The combined solver (PROVED).**  `quantitative_iteration_closed_form`: degree `≤ t^d·D₀` (entry 273) ∧
  `2^t·E ≤ m·2ⁿ` — the closed-form solution of the size/depth/error recurrence.

**Net:** the analytic content of the iteration is done — the closed-form degree `t^d·D₀` and error `size·2^{-t}` are
proved.  The one remaining piece of `QuantitativeDepthBound` is the structural `Circ` recursion
(`CircuitStructuralRecursion`, the committed arc's quantitative `approximable_exists`) that feeds the per-gate
decomposition into the solver.  After that, the route's only open theorem is the Smolensky wall
(`SmolenskyNonNativeLowerBound`) — for composite modulus, entry-238 `CarryRefinementCrossing`.  Not faked, not a
separation.

## 5q. The Smolensky pigeonhole — the counting/rank half of the wall, proved (entry 275, step 4)

The attack on the wall itself (`…ACC0SmolenskyPigeonhole`).  The Razborov–Smolensky non-native lower bound splits into
**(counting/rank)** + **(degree-halving representation)**; this entry *proves the counting/rank half* via the §5f rank
kernel and §5g dimension, isolating the degree-halving as the single residual socket.

* **Point indicators independent (PROVED).**  `ptInd_linearIndependent`: the point indicators over a finset `S` span a
  space of dimension `|S|`.
* **The pigeonhole (PROVED).**  `smolensky_pigeonhole`: if every point indicator of `S` lies in `W` with
  `finrank W < |S|`, then `False` — the `|S|`-dim span cannot embed in `W` (§5f `exists_notMem_of_finrank_lt`).
  `smolensky_pigeonhole_lowDegree` instantiates `W = lowDegreeSubmodule n D'` (§5g): a good set bigger than the
  low-degree dimension forces a high-degree point function.
* **The reduction (PROVED).**  `smolensky_lower_bound_via_pigeonhole`: degree-halving + (good set large) ⇒ `False`.
* **The residual socket.**  `SmolenskyDegreeHalving` — a degree-`D` approximator makes every good-set point function
  degree `≤ n/2+D` (the Razborov–Smolensky representation lemma, using `MOD_q`'s algebra over `F_p`).  The genuine
  remaining core; composite = §3/entry-238 `CarryRefinementCrossing`.

**Net:** the wall's *counting/rank half* is now machine-proved — a large good set provably cannot have all-low-degree
point functions (the §5f pigeonhole, §5g dimension).  The Smolensky lower bound is reduced to the *single* socket
`SmolenskyDegreeHalving` (the degree-halving representation lemma).  Of the entire ACC route, the only open content is
now that one classical representation lemma (prime case) / the composite carry-crossing (entry 238) plus the committed
arc's structural `Circ` recursion.  Not faked, not a separation.

## 5r. The Smolensky degree-halving — the prime-case substitution identity (entry 276)

The attack on the residual socket `SmolenskyDegreeHalving`, **prime case only** (`…ACC0SmolenskyDegreeHalving`) —
*composite untouched* (the §3/entry-238 `CarryRefinementCrossing` wall).  The algebraic core of degree-halving is proved.

* **The substitution identity (PROVED).**  `smolensky_substitution`: over the `{±1}` encoding (`yᵢ² = 1`),
  `∏_{i∈S} yᵢ = (∏ᵢ yᵢ)·(∏_{i∈Sᶜ} yᵢ)` — the full product is `∏_S·∏_{Sᶜ}` and `(∏_{Sᶜ})² = 1`, so it collapses to
  `∏_S` (closed by `linear_combination`, sidestepping the dependent-motive `rw` on the `univ` product).
* **The halving (PROVED).**  `compl_card_lt_half` (`|S| > n/2 ⇒ 2·|Sᶜ| < n`) + `monomial_halving`: a high-degree
  monomial equals the *full product* times a *sub-half-degree* complement.
* **The residual socket.**  `FullProductLowDegreeOnGoodSet` — replacing the full product by the degree-`D` approximator
  on the good set; combined with `monomial_halving`, every monomial on `G` has degree `≤ n/2 + D`, discharging
  `SmolenskyDegreeHalving` (§5q).  Prime = textbook; composite = §3/entry-238.

**Net:** the algebraic heart of Smolensky's degree-halving — the `{±1}` substitution trading a degree-`|S|` monomial for
the full product times a degree-`(n−|S|)` complement — is machine-proved.  With §5q's pigeonhole, the prime-`MOD` lower
bound now rests on the *single* circuit-specific socket `FullProductLowDegreeOnGoodSet` (the approximator equals the full
symmetric product on its good set).  Composite modulus remains the open `CarryRefinementCrossing` wall.  Not faked, not a
separation.

## 5s. The prime-case wiring — replacing the full product by the approximator (entry 277, step 1)

The bridge from entry 276 into the proven approximation machinery (`…ACC0FullProductGoodSet`).  Entry 276's residual
socket `FullProductLowDegreeOnGoodSet` needed *the approximator to equal the full product on the good set*; this entry
shows that agreement is exactly what replaces the full product by the approximator inside the halving.

* **The wiring (PROVED).**  `fullProduct_replace_on_goodSet`: given `∀ x ∈ G, P x = ∏ᵢ yencₓ i` (the approximator agrees
  with the full product on the good set), then on `G`, `∏_{i∈S} yencₓ i = P x · ∏_{i∈Sᶜ} yencₓ i` — substitute the
  agreement into §5r's `smolensky_substitution`.  The hard full product is replaced by the degree-`D` approximator.
* **The halving packaged (PROVED).**  `monomial_eq_approx_times_lowComplement`: for `|S| > n/2`, on `G` the high-degree
  monomial equals approximator × sub-half-degree complement (`2·|Sᶜ| < n`).
* **The residual socket.**  `ApproximatorDegreeBound` — `P` degree `≤ D` ⇒ the product has degree `≤ D + n/2`, so
  good-set point functions ∈ `lowDegreeSubmodule n (D + n/2)`, discharging `SmolenskyDegreeHalving` (§5q/§5r).

**Net:** the *agreement input* of the degree-halving socket — formerly the unspecified "approximator = full product on
good set" — is now wired to the approximation machinery: it is precisely what boosting (§5i) / `Approximable` (committed
arc) supply (the `AC⁰[p]` approximator agreeing with the symmetric target off a small bad set).  For the **prime case**,
the Smolensky lower bound is now assembled from proved parts: approximation (good set large) → full-product replacement
(§5s) → degree-halving (§5r) → pigeonhole contradiction (§5q), modulo only `ApproximatorDegreeBound` (product-degree
bookkeeping).  **Composite modulus stays the open `CarryRefinementCrossing` wall** (§3/entry 238) — deliberately
untouched.  Not faked, not a separation.

## 5t. The prime Smolensky lower bound, assembled + wired to ACC (entry 278, steps 3–4)

The capstone of the prime route (`…ACC0SmolenskyPrime`): the prime-case Smolensky lower bound, assembled from the proved
pieces, and wired to `ACC0CompositeComponent`.

* **Step 3 (PROVED).**  `smolensky_prime_goodset_bound`: under degree-halving (§5r/§5s), `|G| ≤ lowDegreeDim n D'` (the
  pigeonhole §5q in positive form — the good set is bounded by the low-degree dimension).  `no_small_approximator`: with
  a large good set (`2ⁿ − E ≤ |G|`, the approximation machinery's small-bad-set output) and the binomial tail
  (`lowDegreeDim n D' < 2ⁿ − E`), this is a contradiction — *no low-degree small-error approximator of the symmetric
  `MOD`/parity target exists*.
* **Step 4 (PROVED).**  `prime_route_to_ACC0Component`: the resulting `CrossFieldCountHard` feeds the §5c/entry-261
  bridge to `ACC0CompositeComponent`, the component upstream of Williams.

**Net:** the entire prime-case Razborov–Smolensky route is now assembled from machine-proved parts — approximation →
full-product replacement (§5s) → degree-halving (§5r) → pigeonhole bound (§5q) → contradiction (`no_small_approximator`)
→ `ACC0CompositeComponent` (§5c) — modulo only mechanical/standard residuals (`ApproximatorDegreeBound` product-degree
bookkeeping, the binomial tail, the prime-case `CrossFieldCountHard` identification) and the committed arc's structural
`Circ` recursion.  **Composite modulus is the one genuinely-open object** — the `CarryRefinementCrossing` wall (§3/entry
238), deliberately untouched.  Not faked, not a separation.

## 5u. Prime mechanical closure — the bookkeeping discharged (entry 279, step 1)

The mechanical residuals of the prime route (`…ACC0PrimeMechanicalClosure`).

* **`ApproximatorDegreeBound` discharged (PROVED).**  `approximator_times_complement_totalDegree`: the degree of a
  product is at most the sum of degrees (`MvPolynomial.totalDegree_mul`) — the approximator (degree `≤ D`) times the
  complement monomial (degree `≤ n/2`, §5s) has degree `≤ D + n/2`.  This is exactly the product-degree bookkeeping the
  degree-halving needed.
* **The clean prime theorem (PROVED, no axioms).**  `prime_smolensky_route_closed`: the prime hardness
  (`CrossFieldCountHard`, from §5t's `no_small_approximator`) yields `ACC0CompositeComponent` via the §5c bridge.
* **Honestly not discharged.**  The *binomial tail* (`lowDegreeDim n (n/2+D) < 2ⁿ − E`, `D = O(√n)`) is the standard
  Chernoff estimate, kept as a numeric hypothesis (the Smolensky parameter regime), not faked; the committed `Circ`
  recursion is the circuit arc's.

**Net:** the prime-`ACC⁰[p]` lower bound is now assembled with every *mechanical* part machine-proved — degree-halving
(§5r), wiring (§5s), pigeonhole bound (§5q/§5t), product-degree (§5u) — and only standard parameter estimates (the
binomial tail) and the committed `Circ` recursion outside Lean.  **The single genuinely-open frontier is composite
modulus** — the `CarryRefinementCrossing` wall (§3/entry 238).  It is not bookkeeping; it needs a new idea, and is left
as the one honest open object.

## 5v. The composite wall, smallest case — MOD₆ separated layers cross fields (entry 280, step 5)

The honest composite attack (`…ACC0Mod6SeparatedLayers`): take `6 = 2·3` and the natural "separated layers" idea, and
**prove precisely where it fails** — pinning `CarryRefinementCrossing` (§3/entry 238) at `n = 6`.  *This is a no-go, not
a way through.*

* **The CRT factorization (PROVED).**  `mod6_fires_iff_mod2_and_mod3`: `MOD₆` fires iff both `MOD₂` and `MOD₃` fire
  (`6 ∣ #trues ↔ 2 ∣ #trues ∧ 3 ∣ #trues`, coprimality of 2,3, entries 245/270).  So `MOD₆` genuinely separates into a
  `MOD₂` and a `MOD₃` layer.
* **What works field-by-field.**  Each factor is native over its own field (entry 270 — `MOD₂` degree 1 over `F₂`,
  `MOD₃` degree 2 over `F₃`); the Fermat representation works precisely in characteristic equal to the modulus.
* **Where it fails (PROVED no-go).**  `mod6_layers_cross_fields`: no field has `CharP F 2 ∧ CharP F 3` (`no_common_char`,
  entry 243), so the two CRT factors demand *incompatible* characteristics.  The prime route (§5q–§5u) commits to one
  characteristic; it cannot run on the combined `MOD₆` gate.  **This is the carry-crossing obstruction in its smallest
  instance** — the polynomial method picks one field, and composite modulus lives over several.

**Net:** the natural way to extend the prime Smolensky route to composite modulus — separate the CRT layers — *provably
fails by field incompatibility*.  This is exactly why composite `ACC⁰` is the genuine wall: it needs a method *not
committed to a single characteristic*.  A proved negative structural fact (the `CarryRefinementCrossing` shape at
`n = 6`), not a circumvention.  Not faked, not a separation.

## 6. Honest conclusion

The arc is a complete, machine-checked, conservative **anatomy**: Williams' route reconstructed and decomposed; the
composite-`ACC⁰` wall driven to one precise, classical open object; every reducible part proved or refuted; nothing
faked.  As a proof-search engine, the N-Frame framing earned its keep — it repeatedly told us *which* boundaries
collapse (size, decode, layer degree, counting budget), *which* refine (the carry seam into Kummer/CRT structure), and
*which* is genuinely irreducible (cross-field mixing).

The result is not a separation.  It is a faithful localization of where any new proof of this separation must enter,
machine-checked end to end.
