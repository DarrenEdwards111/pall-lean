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

## 6. Honest conclusion

The arc is a complete, machine-checked, conservative **anatomy**: Williams' route reconstructed and decomposed; the
composite-`ACC⁰` wall driven to one precise, classical open object; every reducible part proved or refuted; nothing
faked.  As a proof-search engine, the N-Frame framing earned its keep — it repeatedly told us *which* boundaries
collapse (size, decode, layer degree, counting budget), *which* refine (the carry seam into Kummer/CRT structure), and
*which* is genuinely irreducible (cross-field mixing).

The result is not a separation.  It is a faithful localization of where any new proof of this separation must enter,
machine-checked end to end.
