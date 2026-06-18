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

## 6. Honest conclusion

The arc is a complete, machine-checked, conservative **anatomy**: Williams' route reconstructed and decomposed; the
composite-`ACC⁰` wall driven to one precise, classical open object; every reducible part proved or refuted; nothing
faked.  As a proof-search engine, the N-Frame framing earned its keep — it repeatedly told us *which* boundaries
collapse (size, decode, layer degree, counting budget), *which* refine (the carry seam into Kummer/CRT structure), and
*which* is genuinely irreducible (cross-field mixing).

The result is not a separation.  It is a faithful localization of where any new proof of this separation must enter,
machine-checked end to end.
