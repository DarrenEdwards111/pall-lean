# SCOPE: The observer-boundary thread — map, verdict, and where the wall is

This document closes the observer-boundary investigation on branch `razborov-recoverRho-wip`. It is a **map of
the obstruction**, not a separation. **Verdict: useful — it exposed false routes, produced valid *restricted*
lower bounds, and pinned the exact missing quantifier — but it does not prove `P ≠ NP` and does not get around
the central barrier.** Everything below is machine-checked with `#print axioms ⊆ {propext, Classical.choice,
Quot.sound}` and no `sorry`.

## 1. What it genuinely achieved

**False routes exposed (machine-checked no-gos).**
* Final-bit / decision-only observers collapse to zero innovation (`ChargedLengthObserverCollapse.universal_observer_lower_impossible`).
* The dynamic query-innovation measure also collapses: a time-invariant scheme — even a rich, input-separating one — has zero innovation (`ChargedDynamicQueryCollapse.universal_dynamic_lower_impossible`, `richScheme_dynamic_zero`).
* The maximally-rich *canonical* scheme has innovation *exactly the clock* — padding-sensitive, not a language invariant (`ChargedCanonicalQueryAudit.canonical_schemeResource_eq_clock`, `ChargedDynamicSPDPCapstone.charged_dynamic_padding_sensitive`).
* The unrestricted minimum over decompositions collapses via the empty/singleton cut, in *both* the log observer (`BlockDecompositionMinGap.hardF_decomposition_gap`, cut `≤ 2`) and the dimension observer (`DimensionUpperBound.unrestricted_min_trivial`, empty cut `≤ 1`).

**Valid restricted lower bounds.**
* Log-scale (Nečiporuk residual counts): every address block of `hardF` forces boundary `≥ 2^b − 1`
  (`BlockDecompositionMin.hardF_minBlockBoundary_ge`), robust to unions of blocks
  (`BlockDecompositionMinUnion`), a bounded number of data cells (`BlockDecompositionMinBoundedData`,
  `≥ 2^b − 1 − |D|`), and dropping address bits (`BlockDecompositionMinPartial`, `≥ 2^{b−d} − 1`).
* Dimension-scale (residual-span rank): the equality function has full rank `2^k` on a structured block
  (`DimensionFullRank.eqFun_dim_ge`), with the matching upper bound `≤ 2^{|S|}` (`DimensionUpperBound`).
* Communication / proof-space: fooling reproduces `log₂ n` (rectangle cover) and `c·t` (Tseitin proof-space) via
  the same non-mergeability principle.

**The exact missing quantifier.** Every one of these lower bounds is over *one* observer, query scheme, cut, or
representation. The bound `P ≠ NP` needs would have to hold over **every real polynomial-time SAT decider**. That
gap is the whole content of the frontier (§3).

**A reusable toolkit + a taxonomy.** See §2.

## 2. The taxonomy (three observer classes, two calculi)

| class | boundary | fooling base bound | propagation calculus |
|---|---|---|---|
| **1. Restriction** (residual counts — formulas, communication matrices) | `log₂ (#residuals over a variable subset)` | `log₂ K ≤ boundary` | halve/square (`RestrictionObserver`, `functionResidualObserver`) |
| **2. Witness-indexed fooling** (proof-space, rectangle cover) | `log₂ (#objects of a witness)`, `sInf` over witnesses | `log₂ K ≤ boundary` | none (min over witnesses) |
| **3. Dimension / rank** (AC⁰[p] degree) | `finrank (feature subspace)` | `K ≤ dim` (linear) | linear halve/square (`dimResidualObserver`) |

* **1 ∩ 3** is occupied by the residual-span *dimension* (`DimensionRestrictionObserver`): it is simultaneously a
  `DimObserver` (class 3) and a restriction observer (class 1, linear form).
* The **general min over all decompositions** is `CookLevinFrontierHyp`. Its **class-3 (linear/rank) shadow is
  Valiant matrix rigidity** — the exact wall the N-Frame linear-mixer analysis already terminated on.

## 3. The frontier, stated precisely

The observer interface (`ComputationalDepthPvsNPSeparatingInvariant`) already proves the reduction:

> `no_InP_of_invariant : PUpper R ∧ SATLower R L → ¬ InP L`, and with `L ∈ NP`, `PneqNP_of_invariant`.

In decomposition language, a proof of `SAT ∉ P` would need **all** of:

1. **(Done, restricted.)** SAT (or a hard family) has high boundary on every decomposition *in a structured
   class* — the restricted rungs of §1.
2. **(The decisive open step — machine-completeness bridge.)** *Every* polynomial-time SAT machine induces an
   admissible structured decomposition, and cannot evade the hard cuts through encoding, padding, state
   representation, or a different decomposition. Formally this is the `PUpper`/coverage direction made uniform
   over *all* machines — nothing in this thread supplies it, and the collapse no-gos (§1) show why every
   *specific* observer/cut/scheme fails to.
3. **(Open.)** The corresponding SAT lower bound, uniform over that machine-complete class.

Steps 2–3 are, essentially, the unsolved `P`-vs-`NP` breakthrough. The observer machinery makes them **precise**;
it does not make them **easier**.

## 4. Recommendation (honest)

* **Close and document this thread; stop adding calibrations.** Further observer-calculus building provably routes
  to the same frontier (every calibration checked — AC⁰[p] degree, Nečiporuk formula, communication rectangle,
  proof-space — reduces to the fooling base bound + the machine-completeness gap).
* The productive continuations are:
  1. **Attack the machine-completeness bridge directly** — and expect it to fail at a known barrier
     (relativization / natural-proofs / algebrization; the rank shadow is Valiant rigidity).
  2. **A genuinely different invariant that is representation- and padding-invariant *by definition*** — not
     patched to be, but intrinsically so. Nothing in this thread was.
  3. **New *restricted*-model lower bounds** (bounded-depth circuits, formulas, branching programs, restricted
     proof systems) — presented as what they are, never as `P ≠ NP`.

## 5. Bottom line

Useful? Yes — it mapped and formalized the obstruction extremely well, and it stops us from mistaking a restricted
lower bound for `P ≠ NP`. Breakthrough? No. The wall is the machine-completeness bridge, and it is the same wall
the whole program keeps reaching. Nothing in this thread is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
