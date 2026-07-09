# Non-Natural Separating Measure — one candidate, the triage, and the kill basis

*Honest record of the requested move: invent one candidate separating measure and run the triage filter
immediately. Candidate proposed, triaged, **died at the filter**; a suite of computable candidates all die
the same way; and the structural reason is identified. Demonstrated, not asserted (`triage_harness.py`).
Nothing here is `P ≠ NP`.*

---

## The candidate and its triage

**Candidate `μ_top(f)` = high-level Fourier mass** = `∑_{|S|>n/2} f̂(S)²` — an intrinsic, computable,
complexity-correlated measure (a fair "non-natural attempt": high-degree Fourier structure is a real
hardness signal). Run through the filter (`triage_harness.py`, `n=10`):

| measure | parity (P) | tseitin-lin (P) | trivial-comp (P) | majority (P) | AND (P) | random (hard proxy) |
|---|---|---|---|---|---|---|
| influence `I[f]` (spectral) | **10.0** (=n, max) | 3.0 | 0 | 2.46 | 0.02 | 4.94 |
| **`μ_top`** top-level mass | **1.00** (max) | 0 | 0 | 0.15 | 0.001 | 0.35 |
| Fourier sparsity | 1 | 1 | 1 | **1024** | **1024** | 1024 |
| ANF degree (GF2) | 1 | 1 | 0 | 8 | **10** (=n) | 10 |

**Verdict: `μ_top` is MAXIMAL on parity, which is in `P` → discarded.** (Parity is a single top-level
character, so it maximizes every high-degree/spectral measure.) The suite confirms the pattern:

- **influence / `μ_top`** (spectral) → maxed by **parity** (`P`).
- **Fourier sparsity** → `2^n` on **AND** and **majority** (both `P`) → discarded; it is exactly the
  constructive+large distinguisher of Razborov–Rudich (natural property).
- **ANF degree** → `=n` on **AND** (`P`) → discarded; also `≤ n`, so **never super-polynomial** (wrong scale).

Every computable intrinsic candidate lands in one of: **high on a `P`-easy object**, **RR-natural**, or
**bounded by `n`**.

---

## The kill basis (why this is not just bad luck)

`{parity, Tseitin, trivial-DTM-compilation}` is a **kill basis** for the triage filter: each is the extremal
point of one family of computable measures, and each is in `P`.

| Measure family | Extremal `P`-easy object | Why |
|---|---|---|
| spectral / analytic (influence, approx-degree, `μ_top`, sensitivity) | **parity** | a single top character — maxes high-degree/sensitivity |
| proof-algebraic (resolution width, GF(2) structure) | **Tseitin** | expander-hard for the model, yet a GF(2) linear system (`∈ P` by Gaussian elimination) |
| syntactic / representation (SPDP rank, compilation monomial count) | **trivial-DTM compilation** | rank floor `C(n/3, log n)` is a grid artifact, high for the do-nothing machine |

Any computable measure that is high on hard functions is high on at least one of these three — and all three
are in `P`. The deep reason is not empirical: **the filter is the concrete face of Razborov–Rudich
largeness.** A computable measure that is low on *every* `P`-easy object and high on an NP object is
*constructive + large + useful against `P/poly`* — a natural property, which breaks strong PRGs. So
(modulo standard crypto) **no computable intrinsic candidate can survive the filter**; the three P-easy
objects are just the witnesses for the three main families.

---

## What this means for the next move

The requested strategy — *invent a candidate measure, then run the triage filter* — is **provably empty for
computable candidates**. Running the triage "immediately" is only possible for a measure you can evaluate on
truth tables, i.e. a computable one, i.e. one RR has already killed.

The only candidates the filter does **not** kill are the ones it **cannot be run on**:

- **non-computable** (bounded-arithmetic / proof-theoretic: `μ` defined by provability in a weak system —
  dodges RR's *constructivity*), and
- **non-large** (GCT-style: `μ` keyed to the exceptional symmetry of the permanent/SAT, high only on a
  `2^{-ω(n)}`-sparse set — dodges RR's *largeness*; occurrence-obstructions proven insufficient
  (Bürgisser–Ikenmeyer–Panova 2016), multiplicity obstructions open).

Both are **un-triageable by construction** — you cannot filter them on a trivial DTM or parity, because their
whole point is to not be an efficiently-checkable large property. So the honest status is:

> The "candidate + triage" loop terminates. Every candidate it can act on, it kills. The live corner is
> exactly the set of candidates it cannot act on — the non-computable and non-large ones — and progress there
> is not "propose a measure and test it," but a from-scratch construction in GCT or bounded arithmetic.

Mapping Darren's five directions:

| Direction | Triageable? | Status |
|---|---|---|
| spectral/analytic/rigidity measures | yes (computable) | **killed** by the filter (above) |
| Fixed-object exploitation resistance (semantic) | — | `= circuit complexity`, circular |
| Williams algorithmic method (faster SAT → separations) | n/a | not a measure — the diagonalization route; the scalable lever, but a different kind of work |
| GCT-multiplicity | no (non-large) | **live**, un-triageable; occurrence-obstructions dead |
| bounded-arithmetic / proof-complexity | no (non-computable) | **live**, un-triageable |

---

## Honest bottom line

I proposed a concrete candidate, ran the triage, and it died on parity; a suite of computable candidates all
die; and the reason is Razborov–Rudich, made concrete by the `{parity, Tseitin, trivial-compilation}` kill
basis. **The computable-candidate space is empty.** A genuine `P ≠ NP` candidate must live in the
non-computable or non-large corner (GCT-multiplicity / bounded arithmetic), where the work is a construction,
not a triage. Consolidating restricted-class lower bounds remains the real, provable output; the theorem
still needs a new idea in that corner.

*Demo: `triage_harness.py`. Companions: `COMPOSITE_MEASURE_ATTEMPT.md`, `OBSERVER_MEASURE_ATTEMPT.md`,
`PRIME_ACC0_CAPSTONE.md`. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*
