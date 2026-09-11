# Scope — the God-Move / Cook–Levin proof obligation, made precise

**Goal (per the plan): state the two load-bearing frontier hypotheses exactly, decompose them into local
lemmas, and prove the logical skeleton — so the proof obligation is fully visible.  The skeleton is
formalized in `ComputationalDepthGodMoveObligation.lean` (sorry-free, axiom-clean).**

---

## The two routes, and the honest status of each

The historical scope organized the attempted proof around these interfaces:

* **Route F — `CookLevinFrontierHyp`** (P-side rank frontier): every bounded Cook–Levin compilation has the
  within-profile / SPDP rank upper bound.  Already isolated as a `Prop`; `peqnp_false_of_frontier` is
  kernel-clean conditional on it.
* **Route G — `GlobalGodMoveHyp`** (God-Move extraction): a rank-monotone, witness-free, instance-uniform
  gauge `T_Φ` with `T_Φ(P_solver Φ) = Q_Φ` and `rank(T_Φ p) ≤ rank p`.  Now demoted from a custom axiom to
  explicit `Prop` hypotheses (`SCOPE_PVSNP1_AUDIT.md`, "RESOLVED").

## What the skeleton theorem settles about Route G

`ComputationalDepthGodMoveObligation.lean` formalizes the God-Move gauge precisely
(`GodMoveGaugeExists R p₀ B k` = `∃ T, RankMonotone R T ∧ R(T p₀) ≤ B ∧ k ≤ R(T p₀)`) and proves:

* **`not_godMoveGaugeExists_of_gap`** — *the central danger, as a theorem*: when `B < k` (`B = n²⁰⁰`,
  `k = C(n/3, log n)`, gap holds at `n = 2⁸⁰⁴`), **no such gauge exists**.  It is the rank sandwich
  `k ≤ R(T p₀) ≤ B < k` — `godMove_rank_monotone` + the projected P-side bound, confronted with the
  axiom-free NP-side minor.
* **`globalGodMoveHyp_iff_no_hard`** — **`GlobalGodMoveHyp ↔ ¬∃ hard instance`**, given the per-instance gap.

**Logical scope, corrected 2026-09-10.** The equivalence does **not** rule out the God-Move as a proof
strategy. Under a hypothetical polynomial-time SAT decider, deriving a source, a valid extraction, and
incompatible rank bounds would be a legitimate proof by contradiction. The equivalence shows that the
abstract existence hypothesis already carries the missing conclusion; merely assuming it does not prove
separation. It does not show that its component properties cannot be derived from the hypothetical decider.

This file's skeleton is an abstract rank sandwich. It does not itself construct a computation encoding,
prove witness independence or instance uniformity, or identify the semantic hard target. Those obligations
must be discharged by the concrete construction rather than inferred from the skeleton's name.

## Decomposition of the two load-bearing lemmas (the local targets)

These describe obligations for the intended faithful construction. Existing abstract or special-case
lemmas must not be mistaken for a proof that all of them hold together for that construction.

### Route G local lemmas (the gauge)
1. `godMove_gauge_exists` — the amplituhedron/global gauge exists for the instance.
2. `godMove_projection_multilinear` — the projection preserves multilinearity.
3. `godMove_admin_collapse` — administrative (tableau-bookkeeping) variables collapse correctly.
4. `godMove_clause_sheet_survives` — the clause-sheet `Q_Φ` survives the projection.
5. `godMove_correct` — the extracted object equals `Q_Φ`: `T_Φ(P_solver Φ) = Q_Φ`.
6. `godMove_rows_into_subspace` — SPDP rows map into subrows/subspaces.
7. `godMove_rank_monotone` — `rank(T_Φ p) ≤ rank p` (profile rank cannot increase).
8. `godMove_witness_free` — `T_Φ` depends only on `Φ`, not on a satisfying assignment.

The complete upper/lower rank sandwich is contradictory when `B < k`
(`not_godMoveGaugeExists_of_gap`). That is the intended endpoint if every component is derived under a
hypothetical faithful polynomial-time SAT decider. The contradiction is not a reason to abandon the
component proof program. It is a reason to keep its hypotheses explicit and to ensure that all bounds
concern the same source, extracted target, partition, and SPDP parameters.

### Route F local lemmas (the P-side frontier — `CookLevinFrontierHyp`)
1. profile classification (finitely many local profiles);
2. within-profile finrank bound;
3. bounded number of profiles;
4. Cook–Levin locality;
5. profile-span compression;
6. final SPDP rank bound `≤ n²⁰⁰`.

These local claims need to be checked against a specific compiler. Subsequent work has refuted the desired
polynomial bound for the existing raw product-form `compiledPoly`; its large rank occurs even without SAT
correctness. Thus that exact raw-source frontier is not an open lemma to fill in. See
[GodMoveGapRepairs.md](research-audits/nframe-fixed-invariant/GodMoveGapRepairs.md).

The paper's primary Global God-Move route instead needs a faithful instrumented source with a
runtime-derived upper bound and a valid extraction to the designated hard coupled sheet. The separate
paired interfaces are `GlobalGodMoveGauge.Theorem207PaperSourcePSideUpperBound` and
`GlobalGodMoveGauge.Theorem207PaperSourceToTargetRankBridge`, on the same constructed objects. Their
arithmetic closure is proved. The new extraction below supplies the latter for a specified normalized
operational SAT source; the former remains unproved, so their joint construction is not complete.

## Tiny-instance test (item 3)

`tiny_no_gauge` (in the Lean file) is the minimal computational sanity: with `R = id`, `B = 3 < k = 5`, no
gauge keeps `R(T p₀) ≤ 3` while `5 ≤ R(T p₀)`.  This is the rank sandwich at the smallest scale — it shows
the obstruction is not an artifact of `n = 2⁸⁰⁴` but holds whenever `B < k`.

A fuller tiny test (next concrete step, honest sandbox): build a tiny SAT instance → tiny Cook–Levin
tableau → compiled polynomial → a candidate projection `T` → compute the SPDP/partial-derivative rank
before and after via `native_decide`.  Two things to look for: (a) does the candidate `T` actually satisfy
`rank(T p) ≤ rank p` (most projections do *not* — rank monotonicity is special); (b) can any `T` both
collapse the P-side rank and keep the minor — which the skeleton theorem says is impossible once `B < k`.

## Current continuation target

Continue with the God-Move compiler/collapse/extraction chain described in
[GodMovePaperAlignment.md](research-audits/nframe-fixed-invariant/GodMovePaperAlignment.md). Sample and
wire-basis discovery does not by itself supply this SPDP transport. A correct conditional construction
must preserve the hard minor while obtaining the source bound from legal computation.

The historical `PaperFaithfulSeparation.DecidesSAT` also needs care: the existing audit proves an
always-accept machine satisfies that positive-only, encoding-free predicate. The actual separation target
is `SeparationTarget.SAT_not_in_P`, with the faithful formula codec and correctness on every input.
Neither an abstract God-Move hypothesis nor a contradiction involving that legacy predicate is a proof
of this target.

The [runtime and designated-sheet audit](research-audits/nframe-fixed-invariant/GodMoveRuntimeAndSheetAudit.md)
now proves two specific limitations of the normalized machine-output route. A fixed linear-time
`ComposableMachine` has superpolynomial normalized SPDP rank under discrete blocks, so the general
runtime-only bound is false. The actual strict first-of-block target normalizes to one and cannot equal
a multilinear verifier characteristic at paper scale. These do not refute every God-Move source/map or
a theorem that additionally uses faithful SAT correctness, but the current characteristic equality and
generic runtime bound cannot supply the required combination.

The subsequent [designated-sheet extraction](research-audits/nframe-fixed-invariant/GodMoveDesignatedProjection.md)
recovers the nonmultilinear sheet explicitly, without normalizing it. A quadratic substitution after
the unit-query face gives exact equality with the actual production target; a row-space argument
proves same-parameter rank transport. Its extension to separate source/output coordinates is an
idempotent linear projection and retains the designated lower bound at the paper's log/log window.
`GodMoveSATDesignatedExtraction.operationalPaperSource_rank_bridge` supplies the named rank bridge.
The rank comparison applies to this source; it is not a global rank-monotonicity theorem.

This does not prove a SAT-specific polynomial runtime bound for the normalized source. Correctness
fixes that source as the canonical SAT language characteristic, independently of the implementation
or clock, and a binomial minor already occurs on easy unit-query faces. The separate canonicity audit
proves that this rank is superpolynomial even in the actual encoded input length. Deriving an upper
bound from a hypothetical polynomial SAT clock remains the missing mathematical argument, not a
consequence of the compact extraction formula or the dimension of its unrestricted output range.

The [SAT runtime-bound audit](research-audits/nframe-fixed-invariant/GodMoveSATRuntimeBoundAudit.md)
now proves the direct upper bound for every source polynomial by spanning its actual shifted rows:
`rank ≤ choose(L,k) * sum_{j ≤ min(k,ell)} choose(k,j) ≤ (2L)^k`. On the specified normalized SAT
source this yields a quasipolynomial upper bound, matched by the existing lower bound at the exact
paper log/log window. It does not yield a fixed polynomial exponent.

`GodMoveSATRuntimeFrontier.satPolynomialClockRankBound_iff_separation` proves that the requested
runtime-rank estimate, restricted to hypothetical polynomial-clock SAT deciders, is equivalent to
the faithful separation target. The forward proof substitutes the polynomial clock into the
runtime budget and invokes the encoded-length rank lower bound; the reverse is vacuous when no
such decider exists. This validates the contradiction strategy but supplies no independent proof
of its missing estimate. An estimate for all SAT deciders, including superpolynomial clocks, would
be a stronger assertion and is not established by this equivalence.

The subsequent [expander and positive-boundary construction](research-audits/nframe-fixed-invariant/GodMoveExpanderPositiveProjection.md)
derives erased-edge label protection from actual graph expansion and maps
the unit-source and designated-sheet derivative minors through a positive
Vandermonde external matrix. An explicit decoder recovers their coordinates.
The boundary dimension must be at least the retained minor dimension; the
rank-one positive-cone construction does not provide polynomial compression.
It supplies no SAT runtime-rank upper bound and leaves separation unproved.

The [executable production connection](research-audits/nframe-fixed-invariant/GodMoveExecutableNFrameConnection.md)
subsequently constructs the designated-row projector in the unchanged
`ObserverGauge` type, derives its exact rank and action, and proves a
minimum over gauges explicitly required to fix those rows. This additional
domain predicate is not substituted for production admissibility. Actual
machine transitions bound the action when that machine materializes the
boundary coordinates, under an explicit serialization contract. Neither
row-preservation by the runtime-bounded wire gauge nor necessary boundary
materialization by every SAT decider is proved. The concrete small-circuit
counterexample confirms that output preservation and exact extraction alone
do not imply preservation of the designated derivative family.

The [compact projector construction](research-audits/nframe-fixed-invariant/GodMoveImplicitGaugeConstruction.md)
now gives executable syntax for the exact production projection's coefficient
kernel, including small input factors and shared recurrence references.
Its node count is `2+3m(k+1)+11m`, and contraction recovers the unchanged
projection on all polynomial inputs. This removes subset enumeration from
descriptor construction. It does not make expanded polynomial evaluation or
coefficient contraction polynomial-time. The actual rank and unit-weight
production action remain superpolynomial in descriptor size. The supplied
boundary-runtime barrier has also been connected to actual machine output
with polynomial encoded lengths. It constrains dense serialization, not
arbitrary SAT deciders. The SAT-specific runtime-controlled connection and
faithful separation target remain unproved.

The [circuit gluing/application continuation](research-audits/nframe-fixed-invariant/GodMoveCircuitGluingAndApplication.md)
proves executable shared-wire composition, exact trace preservation, and
response factorization through actual computed Boolean ports. Its rank
bound is `2^r` for `r` ports; a verified `4r+1`-gate equality circuit attains
that exponential response rank. This response matrix is not substituted
for the production N-Frame invariant. For that unchanged invariant, the
continuation gives compact projector application on separated affine
products and the actual designated quadratic sheet. General application
to the SAT source, a runtime-controlled source upper bound, and separation
remain unproved.
