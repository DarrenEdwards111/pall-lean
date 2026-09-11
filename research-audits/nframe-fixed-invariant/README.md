## 2026-09-11: constructed projection preservation test

[Finite derivative obstruction](GodMoveConstructedDerivativeObstruction.md):
the actual constructed wire projection cannot preserve every second-derivative
direction of the 13-gate six-input conjunction (at least 15 directions).
This specializes the existing generic obstruction to the new numeric builder;
it does not refute a SAT-specific theorem or establish separation.

# Fixed N-Frame invariant: concrete implementation check

The latest [constructed wire projection](GodMoveConstructedProjection.md)
computes the inverse weights for the actual SAT-machine discovery's sample
matrix and derives the full existing wire certificate. Its cached numeric
weight builder uses at most `8r³` rational arithmetic operations, with
polynomial bit length for the final weights. The complete construction
bit-runtime bound and SAT-specific derivative-rank bound remain unproved;
this does not establish separation.

The preceding [actual-runtime snapshot connection](GodMoveRuntimeSnapshotConnection.md)
proves a quadratic production N-Frame rank bound for the span of actual
tape, head, and control coordinate functions. For a correct SAT decider,
this gauge fixes the exact SAT decision polynomial. The required derivative
space need not lie in that span: a concrete four-state scanner has snapshot dimension at most
1,296 and fourth-derivative rank at least 1,820. A SAT-specific argument
controlling the hard derivative rows and separation remain unproved.

The preceding [circuit gluing and projector application](GodMoveCircuitGluingAndApplication.md)
proves exact shared-wire composition and its joint-state factorization.
It also applies the unchanged production projector in compact form to
separated affine factors and the designated quadratic sheet. The interface
rank bound is exponential in the number of Boolean ports, and a linear-size
equality circuit attains it. These results do not prove the SAT-specific
runtime-controlled N-Frame bound or separation.

The preceding [compact projector construction](GodMoveImplicitGaugeConstruction.md)
gives executable arithmetic syntax for the exact production row-projector
kernel, with `2+3m(k+1)+11m` nodes and proved contraction semantics.
Its rank remains superpolynomial in that descriptor size. The incorporated
runtime barrier now follows from actual machine steps for dense output,
including polynomially related encoded input lengths. Efficient contraction,
the SAT-specific runtime-controlled connection, and separation remain unproved.

The preceding [executable production N-Frame connection](GodMoveExecutableNFrameConnection.md)
constructs a concrete gauge with proved rank and action, establishes its
minimum under explicit derivative-row preservation constraints, and bounds
that action by runtime for machines materializing the boundary. Direct
binary coding also removes full-screen enumeration from individual entries.
The required preservation/efficiency theorem for every SAT decider and
separation remain unproved.

The preceding [expander and positive-boundary construction](GodMoveExpanderPositiveProjection.md)
protects the actual SAT and designated-sheet derivative minors against
bounded edge erasure, then encodes them with a positive Vandermonde matrix
and an exact decoder. It includes an adjacency-based Ramanujan calibration.
Preserving the full minor requires its binomial boundary dimension; the
construction does not supply a polynomial runtime-rank bound or separation.

The preceding [SAT runtime-bound audit](GodMoveSATRuntimeBoundAudit.md) proves
an upper bound by explicitly counting shifted-derivative rows. At the exact
paper log/log window, the normalized SAT source has rank between
`n^(log₂ n / 4)` and `n^(3 log₂ n)` for `n ≥ 2²⁰`. This is a quasipolynomial
growth estimate, not a polynomial runtime bound. The still-unproved estimate
restricted to polynomial-clock SAT deciders is shown to be equivalent to
the faithful `SAT_not_in_P` target. Separation remains unproved.

The preceding [designated-sheet extraction](GodMoveDesignatedProjection.md)
recovers the actual nonmultilinear production sheet from the normalized
SAT-machine source by an explicit witness-free map. Its idempotent extension
preserves the sheet's identity-minor lower bound and does not increase SPDP
rank on that source at the same log/log parameters. This fills the named
source-to-target rank bridge for the specified source. The SAT-specific
runtime-derived source upper bound and separation remain unproved.

For the preceding checks of the runtime bound and designated target, see
[GodMoveRuntimeAndSheetAudit.md](GodMoveRuntimeAndSheetAudit.md). A fixed
linear-time machine disproves the generic normalized-rank runtime bound;
the actual designated sheet normalizes to one and cannot equal a multilinear
characteristic. An explicit binomial minor is also transported into the actual
normalized SAT-machine source. These results do not establish separation.

For the earlier Global God-Move face extraction, see
[GodMoveFaceExtraction.md](GodMoveFaceExtraction.md). It derives a concrete
rank-monotone extraction from the normalized actual machine polynomial to the
verifier characteristic, and proves a necessary rank/degree cost for every
local accumulator certificate. The new extraction above extends that face
construction to the actual designated coupled sheet; a runtime-derived
source-rank bound remains unproved.

For whether the machine-dependent revision resolves the selector-to-SAT
objection, see [GodMoveDiscoveryRevisionAudit.md](GodMoveDiscoveryRevisionAudit.md).
It validates the conditional strategy while retaining the independent lower
bound as an unproved requirement for separation.

For the latest construction using an actual supplied SAT machine, with exact
sample/basis correctness and derived adaptive coefficient and query-size
bounds, see [GodMoveMachineDiscovery.md](GodMoveMachineDiscovery.md).
The complete construction runtime and superpolynomial SAT lower bound remain
unproved. Earlier reports below retain their historical verification results.

For adaptive discovery with an explicit predicate-existence oracle and the
separate scalar-query lower bound, see
[GodMoveAdaptiveDiscovery.md](GodMoveAdaptiveDiscovery.md). Oracle-call
counts do not establish polynomial runtime, and the restricted query lower
bound does not establish SAT hardness.

For executable exhaustive sample selection, exact basis-wire discovery, and
the bound on successful sample refinements, see
[GodMoveExecutableDiscovery.md](GodMoveExecutableDiscovery.md). Discovery
still scans all Boolean assignments; no efficient discovery or superpolynomial
SAT lower bound is claimed.

For the explicit sampled projection, executable wire-based evaluator, and
SAT reductions for finding the required data, see
[GodMoveGaugeConstruction.md](GodMoveGaugeConstruction.md).

For the latest production gauge bridge, linear SAT lower bound, and obstruction
for every unrestricted minimizer, see
[GodMoveProductionConnection.md](GodMoveProductionConnection.md). The required
superpolynomial SAT lower bound remains unproved.

For the subsequent desktop-paper God-Move work, see
[GodMoveGapRepairs.md](GodMoveGapRepairs.md). That report separates constructive
product/common-span repairs from the unresolved separation obligations.

2026-09-09. The user requires keeping the N-Frame invariant, not replacing it with surrogate entropies or cut sums.

This check imports FullLagrangianFixed unchanged. With alpha>=0 and beta=gamma=1, the action is alpha times edge energy + r + 1/(1+r). For every r>=0, r+1/(1+r)>=1. The repository's trivialObserverGauge has zero coordinates and zero projection rank, so its action is exactly 1. Hence it is a global minimizer over ObserverGauge N for these allowed positive rank/barrier coefficients.

This contradicts the unconditional explanatory claim in LogDetBarrier.lean that its structural penalty prevents the zero gauge from minimizing the action. It does not refute a genuine logarithmic-determinant barrier on a positive-definite domain, nor an additional admissibility condition that excludes the zero gauge. Those are not supplied by this concrete action/type.

The actual barrier definition is 1/(1+rank), bounded even at zero rank. No production definition is changed by this audit. No substitute invariant is introduced.

DynamicNFrameLagrangianInvariant still takes stateActionRank as a field; StrictDynamicNFrameLagrangianInvariant takes configActionRank. CanonicalDynamicNFrameInvariant instead inserts a binomial scale by SAT semantics and ignores time in its liveBoundaryRank. These interfaces do not construct a machine-selected minimizer of this action.

The next genuine implementation obligation is an admissible gauge domain and machine-to-gauge evolution justified by the intended geometry. Simply deleting the zero gauge or assigning a hard rank would not establish the desired runtime theorem. This check does not construct that evolution or prove SAT hardness.

Reproduce the focused check with:

    /home/darre/.elan/bin/lake env lean research-audits/nframe-fixed-invariant/ZeroGaugeMinimum.lean
