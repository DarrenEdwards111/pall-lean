# God-Move alignment with the desktop paper

The source is `/mnt/c/Users/darre/Desktop/p vs np1.pdf` (280 pages).
It is byte-for-byte identical to `/home/darre/pall-lean/p-vs-np1.pdf`:
SHA256 `c39b7045d58b6ae2cdcd1ae654ccb1314f2adecb2a0934eafe7ec03713a26240`.
Page numbers below are the PDF's printed page numbers.

## Correct proof target

The continuation remains the Global God-Move compiler/collapse/extraction
chain. Recent sample and wire-basis discovery results do not establish the
required SPDP transport. The [scope note](../../SCOPE_GODMOVE_OBLIGATION.md)
has been corrected: a rank contradiction derived under a hypothetical
faithful polynomial-time SAT decider would be a valid proof strategy, not
a reason that the strategy is impossible.

Section 2.2, pp.13–14, explicitly designates the Global God-Move as the
primary separation route. The local log-det rate audit does not settle this
route. Theorem 207, pp.198–199, needs all of the following on the same objects
and at matched SPDP parameters:

1. The uniform compiler, including the instrumented verifier sheet, gives
   a source polynomial with polynomial rank (Theorem 203 and Lemma 204).
2. The witness-free God-Move extraction recovers the designated coupled
   sheet without increasing rank (Definition 6/Lemma 7 and Lemma 205).
3. That very extracted sheet has the superpolynomial identity-minor lower
   bound (the NP-side result, restated as Theorem 217).

The final numerical contradiction follows if these inputs hold. The remaining
work is establishing them together for the intended computation encoding.

The subsequent [Boolean-face extraction](GodMoveFaceExtraction.md) proves
an actual source-specific restriction and unchanged-parameter SPDP transport
for the normalized machine output and its verifier characteristic. It does
not supply the instrumented source's polynomial rank bound or identify this
characteristic with the designated hard coupled sheet. The same work proves
that every accumulator certificate of the local initial/step form contains
the target's rank in its initial-equation multiplier; the generators' small
degree alone cannot bound that certificate cost.

The next [runtime and designated-sheet audit](GodMoveRuntimeAndSheetAudit.md)
proves that the actual strict `TΦ` target normalizes to one, losing its
same-window identity-minor rank. It cannot equal the multilinear verifier
characteristic. The same audit constructs a fixed machine with a proved
linear clock and superpolynomial normalized rank, refuting a general
runtime-only collapse for that invariant. This does not refute a bound
conditioned additionally on faithful SAT correctness or every alternative
God-Move source/map.

The latest [designated-sheet extraction](GodMoveDesignatedProjection.md)
now supplies an explicit map from the normalized operational SAT source to
the actual nonmultilinear target. It substitutes `X_i -> 1-X_i+X_i^2` into
the extracted unit monomial. A proved row-space containment gives the
same-parameter rank inequality, and a separate-coordinate extension gives
an idempotent linear projection. The existing designated identity-minor
bound survives. This supplies the named source-to-target bridge for that
source, while its SAT-runtime-derived upper bound remains unproved.

The subsequent [SAT runtime-bound audit](GodMoveSATRuntimeBoundAudit.md)
proves the direct finite-row upper bound and matches it with the actual
source minor at the paper's exact log/log window. The resulting source
growth is quasipolynomial. A bound polynomial in encoded length plus
runtime, if proved for polynomial-clock SAT deciders, would contradict
that lower bound with all constants and exponents accounted for. That
restricted estimate is equivalent to `SAT_not_in_P`; the equivalence does
not prove either statement. A machine-dependent polynomial exponent also
does not automatically supply the specific `n^200` bound without further
scaling. The arbitrary-power lower bound handles the general conditional
contradiction directly.

The [expander and positive-boundary continuation](GodMoveExpanderPositiveProjection.md)
now protects actual minor labels against erased edge coordinates and maps
the SAT and designated-sheet derivative rows to a proved positive external
matrix with exact decoding. Expansion supplies label preservation; the
coefficient identities supply row transport. Preserving all these rows
requires their full binomial boundary dimension. This adds concrete geometry
to the extraction side without deriving the missing runtime upper bound.

The [executable production connection](GodMoveExecutableNFrameConnection.md)
now realizes those rows by an explicit production `ObserverGauge`, with
derived rank and exact action. It proves a minimum subject to row-fixing
constraints and a runtime/action bound under an actual boundary-output
contract. Direct code execution computes individual positive entries. The
computed-wire gauge is still a different object: a 33-gate example fixes the
output and permits exact extraction while failing to preserve the 1820-row
designated family. A SAT-specific preservation and efficiency theorem is
still needed to combine the source bound with that hard-row requirement.

Theorem-number caution: p.14 refers to a collapse "Theorem 170", but the
current item numbered 170 is a restricted-DNF construction. The actual
compiler and final argument are found at Theorems 203 and 207.

## What the Lean code already provides

- `PiStarConcrete.piZero_isRankMonotoneGauge` proves rank monotonicity for
  the concrete zero-substitution gauge.
- `RouteBPaperFaithfulTPhiExtraction.lean` implements a canonical strict
  extraction and same-target identity-minor data, including
  `routeBPaperFaithfulTPhi_extraction_and_identity_minor`.
- `GlobalGodMoveGauge.lean` distinguishes the raw local product compiler
  from a candidate paper-faithful instrumented source. The separate source
  conditions are named `Theorem207PaperSourcePSideUpperBound` and
  `Theorem207PaperSourceToTargetRankBridge`.
- `GodMoveSATDesignatedExtraction.operationalPaperSource_rank_bridge`
  proves the latter for its concrete normalized SAT-machine source.
  `GodMoveSATDesignatedProjection` gives exact extraction, idempotence, and
  source-specific rank transport in a common enlarged variable space. No
  polynomial source upper bound or global rank-monotonicity contract is
  supplied by these results.
- For the existing raw product compiler, that file already contains
  `theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly`: the
  requested polynomial bound conflicts with its separately established
  large-rank lower bound. This is why simply filling in the raw-bound field
  cannot be the God-Move construction.

These are source-level findings; this review does not claim a fresh full
build of all the historical God-Move modules.

## Two concrete proof obligations in the paper

### Collapse must survive instrumentation on the same polynomial

Theorem 203 Step 3, p.196, forms the global polynomial as a sum of local,
constant-degree gadget contributions. Lemma 204, on the same page, prepends
the multiplicative sheet `Q = product_C (1 - z_C V_C^2)` and asserts that
polynomial rank is preserved. Lemma 224, p.207, asserts the decomposition
`P = Q + R` and cites disjoint addresses and radius-one locality.

Disjoint supports establish additive separability into a verification part
and a computation part. They do not establish that the verification part
is that product. Acceptance preservation under instrumentation also does
not imply preservation of an algebraic rank upper bound. The required
collapse theorem must apply to the fully specified, instrumented source
from which the product is actually extracted.

The small check in `GodMoveAdditiveExtractionCheck.lean` addresses only this
literal sum-versus-product step. It must not be read as a theorem ruling out
every redesigned or separately justified God-Move compiler.

It proves that the sum `(1-z0)+(1-z1)` has mixed derivative zero, whereas
the product `(1-z0)*(1-z1)` has mixed derivative one, and that arbitrary
independent affine substitutions preserve the additive source's zero mixed
derivative. These are the paper's two selector factors after fixing the
clause-square values to one. The final Lean 4.28.0 check passed without
warnings; all printed theorem dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Verification command, from `/home/darre/pall-lean`:

```sh
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/GodMoveAdditiveExtractionCheck.lean
```

### Anonymous profiles must share one small spanning space

Lemma 27, p.42, notes correctly that coordinate permutations preserve the
rank of each matrix. The later profile argument (Lemma 31, pp.43–45) needs
the stronger conclusion that all rows with one profile lie in a single
small subspace of the same coefficient space.

Equal rank under different permutations does not alone prove that conclusion.
For example, the lines spanned by distinct coordinate vectors all have rank
one and are permutation-equivalent, while their combined span has dimension
equal to the number of coordinates. A common factorization or a justified
quotient is needed; if a quotient is used, the same NP minor must survive it.

Lean exposes this requirement in `WithinProfileBound.lean`, notably
`CookLevinWithinProfileFinrankFrontier` and
`CookLevinProfileTemplateCollapseAtProfile`.

## Status

The new [characteristic-target calibration](GodMoveCharacteristicCalibration.md)
also checks a separate representation issue. Section 25.1 (p.126) starts
with Tseitin contradictions and Theorem 117 asserts positive rank for their
characteristic polynomial. But the characteristic polynomial defined in
section 23.2 (pp.122–123) sums only over satisfying assignments: for an
unsatisfiable formula it is exactly zero. This is now verified for genuine
signed CNFs in `GodMoveCharacteristicUnsat.lean`. It is not a refutation of
the later **satisfiable** padded family in Lemma 189 (p.177), or of raw gadget
products that have not been identified with this characteristic polynomial.

The current extraction preserves the actual designated sheet and its rank
lower bound for a specified normalized SAT-machine source. Its polynomial
runtime-derived upper bound remains unproved. The source is a language
characteristic over all words of an encoded length, and the extracted
product is already available from easy unit-query behavior; its large rank
alone does not establish unavoidable SAT computation time. The separation
remains unproved.
