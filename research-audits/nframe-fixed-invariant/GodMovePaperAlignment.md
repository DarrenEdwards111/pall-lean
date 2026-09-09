# God-Move alignment with the desktop paper

The source is `/mnt/c/Users/darre/Desktop/p vs np1.pdf` (280 pages).
It is byte-for-byte identical to `/home/darre/pall-lean/p-vs-np1.pdf`:
SHA256 `c39b7045d58b6ae2cdcd1ae654ccb1314f2adecb2a0934eafe7ec03713a26240`.
Page numbers below are the PDF's printed page numbers.

## Correct proof target

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
  from a candidate paper-faithful instrumented source. The remaining source
  conditions are named `Theorem207PaperSourcePSideUpperBound` and
  `Theorem207PaperSourceToTargetRankBridge`.
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

The correct continuation is the God-Move compiler/collapse/extraction chain,
not an assertion that the local log-det ceiling refutes it. No new proof of
the universal, same-source collapse and minor-preservation combination has
been obtained in this attempt. The separation remains unproved.
