# Polynomial precision throughout the constructed projection's inverse

The numeric inverse stage now has proved polynomial precision throughout its
execution, in addition to its existing cubic rational-operation count. The
SAT-specific derivative-rank bound remains unproved. This result does not
establish separation or the complete construction's bit-runtime bound.

## What is proved

For an independent Boolean `r × r` sample matrix, the same cached inverse
algorithm used by `buildDescriptorWithCost` has these guarantees:

- It computes the inverse weights satisfying the projection's duality identity.
- It uses at most `8*r^3` rational additions, subtractions, multiplications and
  divisions.
- Every canonical rational operand and result, including every partial sum of
  each dot-product loop, has numerator magnitude and denominator at most
  `2^(100*(r+1)^4)`. Each therefore needs at most `100*(r+1)^4+1` magnitude
  bits, with the numerator sign accounted for separately.

The input's Boolean entries and independence are the only mathematical
premises for this numeric-stage theorem. The actual SAT-machine discovery
wrapper derives both premises from `Decides M SATLang T`; callers do not
supply a precision bound, inverse, duality identity or spanning certificate.
Discovery still uses that supplied SAT decider.

## Why the intermediate bounds hold

`GodMoveTrackedRowPrecision` bounds every stored orthogonal row `U` by writing
it as the exact residual of an original Boolean row against an independent
prefix of the original matrix. The integer Gram formula gives one bounded
denominator for the whole row. The tracking identity `U=C*A`, together with
the already proved inverse and its cofactor formula, similarly bounds each
stored provenance row `C`. Both have canonical magnitudes at most
`2^(5*(r+1)^2)` at every prefix of the actual cached builder.

This is a global algebraic bound on stored values. It does not repeatedly
apply a generic height estimate from one orthogonalization step to the next,
which would give a much poorer bound.

`GodMoveRationalPrecisionArithmetic` proves canonical rational bounds under
addition, subtraction, multiplication, division, and finite sums. Its list
prefix results allow repeated indices and bound each partial sum directly.

`GodMoveDotLoopPrecision` connects these prefixes to the instrumented
`sumProductsOn` implementation. Running a prefix and resuming its suffix is
the same execution, including its counter. `DotPrecision.step` covers the
actual multiplication operands and result, the current accumulator and the
next addition result; `DotPrecision.result` covers the returned dot product.

`GodMoveTrackedArithmeticPrecision.inverse_precision` assembles these bounds
for input rows, stored rows and provenance coefficients, norms, component
quotients, both residual updates, new norm calculations, scaled rows and all
final weight sums. `inverse_correct_cost_precision` combines this certificate
with correctness and the cubic count for the same materialized inverse.

`GodMoveConstructedProjectionPrecision` applies the result to the exact matrix
wrapper used by the descriptor builder and then to the actual machine-discovered
samples. Its precision assertion covers this numeric inverse kernel.

For the faithful unrolling of a SAT machine at encoded input length `L`,
`actualSAT_descriptor_precision_budget_le_clock` also proves that the exponent
is at most

`100*(circuitConstant M*(L+T L+1)^4+1)^4`.

This follows from the proved sample-count/wire-rank identity and circuit-size
bound. Thus the numeric precision bound is polynomial in the original input
length and supplied computation clock, not just in an unconstrained matrix
dimension.

The determinant and cofactor formulas are used in proofs. The executing
builder remains the cached orthogonalization algorithm; it does not compute
determinants by enumerating permutations.

## Exact remaining scope

Canonical rational precision and the rational-operation count are established.
This does not formally bound the internal integer work of Lean's rational
primitives, allocation and indexing, circuit evaluation or discovery, nor
compile the complete construction to a clocked Turing machine. Those costs
must be connected to the construction before claiming a verified total
bit-runtime bound. Polynomially many bounded rational operations address the
numeric kernel; they are not a theorem about the entire host implementation.

The semantic projection's range is exactly `wireSpace c`, and its rank is
`wireRank c`. For an actual SAT decider, the existing construction fixes the
SAT decision polynomial and has a rank bound derived from its unrolled
circuit's runtime. Fixing that output does not imply fixing its derivatives
or containing their joint span. The existing six-input conjunction test
already shows a derivative direction lost by the constructed wire projection;
that test is a calibration, not a counterexample to the SAT-specific target.

The paper's proposed profile argument also needs this distinction. Lemma 27
of `p-vs-np1.pdf` (printed page 42) preserves individual ranks under
permutations of interface identities. Lemma 31 (pages 43–44) then needs a
common small space for all placements with the same histogram. Equal ranks
under different invertible permutations do not establish that common-span
claim. For `∏ᵢ Xᵢ`, the order-`k` derivatives all share the same profile and
are permutation-equivalent, yet their distinct complementary monomials span
`choose(r,k)` independent directions. The existing unit-characteristic
coefficient-minor theorems formalize that independence. Identifying the
labels can discard the minor required by the lower bound.

`GodMoveSATRuntimeFrontier.satPolynomialClockRankBound_iff_separation` already
identifies the remaining SAT-restricted upper bound as equivalent to
`SAT_not_in_P`, given the established matching source lower bound. The reverse
direction is vacuous when no polynomial-clock SAT decider exists. That
equivalence neither proves the bound nor makes it false. A valid SAT-specific
argument controlling the joint labelled derivative span is still missing.

## Validation

The complete focused checker passed under Lean 4.28.0:

- 124 audit modules;
- 995 printed axiom checks;
- 543 files in the checked source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked source predates its final log. The new sources contain no `sorry`,
`admit`, custom axioms or `native_decide`.

Reproduction:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260911/intermediate-precision-checks
```

The local result record is
`/home/darre/godmove-audit-20260911/intermediate-precision-checks/results.json`.
