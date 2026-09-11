# Precision throughout the cached construction

The cached discovery and column-selection programs now have polynomial
canonical-rational precision bounds, including their intermediate products,
partial sums and rejected rows. The combined theorem connects these bounds
to the inverse computed for the actual returned projection descriptor.
This closes the remaining rational-stage precision gap. The complete
construction's bit-runtime bound and the SAT-specific derivative-rank bound
are still unproved; this work does not establish separation.

## A bound maintained by the executed insertions

`GodMoveCachedBasisPrecision.Ready` records two properties: the stored span
has Boolean generators, and the stored orthogonal rows have bounded canonical
numerators and denominators. The second property cannot be inferred from the
first alone: an orthogonal basis can be rescaled without changing its span.

`empty_ready` establishes both properties initially, and `insert_ready`
preserves them for the actual cached insertion of any Boolean row. This
includes duplicate and dependent rows. An independent subfamily of the
original Boolean generators and the integer Gram formula bound the unique
orthogonal residual. The proof does not iterate a worsening precision bound
through the insertion history. Selection of that subfamily occurs in the
erased proof, not in the executable algorithm.

For ambient width `s`, stored row coordinates satisfy

`|numerator|, denominator ≤ 2^(5*(s+1)^2)`.

Stored squared norms satisfy the analogous bound with exponent
`(2*5*(s+1)^2+1)*(s+1)`. These are bounds on reduced rational values;
the `.size` magnitude-bit bounds add one to the exponents.

## Every rational stage of discovery, selection and inversion

`GodMoveCachedArithmeticPrecision.matrix_precision` covers stored rows,
norms, scaled-row quotients, products, dot-product accumulators and final
residual-matrix entries. `insert_precision` covers the input, component
dot products and quotients, residual products and accumulators, residual
coordinates and the squared-norm loop. `DotPrecision` refers to the actual
zero-seeded counted loop, including every prefix accumulator.

`GodMoveCachedConstructionPrecision` follows the executed branches:

- Discovery requires a matrix certificate at every attempted round,
  including its final unsuccessful attempt. It requires an insertion
  certificate precisely when the returned sample is inserted.
- Column selection requires an insertion certificate for every materialized
  Boolean column, including columns omitted from the selected basis.
- Inversion uses the sample data and dimension stored in the actual
  `GodMoveCachedProjectionConstruction.construct` result.

The discovery and selection precision proofs hold for any supplied machine
and clock. SAT correctness is used to obtain independence of the final
sample matrix for inversion; no additional caller-supplied precision or
basis-selection hypothesis is introduced.

`construct_cost_and_precision` combines the existing bound of
`32*(s+1)^4` counted rational operations with these three precision
certificates. `construct_precision_budgets_le_circuit` puts their dimensions
under the common exponent `100*(s+1)^4`. Thus all covered canonical rational
numerators and denominators require at most `100*(s+1)^4+1` magnitude bits.

The operation counter still covers residual matrices, basis insertions,
column selection and inverse arithmetic. Internal integer normalization,
coefficient clearing, Boolean evaluation, query construction and encoding,
comparisons, allocation and indexing are outside that counter.

## An explicit subtraction and comparison primitive

`GodMoveBinarySubtract.subtractBits` emits a Boolean subtraction circuit
with exactly eight gates per input bit. Its verified arithmetic identity is

`difference + Y + borrowIn = X + 2^width * borrowOut`.

`subtractBits_borrow_iff` proves that the final borrow is true exactly when
`X < Y + borrowIn`. Output width and reference bounds are proved as well.
Kernel-evaluated examples check ordinary subtraction, underflow and an
incoming borrow.

This is an actual emitted circuit, rather than an assigned arithmetic cost.
It has not been substituted into the rational construction. Its gate count
does not measure circuit construction, wire lookup, allocation or Lean's
external integer implementation.

## The remaining two requested bounds

For complete construction runtime, the rational primitives still need a
verified binary implementation and cost bridge, including division, gcd and
normalization. The builder also needs accounting for its remaining host
operations and linkage to the existing bound on actual SAT-call clocks.
The new subtraction circuit is one primitive toward that implementation;
it is not a division, gcd or complete rational-arithmetic backend.

For the SAT-specific derivative-rank bound, none of these precision or
arithmetic results places the labelled derivative rows into the computed
wire span. The projection's range is unchanged. Correct SAT computation
fixes the decision polynomial, but a bound on its computed wire coordinates
does not establish a bound on their joint derivative span. The existing
SAT-restricted target's equivalence with `SAT_not_in_P` supplies no proof of
either proposition. No missing rank premise has been assumed here.

## Validation

The complete expanded audit passed under Lean 4.28.0:

- 137 audit modules;
- 1,086 printed axiom checks;
- 556 files in the checked source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked source predates its final log. The four new Lean files contain
no `sorry`, `admit`, custom axioms or `native_decide`. Independent reviews of
the arithmetic-stage coverage and the report found no scope mismatch.

Reproduction:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260911/cached-all-precision-checks
```

The local result record is
`/home/darre/godmove-audit-20260911/cached-all-precision-checks/results.json`.
