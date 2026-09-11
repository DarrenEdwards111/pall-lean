# Constructed projection weights from actual SAT-machine discovery

2026-09-11. Continuation of `aed2b17b`.

The discovered wire projection now has an executable numeric descriptor,
including its inverse weights. The finite duality equations and exact
wire-space range are proved from the construction. The weight-building
stage uses at most `8r³` rational arithmetic operations, and its final
weights have polynomial bit length. This does not prove the SAT-specific
derivative-rank bound or a complete bit-runtime bound for discovery and
projection construction. Separation remains unproved.

## Completing the numeric construction

The existing procedure uses a supplied, globally correct SAT machine to
discover separating assignments and select independent original circuit
wires. Earlier modules proved their spanning, independence, query counts,
and certain precision bounds, but did not construct the final inverse
weights needed by `SampleCertificate` and `WireCertificate`.

`GodMoveProjectionSamples` now forms the square matrix

```
A[j,k] = value of selected wire k on discovered sample j.
```

Each sample runs the original Boolean circuit once; all selected values
are then stored in a vector. The discovery theorems show that sample and
basis counts agree, and column independence proves that this actual matrix
is nonsingular. The entries are zero or one. No expanded polynomial
coefficients or enumeration of all assignments enter this matrix-building
step.

`GodMoveTrackedOrthogonalization` constructs the inverse weights using
rational Gram–Schmidt with tracked coefficients. It stores the orthogonal
rows `U`, their coefficients `C` relative to the original rows, and their
squared norms. Lean proves the invariant

```
U = C A.
```

At each step, the projection coefficients are computed once. Both the
numeric residual row and its coefficient row are materialized as vectors.
The nonzero-norm, orthogonality, tracking, and processed-span invariants
are all derived from independence of the original rows.

The final stored weight matrix is

```
W = Uᵀ diag(1 / norm_i) C,
W A = I.
```

The identity is a theorem about the computed matrix. The builder receives
neither a supplied inverse nor a duality certificate, and uses no
determinant enumeration. Materializing the rows matters: merely storing
functions that recursively recompute preceding rational expressions would
not establish the same operation count.

## What the cost and precision proofs establish

`GodMoveTrackedOrthogonalizationCost` instruments actual rational
addition, subtraction, multiplication, and division operations. Its dot
products use explicit loops; the intermediate and final values are stored.
Erasure of the counters returns exactly the proved numerical builder.
For an `r × r` input matrix, the exact count satisfies

```
2 · operations + r = 10r³ + 5r²,
operations ≤ 8r³.
```

`GodMoveProjectionWeightPrecision` independently derives the final weight
bound from `W A = I` and the zero/one entries of `A`. It proves

```
W[i,j] = adj(A)[i,j] / det(A),
abs(numerator(W[i,j])) ≤ r!,
denominator(W[i,j]) ≤ r!.
```

Consequently each canonical numerator magnitude and denominator has at
most `(r+1)²+1` bits. The determinant and adjugate appear only in the proof
of this bound; the executable builder uses the cached row algorithm.

The operation count prices rational arithmetic as arithmetic operations.
It excludes acquiring the input matrix, memory traffic, and the bit cost
of each rational operation. The final-entry bound does not by itself
bound all intermediate rows, norms, quotients, or partial sums. A complete
bit-runtime proof must also bound those values and account for the host
discovery, query construction, and the supplied machine's executions.
No such complete runtime claim is made here.

## The resulting production gauge

`GodMoveConstructedProjection.machineDescriptor` stores the discovered
samples, selected original wire references, and computed rational weights.
Its companion `machineCertificate` satisfies the existing `WireCertificate`
type. The caller supplies only the actual SAT machine and its correctness;
numeric duality and global wire spanning are derived, not additional
caller-supplied hypotheses.

The resulting `sampledGauge` is an idempotent projection whose range is
**exactly the computed-wire space**. Its rank equals the previously bounded
wire rank. When constructed for the supplied machine's own unrolled
circuit, it fixes the actual SAT decision characteristic and inherits the
quartic input-plus-clock rank bound. The explicit Boolean-point evaluator
uses the original shared circuit and the input polynomial's values at the
stored samples. Values of an arbitrary input polynomial must still be
provided or computed.

This projection has the same wire-space range and production rank as the
earlier algebraic wire gauge; it need not agree with that gauge on inputs
outside the range. It does not replace the distinct quadratic snapshot
gauge or the designated derivative-row gauge.

## The separation requirement is still open

No SAT-specific upper bound on the source's full derivative space was
obtained. The existing canonical-source theorem and unit-face minor remain
unchanged, as does the formal equivalence between the proposed
polynomial-clock SAT rank estimate and the faithful separation target.

Constructing the wire projection's weights does not place the hard
derivative rows in its range. The earlier wire-space and snapshot-space
counterexamples already exclude that inference from output preservation
alone. The construction also continues to rely on a supplied correct SAT
machine; it does not construct an independent polynomial-time SAT solver.

## Validation

The five new modules are included in the source-matched audit checker.
The numerical builder also executes checks on a nontrivial `2 × 2` inverse
and the empty matrix. The theorem proofs use no native-evaluation axiom.

```bash
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260911/constructed-projection-checks
```

The complete run passed on Lean 4.28.0: 118 audit modules, a 537-file source
closure, and 943 printed axiom checks. The focused modules emitted zero
warnings and used only `propext`, `Classical.choice`, and `Quot.sound`.
The five new modules account for 42 checks. The production dependency
build succeeded and replayed existing linter warnings. The machine-readable
result is
`/home/darre/godmove-audit-20260911/constructed-projection-checks/results.json`.
