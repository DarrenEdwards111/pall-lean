# Discovery through an actual supplied SAT machine

The subsequent [revision audit](GodMoveDiscoveryRevisionAudit.md) checks this
construction against the selector-to-SAT objection. It validates the
conditional use of a hypothetical correct SAT machine, while proving that
the added guarantees do not eliminate that hypothesis or establish separation.

This continuation replaces the abstract predicate-existence oracle on the
wire-discovery path with explicit Boolean circuits, their actual CNF encodings,
and clocked runs of a supplied SAT machine. Lean proves that the returned
samples separate the entire computed-wire space and that the selected wire
indices form an exact basis. It also derives polynomial bounds on the number
of direct SAT requests, the rational coefficient bit lengths at every
discovery state, and the sizes of the emitted queries.

**Correctness assumes `Decides M SATLang T`. This constructs neither a
polynomial-time SAT decider nor a superpolynomial SAT lower bound. The full
runtime of the composite discovery implementation remains unproved.**

The logical direction matters. The earlier reduction derives SAT correctness
from an unrestricted separating selector. An efficient implementation with
efficiently readable sample assignments would therefore supply an efficient
SAT algorithm; that reduction did not include a Turing-machine cost theorem.
Here SAT computation is supplied as a hypothesis and used to implement discovery.
If the supplied SAT clock is polynomial, the proved bounds give polynomially
many requests of polynomial size with polynomial machine-clock bounds. This
conditional construction is consistent with the earlier reduction and does
not contradict a presumed hardness result by itself.

## Concrete construction and semantic connection

For an `s`-gate circuit `c` on `n` Boolean inputs, each sampled assignment gives
the actual 0/1 values of all `s` wires. The maintained rational basis spans these
sampled rows. Its orthogonal residual operator has explicit coefficient rows
`q_j`. A new wire row lies outside the current span exactly when one of the
relations `sum_i q_j(i) * wire_i` is nonzero.

The implementation now handles each such relation as follows:

1. `GodMoveRationalClearing` multiplies by the positive product of the actual
   coefficient denominators. It proves that the resulting integer relation
   has exactly the same zero set. Both the common denominator and the cleared
   integer magnitudes have bounds in the supplied coefficient precision.
2. `GodMoveSignedBinary` serializes those integers with a sign and explicit
   little-endian magnitude bits. Reconstruction is proved exact at the chosen
   width. For coefficients with numerator and denominator bounded by `2^b`,
   each magnitude uses `(s+1)*b+1` bits.
3. `GodMoveBinaryAdder`, `GodMoveControlledWord`, `GodMoveWireSum`, and
   `GodMoveWeightedWireQuery` construct a Boolean circuit for the relation.
   The original circuit and its wire sharing are retained. Positive and
   negative sums use full-carry adders, and a comparator tests inequality.
   No Boolean assignment table enters the construction.
4. `GodMoveCircuitCNFSize` bounds the existing production Tseitin encoder,
   including its actual bit codec. `GodMoveMachineCircuitOracle` runs
   `decideOut M` on that encoded word for `T(word.length)` steps. The equivalence
   between the answer and circuit satisfiability follows from `Decides` and
   the existing verified encoder; it is not a supplied answer-equivalence
   assumption. Prefix specialization fixes an input without increasing the
   gate count, yielding a witness in at most `n+1` direct SAT requests.
5. `GodMoveRationalMachineQuery` connects this complete query path to the
   original rational relation. `GodMoveMachineRowFinder` tries its residual
   coordinate rows and returns an independent wire row, or proves that every
   Boolean wire row already belongs to the current span.
6. `GodMoveMachineDiscovery` performs the adaptive insertions and then selects
   basis columns from the returned sample table. It needs no `CubeOracle` or
   `OracleCorrect` argument. Starting with `s+1` rounds suffices, and both the
   number of samples and number of selected basis wires equal `wireRank c`.

`actualMachine_basis_connection` instantiates discovery on the supplied
machine's own unrolled circuit `circuitFor M L (T L)`. The selected wires span
exactly its computed-wire space. Their span contains the SAT decision
characteristic on encoded inputs of length `L`, and their number is at most
`circuitConstant M * (L + T L + 1)^4`. Thus the construction is connected to the
same machine whose correctness supplies the SAT queries. This is a symbolic
space across the input slice; its rank is not the dimension of scalar values
from a single fixed run.

## Derived precision and query bounds

The coefficient budget is no longer an unexplained assumption about the
adaptive states. `GodMoveGramPrecision` considers an independent 0/1 matrix
`R` with `r` rows and `s` columns and forms the integer matrices

```text
G = R Rᵀ
D = det(G) I - Rᵀ adj(G) R.
```

Lean proves `det(G) != 0`, identifies the kernel of `D` with the span of the
original rows, and bounds each integer entry of `D` by
`(r*r+1) * r! * (s+1)^r`. More specifically, for any maintained basis with
that row span, the actual residual coefficient is exactly
`D[j,i] / det(G)`. Bounding the canonical rational numerator and denominator
then gives at most `2*(s+1)^2+1` bits for each, since independence implies
`r <= s`. The determinant expansion is used to prove the magnitude bound;
the discovery implementation does not compute these determinants.

`GodMoveGramSamplePrecision` constructs the required independent original
0/1 rows from the current sample list, using the existing row selector.
There is no supplied independent-basis or precision witness. Its theorem
requires only the maintained equality between the numeric basis span and
the sample-row span.

`GodMoveMachineDiscoveryPrecision` preserves that equality down the actual
executed discovery branch. `machineSearch_precision` therefore bounds the
computed `coefficientBits` of every residual relation at every state where
queries can occur. This is a bound on the coefficients the driver actually
uses, rather than on alternative relations not connected to it.

Writing `b(s) = 2*(s+1)^2+1` and

```text
Q(s,b) = 32 * (s+s+s*((s+1)*b+1)+1)^2,
```

the proved bounds are:

| Quantity | Bound |
| --- | --- |
| Direct SAT requests recorded by one discovery search | `(s+1)*s*(n+1)` |
| Returned samples and basis wires | Exactly `wireRank c`, at most `s` |
| Residual coefficient numerator/denominator bit lengths | `b(s)` |
| Gates in a generated relation circuit | `Q(s,b(s))` |
| Actual encoded initial coordinate-query word length | `100*(n+Q(s,b(s))+1)^2` |
| Its SAT-machine clock, if `T(m) <= C*(m+1)^d` | `C*101^d*(n+Q(s,b(s))+1)^(2*d)` |

Witness-search restrictions preserve gate count and decrease the input arity,
so the same size majorant applies to those restricted circuits. The explicit
clock theorems concern individual requests, not an operational cost semantics
for the full host program.

## What remains unresolved

The current implementation stores rational vectors as functions. A newly
stored residual can retain older projection functions, so repeated coordinate
evaluation can repeat prior arithmetic. Polynomial dimensions and canonical
coefficient bit lengths do not prove polynomially many host arithmetic steps.
A materialized implementation with proved reuse and a combined cost theorem
is still required. The present bounds also do not count all intermediate
arithmetic, rational normalization, compilation, encoding, or final column
selection. They do not establish a polynomial-time composite
`ComposableMachine`.

`PolyBounded T` bounds the values of a supplied clock function; it does not
bound the cost of evaluating that function. A future uniform runtime theorem
must address this, for example by using an explicit polynomial majorant as
the clock. The query counter models direct requests in one search. Calling
`machineSamples` and `machineBasisIndices` separately runs discovery twice;
the count is not a claim of shared execution across separate calls.

The complete sampled gauge certificate still needs its inverse weights and
their cost connection. Production definitions are unchanged. In particular,
the previously proved obstruction for unrestricted production minimizers
remains: their rank is bounded with fixed positive weights, and unit rank and
barrier weights force the zero projection. The restricted scalar-query lower
bound still does not apply to an algorithm that reads circuits and their
internal wires.

No result here proves an unavoidable superpolynomial lower bound for every
SAT decider on the same computed invariant. That is a missing mathematical
result, separate from implementing and costing this conditional discovery.
No `P != NP` theorem is claimed.

## Verification

On 2026-09-10, all **61 focused modules** passed, with **493 printed axiom
checks**, zero warnings, and only `propext`, `Classical.choice`, and
`Quot.sound`. The checker matched a 479-file source closure, including byte
comparisons of the imported production sources and dependency configuration.
No production source changed.

The focused check uses Lean 4.28.0 and rebuilds the source-matched production
imports before compiling the audit modules:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/machine-query-checks
```

On a checkout with its own dependencies, omit `--dependency-checkout`.
The new guarded executable checks exercise signed cancellation, multi-bit
carries, and the fractional relation `x/2 + y/3 - 5/6`. These small tests
enumerate two-input assignments only to check the emitted circuit; the
discovery definitions do not enumerate assignments.
