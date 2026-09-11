# Signed rational backend and cached dot execution

The backend now executes addition, subtraction, multiplication and division on
stored Boolean rational operands and returns their canonical signed results.
The fixed-width dot circuit matches the existing counted rational loop, and
its materialized execution is connected to the cached construction's proved
precision certificates. A separate tape-machine lemma supplies a concrete
framed append operation with an exact clock.

The complete construction runtime and SAT-specific derivative-rank bound are
still unproved. No separation theorem without the existing missing premise
has been obtained.

## Canonical rational operations

[GodMoveRationalWireEncoding.lean](GodMoveRationalWireEncoding.lean) defines a
sign reference and two little-endian magnitude words. `Represents` asserts
equality with the canonical rational numerator and positive denominator.
These equalities imply exact decoded value and rule out a zero denominator.
Zero may carry either sign; both denote the canonical integer numerator zero.

The new operations emit gates for their arithmetic and cancellation. Native
rational operations specify the result; they do not calculate the returned
Boolean bits.

| Circuit | Result | Output magnitude width | Gate bound for width-`w` operands |
| --- | --- | --- | --- |
| `GodMoveSignedArithmetic.addSigned` | Exact signed integer sum | `w+1` | Exactly `27*w+7` |
| `GodMoveSignedArithmetic.subtractSigned` | Exact signed integer difference | `w+1` | Exactly `27*w+8` |
| `GodMoveBinaryRationalAdd.addFractions` | Canonical rational sum | `2*w+1` | `1024*(w+1)^3` |
| `GodMoveBinaryRationalAdd.subtractFractions` | Canonical rational difference | `2*w+1` | `1024*(w+1)^3` |
| `GodMoveBinaryRationalMultiply.multiplyFractions` | Canonical rational product | `2*w` | `1024*(w+1)^3` |
| `GodMoveBinaryRationalDivide.reciprocalFraction` | Canonical reciprocal | `w` | Exactly `8*w+4` |
| `GodMoveBinaryRationalDivide.divideFractions` | Canonical rational quotient | `2*w` | `1040*(w+1)^3` |

Signed addition retains the carry. Opposite signs use the magnitude difference
and its appropriate sign. Rational addition uses cross products; all four
operations use the verified gcd and division circuits for canonical reduction.
The reciprocal circuit detects a zero numerator and selects `0/1`, so division
by zero follows the repository's totalized rational convention. No nonzero
divisor premise is imposed.

[GodMoveBinaryScalarExecution.lean](GodMoveBinaryScalarExecution.lean) packs
each operand's actual sign and magnitude lists into the initial wire store.
The output sign and both output words are read from the executed store.

[GodMoveBinaryRationalBackend.lean](GodMoveBinaryRationalBackend.lean) joins
packing, operation dispatch and materialized execution. Its `inputWidth` is
the sum of the four stored magnitude-list lengths plus one, so width selection
uses the supplied representation, including any padding. For this width `w`,
the store has `4*w+2` bits, the circuit has at most `2048*(w+1)^3` gates, and
at most `4*w+3` output bits are read. `evaluate_correct_and_cost` proves the
canonical result and an evaluator traversal bound of

`40000000*(w+1)^6`.

## Fixed-width dot calls in the cached construction

Simply composing rational circuits would repeatedly enlarge stored widths.
The new `resize_represents` theorem instead proves that padding and taking
exactly `w` bits preserves a canonical value whose actual numerator magnitude
and denominator are strictly less than `2^w`. The existing `BitBound q b`
certificate supplies that condition at `w=b+1`.

[GodMoveBinaryDotProduct.lean](GodMoveBinaryDotProduct.lean) emits the actual
multiply-normalize-resize-add-normalize-resize sequence at each iteration.
`dotFits_of_dotPrecision` derives safe resizing for every product and partial
sum from the existing `DotPrecision` certificate. It covers the empty dot and
all prefixes, not just the final answer.

`dotFrom_sumProductsOn` proves canonical representation of the same value as
the existing `sumProductsOn` loop. For `s` pairs at precision exponent `b`,
the emitted program contains at most

`2048*s*(b+2)^3`

gates and keeps both output magnitude words at `b+1` bits.

[GodMoveCachedBinaryDotExecution.lean](GodMoveCachedBinaryDotExecution.lean)
executes that program and collects its actual output. If the input-list length
is `I` and the initial wire-store length is `V`, it proves a traversal bound of

`40000000*(I+V+s+b+2)^8`.

The four cached-call specializations cover component sums, residual-coordinate
sums, residual norms and residual-matrix sums, including a zero residual that
insertion rejects. They use readiness of the actual cached basis and, for
insertion calls, Boolean input rows to discharge the intermediate precision premise at
`b = arithmeticBits s = 100*(s+1)^4`. The initial reference/representation
relation remains explicit: these theorems verify individual dot replacements
on correctly stored operands. The full adaptive builder has not yet been
rewritten to maintain that relation across every branch.

## What has reached the tape-machine model

[GodMoveSATPaddingInvariance.lean](GodMoveSATPaddingInvariance.lean) proves
that appending false bits does not change the decoded formula or `SATLang`,
including malformed and truncated encodings. This checks compatibility with
the machine's inability to observe trailing blank tape cells. It also proves
that no total halting machine can transduce every raw list `xs` to
`xs ++ [true]`: the empty input and a single false bit have identical tape
observations but require different output bits. An explicit frame is therefore
necessary for the intended list-storage implementation.

[GodMoveMarkedFrameMachine.lean](GodMoveMarkedFrameMachine.lean) uses the
existing doubled-bit encoding `b -> bb`, terminated by `01`. It proves that
the actual 28-state append machine has appended one fixed Boolean bit to a
payload of length `L` and halted after `2*L+6` steps. This is a proved clock,
not a least-halting-time theorem. The theorem preserves an arbitrary
prefix workspace when started at the frame's offset. It also supplies a
forced-initialization contract and handles trailing false padding through
observational equivalence. An arbitrary nonblank suffix is outside this
append contract, and choosing the bit at runtime still needs a controller.

This is a verified machine primitive, not the complete machine interpreter.
In particular, the uniform interpreter must keep arbitrary circuit code and
indices on tape; specializing the machine's finite control to each whole
generated circuit would not establish a uniform runtime theorem.

## Remaining obligations

The scalar and dot counters charge the Boolean/list evaluator's wire scans,
store appends, dispatch and output reads. They exclude operand packing,
reference-list construction and resizing, circuit generation, truth-table
lowering, native allocation and instrumentation-counter arithmetic. A complete
machine bound must implement and account for those operations, the remaining
query serialization and storage work, and adaptive control, then combine them
with the already tracked clocks of actual SAT calls. The framed append result
does not automatically compile that whole program.

The independent rank audit found no derivation of the requested SAT estimate.
[GodMoveSATRuntimeFrontier.lean](GodMoveSATRuntimeFrontier.lean) already proves
`SATPolynomialClockRankBound ↔ SAT_not_in_P`; the reverse direction is vacuous
when no polynomial-time SAT decider exists. Thus supplying that estimate as a
new backend field would assume exactly the unresolved separation target.

The normalized source rank concerns the SAT decision polynomial on all words
of the designated encoded length. Correctness makes it independent of the
particular correct machine and clock. Computing a selected order-`k` derivative
entry using `2^k` pinned answers controls work per entry, not the span over all
choices of derivative and shift. At the logarithmic derivative window, the
existing lower bound still gives superpolynomially many independent directions.
The new arithmetic backend does not establish simultaneous containment of
those directions in a runtime-controlled space.

## Validation

All eleven new modules passed their individual Lean checks. The scalar,
cached-dot and framed-machine endpoints then passed a fresh rebuild of their
complete GodMove import closure under Lean 4.28.0:

- 63 audit modules, including all eleven new modules;
- 522 printed axiom checks;
- 488 files in the matched source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked Lean source predates its final log. The new sources contain no
`sorry`, `admit`, custom axioms or `native_decide`. Closed kernel evaluations
cover signed carry, negative sums, opposite signs, subtraction of a negative,
cancellation, negative zero and a negative reciprocal. Independent reviews
checked the arithmetic semantics, bounds, cached-call premises and report scope.

The full 156-module default audit was not rerun. Reproduce the focused check:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --module GodMoveBinaryRationalBackend \
  --module GodMoveCachedBinaryDotExecution \
  --module GodMoveMarkedFrameMachine \
  --log-dir /home/darre/godmove-audit-20260911/binary-rational-backend-checks
```
