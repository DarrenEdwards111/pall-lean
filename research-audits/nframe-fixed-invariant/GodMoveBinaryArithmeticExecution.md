# Binary normalization with counted circuit execution

The arithmetic backend now includes emitted Boolean circuits for variable-word
multiplication, unsigned division, gcd and rational normalization. A concrete
Boolean/list evaluator executes the normalization circuit and materializes its
canonical output words with a proved polynomial traversal bound. Integer bounds
also cover the raw products and sums before rational cancellation.

The complete cached construction runtime and SAT-specific derivative-rank
bounds remain unproved. These results do not establish separation.

## Executable arithmetic circuits

All words are little-endian lists of references to earlier Boolean wires.
Both operands may vary at execution time and may share references. Natural
multiplication, division, remainder and gcd appear in the mathematical
specifications, not as instructions in the emitted circuits.

| Component | Proved behavior | Proved emitted gate bound |
| --- | --- | --- |
| `GodMoveBinaryMultiply.productBits` | Exact product; exactly `m+w` output bits | `6*m*(m+1)*(w+2)` |
| `GodMoveBinaryDivision.divideWords` | Exact quotient and remainder of two width-`w` words | Exactly `11*w^2+17*w+2`, at most `16*(w+1)^2` |
| `GodMoveBinaryGCD.gcdWords` | Exact gcd; exactly `w` output bits | At most `64*(w+1)^3` |
| `GodMoveBinaryFractionNormalize.normalizeWords` | Reduced numerator magnitude and denominator, both width `w` | At most `96*(w+1)^3` |

Multiplication retains carries internally, then proves that removing high zero
bits preserves the exact product. Division uses restoring long division,
subtraction and Boolean selectors. Its zero-divisor output is `(0, dividend)`,
matching the repository's totalized natural division and remainder conventions.

Gcd unrolls `2*w+1` actual division/selection rounds. Both operands freeze once
the second operand reaches zero. This avoids the invalid continuation that
would otherwise swap a terminated `(a,0)` state to `(0,a)`. Its exact gate count
is `(2*w+1)*(11*w^2+25*w+4)`.

`GodMoveEuclideanBitIterations` proves the necessary fuel bound from the
executed Euclidean algorithm. Two nonterminal steps strictly halve the second
operand. The algorithm finishes within `2*Nat.size(b)+1` remainder calls; its
actual call log and counter agree. All division operands remain within the
original maximum operand, so the original width is sufficient throughout.

Normalization computes the gcd once and reuses its output wires in two
division circuits. For a supplied positive raw denominator, its actual outputs
equal the canonical rational numerator magnitude and denominator. The original
numerator sign is retained separately; the signed reconstruction theorem
recovers the actual normalized rational. A zero numerator normalizes to `0/1`.

## Integer precision before cancellation

`GodMoveRationalPrimitiveBounds` supplies explicit positive-denominator raw
fractions whose normalizations equal rational addition, subtraction,
multiplication and division. If the operands have canonical precision
exponents `b` and `c`, the raw integer magnitudes are bounded by:

- `2^(b+c+1)` for addition and subtraction;
- `2^(b+c)` for multiplication and division.

The individual cross products are bounded before their addition or
subtraction. Gcd cancellation is exact and cannot increase either magnitude.
These bounds also control the input widths and invocation count of the
executed Euclidean algorithm. Rational division includes the zero-reciprocal
convention.

This gives a proved normalization path with bounded internal operands. It is
not an identification with every optimization in Lean's native `Rat` code,
and the complete rational-operation replacement has not yet been installed
in the cached projection builder.

## What the execution counter proves

`GodMoveBooleanExecutionCost` stores each Boolean operator as a finite truth
table. Its recursive programs explicitly scan the input or wire list for
each read, append the new bit by copying the current immutable list, and
materialize each requested output word by reading its references. Repeated
references cause repeated counted reads. Input-variable lookup is counted.

The erasure theorem agrees with the production `runFrom` evaluator. For `G`
gates, input length `I` and initial wire-store length `V`, execution uses at
most

`7*G*(I+V+G+1)`

steps in the stated Boolean/list traversal model. Collecting `R` output bits
adds at most `R*(V+G+2)+1` steps.

`GodMoveBinaryArithmeticExecution.evaluateNormalization_correct_and_cost`
joins that evaluator to the actual normalization circuit. It proves the
decoded result and the cost bound for the same execution, including both
materialized output words. Its polynomial bound is

`100000*(I+V+w+1)^6`.

This counts the specified dispatch, Boolean selection, list/index traversal
and store/output materialization operations. Circuit generation, conversion
of operators to truth tables, native allocation, the arithmetic of the
instrumentation counter itself, and a compilation into `ComposableMachine`
are outside this bound. The evaluator theorem therefore does not assert the
complete construction's bit-runtime bound.

## The remaining construction and rank requirements

The binary backend still needs to replace the cached builder's rational
primitives, with a proved representation relation across its actual adaptive
branches. The full runtime proof must include code generation, coefficient
clearing and serialization, Boolean query construction, storage management
and the remaining host operations, then combine those costs with the
existing sum of actual SAT-call clocks in a specified machine model.

The SAT investigation checked the proposed shared derivative evaluator.
Finite differences allow evaluating one selected order-`k` derivative from
`2^k` answers. This does not bound the span over all derivative choices.
The existing actual equality circuit has `4r+1` gates and a selector/input
response matrix of rank `2^r`; its selector specializations are independent
delta functions. Thus small shared evaluator size does not imply a small
joint specialization span.

For the SAT-derived evaluator, the missing implication is a polynomial bound
on that joint rank using additional SAT-specific consequences of correctness
and runtime. The existing unit-face extraction preserves a binomial
independent family; its labels cannot simply be identified during
compression. No independent proof of the SAT-restricted rank bound was found,
and no such premise was inserted into the new arithmetic theorems.

## Validation

All eight new modules passed their individual Lean checks. The endpoint and
its complete transitive GodMove import closure then passed a fresh rebuild
under Lean 4.28.0:

- 42 audit modules, including all eight new modules;
- 364 printed axiom checks;
- 443 files in the checked source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked source predates its final log. The new Lean files contain no
`sorry`, `admit`, custom axioms or `native_decide`. Closed kernel evaluation
checks cover multiplication, ordinary and zero-divisor division, gcd including
zero inputs, and normalization including a zero numerator. Independent
reviews checked the algorithms, evaluator accounting, bounds and report scope.

The checker now accepts `--module` and rebuilds the selected endpoint's full
GodMove dependency closure in dependency order. The complete default suite
contains 145 modules; that broader suite was not rerun for this change.

Reproduction:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --module GodMoveBinaryArithmeticExecution \
  --log-dir /home/darre/godmove-audit-20260911/binary-arithmetic-execution-checks
```

The local result record is
`/home/darre/godmove-audit-20260911/binary-arithmetic-execution-checks/results.json`.
