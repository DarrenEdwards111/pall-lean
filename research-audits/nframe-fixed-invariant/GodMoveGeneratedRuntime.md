# Counted rational generation and a shared read/write machine

The new scalar endpoint runs the actual counted rational generator before
serializing, decoding and executing its program. Division, gcd, normalization,
signed arithmetic and all four rational operations now have generation bounds.
A separate finite-control machine reads a selected stored wire and appends its
actual value using the reader's existing encoding.

The complete adaptive construction's machine-runtime bound and the SAT
derivative-rank bound remain unproved. This work does not establish separation.

## Actual circuit generation

The generators recurse through counted list/index operations and return the
whole program together with its output references. Their erasure theorems prove
exact equality with the preceding verified circuits, including canonical
rational normalization. Native rational arithmetic does not supply their bits.

| Generator | Bound for equal operand widths `w` |
| --- | --- |
| [Division](GodMoveBinaryDivisionCompileCost.lean) | Exactly `250*w² + 335*w + 36`, at most `512*(w+1)²` |
| [Signed addition](GodMoveSignedArithmeticCompileCost.lean) | Exactly `453*w + 94` |
| [Signed subtraction](GodMoveSignedArithmeticCompileCost.lean) | Exactly `453*w + 99` |
| [Gcd](GodMoveBinaryNormalizationCompileCost.lean) | At most `32768*(w+1)^5` |
| [Normalization](GodMoveBinaryNormalizationCompileCost.lean) | At most `65536*(w+1)^5` |
| [Full rational dispatch](GodMoveGeneratedScalarBackend.lean) | At most `10000000*(w+1)^5` |

[GodMoveBinaryRationalCompileCost.lean](GodMoveBinaryRationalCompileCost.lean)
assembles multiplication, reciprocal and division.
[GodMoveRationalAddCompileCost.lean](GodMoveRationalAddCompileCost.lean)
assembles addition and subtraction. Both use the counted normalization
generator. The counters include code-length scans, successive offsets,
reversal, zips, padding, trimming and repeated copies of gate prefixes.

These are bounds in the existing traversal model: natural successor and
zero tests are primitives; previously stored indices and immutable tails can
be shared. They are not bounds for deep copying arbitrary unary indices,
native allocation, or serialized input bytes. Counter arithmetic itself and
conversion of arbitrary function-valued gates into truth tables are excluded.

## Integrated scalar endpoint

`GodMoveGeneratedScalarBackend.evaluateGenerated` prepares the actual operand
store once, runs `compileCounted`, and passes the returned code and references
to the stored-program backend. That backend serializes and decodes the program,
executes it once and reads the result's sign and magnitude words. The cost of
the generator is part of this execution's counter.

`evaluateGenerated_correct_and_cost` proves canonical rational correctness and

`210000000*(inputWidth x y + 1)^6`

traversal steps. Here `inputWidth` is the sum of the four supplied magnitude-list
lengths plus one. The bound is on the actual returned execution, rather than
a separately supplied cost certificate. The scalar endpoint still performs
uncounted conversion of function-valued gates to truth tables, including the
`code.map lowerGate` traversal. It also does
not yet implement the adaptive discovery and projection builder in a uniform
machine, so it is not the requested complete construction runtime theorem.

## Reading and extending the same machine store

[GodMoveMarkedAppendMachine.lean](GodMoveMarkedAppendMachine.lean) uses the
reader's DIndex frame: triple-cell data units, a separator, a terminated unary
address, then scratch cells and arbitrary later workspace.

The fixed 88-state `appendM bit` shifts the address through a three-bit carry
and appends `bit` to the data. It takes `3*bits.length + 2*address + 7` steps,
consumes three reserved cells, preserves the address and later workspace, and
returns the head to zero. Its clock is at most the supplied frame length.

The uniform 222-state `copyM` first runs the restoring reader, carries its
actual answer in finite control, and then appends that answer. Its clock is
at most `101*(L+1)^2`. `copyM_run` proves exact tape equality, including the
preserved workspace, and out-of-range addresses append false. Reserved-pool
theorems show precisely how repeated operations consume available scratch.

These are transition counts in the production `ComposableMachine` model,
including its existing reset-to-zero move. No input-length-dependent control
table or externally supplied answer is used. Address preparation and updates,
scratch allocation, program decoding/control and whole-builder composition
still require implementation and cost proofs.

## SAT rank requirement

The new compiler and machine results supply no estimate of SAT derivative
rank. The existing [runtime frontier](GodMoveSATRuntimeFrontier.lean) proves
that the requested polynomial-clock rank estimate is equivalent to the
repository's `SAT_not_in_P` target. Its reverse direction is vacuous under
separation; it is not an independent runtime-to-rank proof. The preceding
[local-clock obstruction](GodMoveSATLocalClockObstruction.lean) also rules out
using an individual easy SAT run to bound the entire canonical source rank.

## Validation

All seven new modules passed individual checks. A fresh rebuild of both
endpoints and their complete GodMove import closure then passed with Lean
4.28.0:

- 61 audit modules, including all seven new modules;
- 591 printed axiom checks, including 95 in the new modules;
- 462 files in the matched source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked Lean source predates its final log. The new modules contain no
`sorry`, `admit`, custom axioms or `native_decide`. Thirteen closed kernel
examples in the new modules cover division, signed arithmetic, layouts,
negative reciprocal, zero reciprocal and full signed multiplication.
Independent review checked the counted call paths, model limits and machine
contract. The full 170-module default audit was not rerun.

Results: `/home/darre/godmove-audit-20260912/generated-runtime-checks/results.json`.

Reproduce the focused check:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --module GodMoveGeneratedScalarBackend \
  --module GodMoveMarkedAppendMachine \
  --log-dir /home/darre/godmove-audit-20260912/generated-runtime-checks
```
