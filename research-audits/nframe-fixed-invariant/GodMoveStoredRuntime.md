# Stored program execution and restoring machine lookup

The scalar backend now has one counted path through operand preparation,
program serialization, decoding, Boolean execution and output collection.
Separate counted compilers generate the actual adder and multiplier programs.
A fixed tape machine performs lookup while restoring its data and address.
The SAT audit also proves an obstruction to bounding the full canonical source
rank by the runtime of an individual easy input.

The complete construction's machine-runtime bound and the requested global
SAT derivative-rank bound remain unproved. These results do not prove separation.

## Preparation and actual code generation

[GodMoveBinaryPackingCost.lean](GodMoveBinaryPackingCost.lean) implements
counted length traversal, append, padding, trimming, reference generation and
successor-based index arithmetic. Their values equal the existing packing and
resizing operations. Preparation constructs the actual operand store and its
references once and takes at most `64*(w+1)` steps, where `w` is the sum of the
four supplied magnitude-word lengths plus one.

The model counts list and unary-index traversal and shares existing natural
values and immutable list tails. It does not identify these counters with
native allocation cost or tape-machine steps.

[GodMoveBinaryMultiplyCompileCost.lean](GodMoveBinaryMultiplyCompileCost.lean)
recursively generates gates using the counted primitives. Its erasure theorems
identify the entire generated program and output references with the existing
verified adder and variable-input multiplier. The counters include repeated
copies of the accumulated gate prefix, lengths, padding, zips and index offsets.

| Compiler | Proved generation counter |
| --- | --- |
| `addBitsCounted`, `k` bit pairs | Exactly `39*k+2` |
| `maskWordCounted`, `w` bits | Exactly `6*w+4` |
| `productBitsCounted`, operand widths `m,w` | At most `128*(m+1)^3*(w+2)` |

The product compiler also has the bound `128*(start+m+w+2)^4`. These are
generation bounds for the adder and multiplier. The full rational compiler
still needs counted division, gcd, signed arithmetic and assembly, and the
scalar endpoint has not yet substituted these counted generators.

## Finite program data and its execution

[GodMoveStoredBooleanProgram.lean](GodMoveStoredBooleanProgram.lean) encodes
all four instruction kinds using two opcode bits, explicit truth-table bits
and terminated unary addresses. A separate flag marks each instruction and
the end of the program. No rational value supplies the output bits.

An address beyond the final possible store is capped at a missing reference.
The evaluator's default-false rule proves this transformation preserves the
whole execution, including forward or invalid references. The capped emitter
visits only the bounded prefix of an address; it never materializes its
potentially enormous uncapped unary encoding. Thus the size theorem needs no
additional well-formedness assumption on the original program.

For input length `I`, initial store length `V` and `G` instructions, write
`B=I+V+G`. The program occupies at most

`G*(2*B+9)+1`

Boolean cells. Encoding and decoding have separate proved traversal bounds.

[GodMoveStoredProgramExecution.lean](GodMoveStoredProgramExecution.lean)
computes the necessary lengths through counted traversals, serializes the
program, decodes that data and executes only the returned instructions.
`executePrepared_value` proves exact agreement with the original evaluator;
the combined traversal bound is

`32*(I+V+G+4)^2`.

The valid-program contract allows any suffix after the program terminator.
`executeEncoded_programBits_append` proves that both result and counter are
independent of subsequent workspace or trailing false padding. This avoids
requiring a machine to distinguish invisible trailing blank cells. No claim
is made that the malformed-stream behavior is already implemented by a tape
machine. Decoder fuel is an explicit bound derived during preparation; its
future machine representation and control still need implementation.

[GodMoveStoredScalarBackend.lean](GodMoveStoredScalarBackend.lean) joins this
path to the actual rational backend and reads the sign and magnitude words
from its returned wire store. It executes the arithmetic circuit once.
`evaluateStored_correct_and_cost` proves canonical rational correctness and

`200000000*(w+1)^6`

traversal steps, including operand preparation, serialization, decoding,
evaluation and output collection. This bound still excludes the full circuit
generator and conversion of its function-valued gates into finite truth tables.

## A restoring lookup in the actual tape-machine model

[GodMoveMarkedReadMachine.lean](GodMoveMarkedReadMachine.lean) defines one
uniform 46-state `ComposableMachine`. Its input uses the existing DIndex
triple-cell data encoding followed by a unary address and arbitrary workspace
suffix. The whole frame has length

`L = 3*bits.length + 2*address + 4 + suffix.length`.

After `100*(L+1)^2` actual machine steps, `readM_run` proves the exact final
configuration: the machine has halted, its answer is `bits.getD address false`,
its head is zero, and its tape is exactly the original input. Lookup can
temporarily mark cells, but the machine restores the entire data, address and
suffix. No in-range assumption is needed.

This discharges a concrete prerequisite for rereading shared wires. It still
uses a different codec from the preceding doubled-frame append machine.
Conversion or a common storage implementation, address preparation and updating,
program decoder, arithmetic/compiler control and their composition into one
uniform machine remain necessary. Neither a length-parametrized finite-control
machine nor an assumed per-step simulation theorem supplies that integration.

## SAT-specific local-runtime obstruction

[GodMoveSATLocalClockObstruction.lean](GodMoveSATLocalClockObstruction.lean)
constructs a two-state extension of any supplied correct SAT decider `M` with
clock `T`. The actual codec decodes every false-headed word as the empty CNF.
The wrapper accepts those words in exactly one step; on other inputs it starts
`M` without modifying the tape or head. Its global correctness is proved with
clock `T(L)+1`.

The wrapper's full canonical decision polynomial and paper source rank are
unchanged. They therefore retain the existing superpolynomial rank lower bound,
even though every designated length has an actual one-step accepting input.
`no_full_source_bound_from_easy_run` rules out an eventual polynomial bound on
that full rank in encoded length plus this one-step local runtime.

The same module proves that restricting the actual source's first coordinate
to false gives the constant polynomial `1`. Thus it asserts no hardness of the
easy face. The global worst-case clock can still be large; this obstruction
neither proves nor refutes the requested global polynomial-clock SAT rank
estimate. No polynomial-time SAT assumption or new rank-bound premise is
inserted into the backend results.

## Validation

All seven new modules passed individual Lean checks. A fresh rebuild of the
four endpoints and their complete GodMove import closure then passed under
Lean 4.28.0:

- 66 audit modules, including all seven new modules;
- 580 printed axiom checks;
- 467 files in the matched source closure;
- zero focused warnings;
- only `propext`, `Classical.choice` and `Quot.sound` in the axiom reports.

Every checked Lean source predates its final log. The new files contain no
`sorry`, `admit`, custom axioms or `native_decide`. Closed kernel evaluations
cover packing, layouts, trimming, generated arithmetic and its counters, all
instruction kinds, invalid references, empty programs and trailing padding.
Independent reviews checked the semantics, counter scope, machine contract,
SAT quantifiers and report. The full 163-module default audit was not rerun.

Reproduce the focused check:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --module GodMoveStoredScalarBackend \
  --module GodMoveBinaryMultiplyCompileCost \
  --module GodMoveMarkedReadMachine \
  --module GodMoveSATLocalClockObstruction \
  --log-dir /home/darre/godmove-audit-20260912/stored-program-runtime-checks
```
