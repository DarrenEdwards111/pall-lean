# Constructed projection: finite derivative-preservation obstruction

2026-09-11, based on d79af1aa.

## Question tested

Can the newly constructed exact wire projection supply the missing derivative
preservation merely because it is explicit, fixes the output, and has a
runtime-controlled range? No: even its actual sample/weight construction
fails a concrete six-input test.

The verified tree compiler produces a six-input conjunction with 13 gates.
Its multilinear characteristic is the product of the six variables. At
strict derivative order 2 and shift 0, the 15 distinct squarefree monomials
of degree 4 give at least 15 independent derivative directions. The space
spanned by all computed wires has dimension at most 13.

Consequently no linear map whose range is contained in those wires fixes
the entire second-derivative space. This holds for every choice of samples
or inverse weights. The final theorem instantiates the obstruction with
`GodMoveConstructedProjection.machineCertificate`, constructed using any
supplied globally correct SAT machine. No polynomial-clock premise is used.

This is a finite specialization of the previously known generic wire-space
obstruction, now connected to the new numeric construction. It is not a
new general circuit lower bound. Order 2 equals floor(log2 6); zero shift is
used here, not the final SAT paper's full log/log window.

## What it rules out, and what it does not

It rules out deriving universal derivative preservation from the constructed
projection's inverse identity, output preservation, or efficient weights.
Changing those weights while retaining the same range cannot repair it.

The test circuit is AND, not the supplied SAT machine's own unrolling.
Thus it does NOT refute a SAT-specific preservation theorem. Nor does it
prove that no different admissible gauge can yield the intended separation.
No production N-Frame invariant has been replaced or modified.

## Remaining SAT obligation

`GodMoveSATRuntimeFrontier.satPolynomialClockRankBound_iff_separation`
already proves that the proposed bound for hypothetical polynomial-clock
SAT deciders is equivalent to `SAT_not_in_P`. The reverse implication is
vacuous; this is not an independent route to the estimate.

The construction of the wire gauge applies to arbitrary circuits, even
when SAT is used to discover its samples. That discovery oracle's global
SAT correctness does not turn every circuit being projected into a SAT
decider. A successful argument must exploit the semantics of the SAT
machine's *own* computation and justify preservation/transport of the exact
source rows, without assuming their runtime rank bound.

Neither this audit nor polynomial bit-runtime for weight construction
supplies that argument. The SAT-specific theorem and P != NP remain unproved.

## Verification

The focused Lean check passes all five printed theorem-axiom checks with
only `propext`, `Classical.choice`, and `Quot.sound`, and no warnings.
The module is registered as the final stage of `check_godmove_circuit.py`.
The full source-matched audit passed: 119 modules, 948 printed axiom checks,
538 source-closure files, zero audit-module warnings, standard axioms only.
Results: `/home/darre/godmove-audit-20260911/derivative-preservation-checks/results.json`.
The dependency build may replay existing production linter warnings.
