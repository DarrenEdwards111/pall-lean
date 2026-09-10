# Executable entries and a production N-Frame connection

2026-09-10. This continuation constructs the designated-row projector in
the unchanged production `ObserverGauge` type, derives its exact rank and
action, and proves its variational minimum under explicit row-preservation
constraints. It also replaces full-screen enumeration with executable
binary coding and derives a runtime/action bound for machines that actually
materialize boundary coordinates. It does not prove SAT separation.

## Direct execution of screen labels and boundary entries

[`GodMoveExecutableScreen.lean`](GodMoveExecutableScreen.lean) scans the
indexed edges and computes their actual constraint parities, setting erased
edge bits to zero. The recursive binary encoder is injective and its value
is below `2^E`. The existing expansion proof therefore establishes label
injectivity after erasure without enumerating the type of all possible
screens or using `Fintype.equivFin` to discover their codes.

The instrumented executable `screenRun` returns the same code and has
exactly `E` edge visits and at most `E * |S|` constraint steps. A visit
includes an erasure test and binary append; a constraint step includes an
endpoint-membership query and parity addition. These are proved counters
for the stated primitive operations. They do not include the bit complexity
of integer arithmetic or the cost of accessing an arbitrary supplied graph.

[`GodMoveExecutableBoundary.lean`](GodMoveExecutableBoundary.lean) computes
each positive external entry as `(screenCode(S)+1)^j`. Its magnitude is at
most `2^(E*j)`, so numerical precision still grows with the requested
coordinate. The new code-derived coefficient map sends actual designated
derivative rows to these computed moment rows. Their independence, the
production-sheet specialization, and the faithful SAT-extraction
specialization all follow from the existing coefficient identity.

Kernel-evaluated K4 examples check codes `7,25,42,52`; after erasing its
first three edge coordinates the codes are `0,24,40,48`. Executable entry
checks return `8^3 = 512` and `25^3 = 15625`. The full coefficient maps
still sum over `choose(m,k)` labels. Per-entry execution is not a
polynomial-time algorithm for full source normalization or boundary output.

## An explicit gauge in the existing production type

Let `a = choose(m,k)` and `qRow(S) = mlProj(partial_S Q)` for the actual
quadratic designated product. Its previously proved coefficient duals give
two concrete linear maps:

```text
D(p)[S] = coeff(X^(S-complement), p(1-X))
R(c)    = sum_S c[S] * qRow(S)
D(R(c)) = c
J       = R composed with D.
```

[`GodMoveBoundaryNFrameGauge.lean`](GodMoveBoundaryNFrameGauge.lean) proves
`J^2 = J`, identifies its range exactly, and derives `rank(J) = a`. These
are proofs from the displayed coefficient identity. There is no arbitrary
complement choice or supplied rank-equality field. Attaching the permitted
zero coordinate field constructs `boundaryGauge m k : ObserverGauge m`.
It fixes the actual designated projected derivative rows and those obtained
from the faithful SAT source by the existing exact extraction.

For every polynomial, applying this gauge preserves all the data read by
the preceding positive boundary. The gauge's action is evaluated using the
unchanged `fullLagrangianFixed` and its actual structural barrier:

```text
fullLagrangianFixed α β γ G (boundaryGauge m k)
  = β*a + γ/(1+a).
```

The coordinate energy vanishes because the current production type permits
zero coordinates independently of the projection. This equality does not
establish a nontrivial graph-energy coupling or replace the structural
barrier by an analytic logarithmic determinant. The gauge fixes the retained
row span; it is not asserted to fix the whole nonmultilinear sheet.

## A proved variational minimum, with its domain stated

[`GodMoveConstrainedBoundaryMinimum.lean`](GodMoveConstrainedBoundaryMinimum.lean)
defines the additional audit predicate `PreservesDesignatedRows k g`:
every selected `qRow(S)` is fixed by `g.projection`. For this domain:

- Every gauge has production rank at least `a`, derived from actual row
  independence and the finite-range field of the production type.
- With nonnegative edge weight and unit rank/barrier weights, every gauge
  has action at least `a + 1/(1+a)`. The proof accounts for the decreasing
  barrier term by proving monotonicity of `r + 1/(1+r)` for `r >= 0`.
- The explicit `boundaryGauge` attains that value.
- Every minimizer on this domain has rank exactly `a`.

This does not modify production `AdmissibleGauge`. The earlier theorem
about zero rank for unrestricted unit-weight minimizers remains valid.
For `a>0`, the preservation constraints exclude the zero projection.
They have not been derived as necessary conditions on a runtime-controlled
gauge for every correct SAT decider. The full selected family is admissible
for discrete blocks; other partitions require their appropriate subfamilies.

## A runtime bound derived from actual legal transitions

[`GodMoveBoundaryRuntimeCost.lean`](GodMoveBoundaryRuntimeCost.lean) proves,
for every actual `ComposableMachine`, input `x`, and time `t`:

```text
head(run M t (init M x)) <= t
length(transOut M x t) <= max(length(x), t).
```

The induction covers halting, reset, optional writes, rereads, and cell reuse
using the actual step semantics. If `transOut` equals a dense serialization
of `q` coordinate records and each record is nonempty, then
`q <= max(length(x),t)`. Applying the preserved-minor dimension theorem gives
`a <= length(x)+t`; if `length(x)<a`, the sharper consequence is `a<=t`.

This also yields a connection to the actual production action:

```text
fullLagrangianFixed α 1 1 G (boundaryGauge m k) <= length(x)+t+1,
```

and `<=t+1` in the short-input case. The exact serialization equation and
nonempty-record conditions remain visible in the theorem. No injectivity or
correct decoding of a supplied codec is inferred solely from nonemptiness.
These are bounds for machines materializing the stated boundary, not for
decision-only SAT machines or implicitly represented operators.

`executable_boundaryGauge_action_le_input_add_time` instantiates that bound
with the directly computed screen entries. A separate equality proves that
the same production gauge preserves this executable boundary's data for
every input polynomial. Thus the executable encoding and production action
are connected to the same designated row space.

The updated [`GodMovePositiveBoundaryMap`](GodMovePositiveBoundaryMap.lean)
also proves that at the minimal capacity `q=a`, its square boundary
projector is exactly `I_a`. Such an identity has a short symbolic
description. Its large semantic rank alone cannot imply construction time;
the physical output contract is essential to the bound just proved.

## The remaining connection, checked on an explicit easy circuit

[`GodMoveBoundaryWireGap.lean`](GodMoveBoundaryWireGap.lean) compares both
actual production gauges in the same polynomial ambient space. For the
verified conjunction circuit at `m=16`, `k=4`:

| Quantity or property | Proved value |
| --- | --- |
| Circuit size | 33 gates |
| Computed-wire gauge rank | At most 33 |
| Output fixed by that gauge | The actual full monomial |
| Quadratic extraction from the fixed output | Exactly the designated product |
| Rank needed to fix all designated rows | 1820 |
| Expander-screen window | `4*k <= m` |

Consequently that output-preserving wire gauge cannot preserve all those
derivative rows. Thus fixing the computed output and having an exact
extraction do not supply the missing derivative-preservation implication.
This is a concrete easy-circuit result; it does not refute a theorem using
additional faithful SAT correctness.

The remaining unrestricted obligation is to derive preservation of the
required hard rows by a gauge whose cost is bounded from every hypothetical
polynomial SAT computation, or to justify an equivalent efficient implicit
representation with the same necessary invariant. The new constrained
minimum and explicit-output cost bound do not establish that obligation.
Efficient full construction and SAT separation remain unproved.

## Verification

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/executable-nframe-checks
```

Lean 4.28.0 verified all **96 modules**, with the **515-file source closure**
and dependency configuration matched before building. The full suite passed
with 773 printed axiom checks and zero warnings. The final two integration
theorems were then checked with the complete runtime module again: all 15
of that module's axiom prints passed without warnings. This verifies 775
declarations across the final module versions, using only `propext`,
`Classical.choice`, and `Quot.sound`.

The log directory contains `results.json`,
`GodMoveBoundaryRuntimeCost.final.log`, and `final-validation.json`, which
records the final recheck and its source hash. No production definitions
were altered and no SAT-separation assumption was added.
