# Computed-wire rank, repaired derivatives, and the remaining separation gap

The subsequent [production connection](GodMoveProductionConnection.md) realizes
this wire rank in the existing gauge type, proves a linear SAT lower bound,
and proves that every unrestricted production minimizer has bounded rank.

This continuation proves an operational upper bound for the span of computed
wires and an exact differentiation identity through Boolean normalization.
It also proves why combining them does not supply the full rank-bounded
connection: the required derivative rows cannot always lie in that wire span.
**The matched SAT lower bound and P versus NP separation remain unproved.**

These results extend the [compact circuit connection](GodMoveCircuitConnection.md).
The computed-wire rank is an auxiliary quantity used to test a possible bridge;
it does not redefine the production N-Frame invariant or establish a relation
to its geometric action.

## An operation-derived rank bound

`GodMoveComputedWireRank.lean` runs the existing gate arithmetization with
polynomial inputs and retains the polynomial emitted by each gate. Define

    wireSpace(c) = span_Q { normalize(p) : p is an emitted wire of c }
    wireRank(c)  = dim_Q wireSpace(c).

These are semantic definitions of the shared circuit's wires. Their expanded
polynomials and a basis of the span need not be efficiently computable.

The file proves:

- `wireRank_le_length`: the rank is at most the number of gates.
- `wireSpace_append_gate` and `wireRank_append_gate_le`: appending a gate
  adjoins one vector and increases dimension by at most one. The update
  evaluates the actual gate on earlier wires, including reuse and rereading.
- `wireSpace_eq_image` and `normalization_does_not_increase_wire_rank`:
  this space is the linear image of the raw wire span, so normalization
  cannot increase **this** dimension.
- `circuitTarget_mem_wireSpace`: the normalized output belongs to the space.

For the actual machine unrolling `circuitFor M L t`, the previously proved
gate bound gives

    wireRank(circuitFor M L t) ≤ K_M * (L+t+1)^4.

Thus a polynomial clock gives polynomial wire rank, both on the symbolic
pinned-query construction and directly on the original encoded-input slices.
The circuit represents all inputs of the supplied length under one clock;
this is not a claim about extracting polynomials from a single concrete run.

The original-input statement also identifies the correct SAT decision target:

    satDecisionTarget L = interpolate(SATFamily L).

Under `Decides M SATLang T`, `actualSATCircuit_target` proves that the normalized
output of `circuitFor M L (T L)` equals this polynomial. Consequently
`satDecisionTarget_mem_actualWireSpace` places it in the clock-bounded wire
space. Here the variables are encoded formula-input bits, as distinct from
the assignment bits of a fixed formula's verifier characteristic.

Output membership supplies no large dimension lower bound. The checked
`output_capture_alone` theorem records that any polynomial belongs to a span
of dimension at most one. The computational restrictions on how a wire span
is built would have to do the work in a lower-bound proof.

## Exact differentiation through the Boolean quotient

Let `N` denote the coefficient normalization imposing `X_i^2 = X_i`, and let
`F_i^b` substitute the Boolean constant `b` for `X_i`. Define raw finite difference

    delta_i(p) = F_i^1(p) - F_i^0(p).

`GodMoveBooleanDifferentiation.lean` proves, for every polynomial and every
derivative list `S`,

    N(delta_S(p)) = partial_S(N(p)).

This includes the empty list and repeated variables. The proof derives the
identity on squarefree monomials, establishes compatibility of Boolean faces
with normalization, and iterates the result. The normalized difference also
satisfies the Boolean product rule with its necessary extra product term:

    D_i(p*q) = N(F_i^0(p)*D_i(q) + F_i^0(q)*D_i(p) + D_i(p)*D_i(q)).

`finiteDifference_row_eq` then proves the exact existing shifted/projected row:

    mlProj(shift * N(delta_S(p)))
      = mlProj(shift * partial_S(N(p))).

Normalization occurs before multiplying by the shift. The file does not
silently replace the repository's coefficient projection with Boolean
normalization of the entire shifted expression.

This repairs the differentiation interface exposed by the `X^3` counterexample.
It does not bound the number or span dimension of all recovered rows, their
joint representation size, or the cost of expanded normalization.

## Why the repaired rows do not give the desired lower-bound transport

`not_all_derivatives_captured` formally rejects the assertion that every
circuit's full strict SPDP space lies in its computed wire space at discrete
blocks, derivative order `floor(log2 n)`, and zero shift.

`not_all_repaired_rows_captured` states the failed combination directly for
the normalized finite-difference rows above. If all of them belonged to the
wire span, their rank would be bounded by the gate count. The already checked
linear-size unit-formula circuits contradict that bound. Repairing the algebra
therefore does not repair the missing rank containment.

These are failures of assertions quantified over **all circuits**. They do
not refute a proposed bound whose hypotheses additionally restrict the circuit
to arise from a globally correct polynomial-time SAT decider. Such a restricted
transport theorem has not been proved here.

## Every fixed CNF verifier target already has a small circuit

`GodMoveDirectVerifierCircuit.lean` constructs a concrete circuit for any
fixed signed CNF: literals are variables or negations, clauses are disjunctions,
and the formula is a conjunction. If `E = |encodeFormula' phi|`, it proves

    length(verifierCircuit n phi) ≤ E
    circuitTarget(verifierCircuit n phi) = verifierCharacteristic n phi.

These results require no SAT decider, correctness assumption, or polynomial
clock. Empty formulas, empty clauses, and variable indices outside the
assignment domain follow the existing default-value semantics. In particular,
the small-circuit phenomenon applies to every fixed CNF assignment predicate,
not only the unit-formula calibration family.

`GodMoveVerifierInvariantBarrier.lean` turns this construction into a precise
barrier. Suppose a natural-valued invariant `I` of the normalized target obeys

    I(circuitTarget c) ≤ C*(n + length(c) + 1)^d

uniformly for all circuits. Then, unconditionally for every `phi,n`,

    I(verifierCharacteristic n phi) ≤ C*(n + E + 1)^d.

`no_targetOnly_verifier_separation` proves that this generic upper bound cannot
coexist with a superpolynomial lower bound on the fixed-CNF targets at the same
input scale. `formulaIndexedInvariant_le_encoded` permits dependence on the
formula too, provided the upper bound applies to every circuit representing
its verifier characteristic.

The barrier is about those quantifiers. It does not rule out quantities
retaining the actual SAT-decider computation, correctness-restricted upper
bounds, or lower bounds for `satDecisionTarget` over formula-input bits.
Assignment verification and existential SAT decision are different predicates.

## Dividing by the easy-product rank cannot rescue the zero-shift measure

`GodMoveZeroShiftRankCeiling.lean` proves for every polynomial `p`, every block
partition `B`, and every strict derivative order `k`,

    mlBlockedSpdpRank B k 0 p ≤ choose(n,k).

At zero shift every row is a scalar multiple of a derivative indexed by a
`k`-subset: admissibility excludes repetitions and derivative commutation
removes order. No multilinearity assumption on `p` is needed.

The easy full product, hence the unit-CNF characteristic, attains this upper
bound exactly for discrete blocks. Dividing by that easy baseline therefore
leaves a ratio at most one for every target. For `k > n` both ranks are zero;
the Lean rational ratio uses its defined `0 / 0 = 0` convention. This conclusion
concerns the stated strict zero-shift rank, not all derivative/shift measures.

## What remains

The positive results now connect actual machine simulation to a rank with a
derived polynomial upper bound and identify its output with the SAT decision
polynomial. They do not show unavoidable superpolynomial growth of that rank.
The former characteristic-SPDP lower bound cannot be transferred by generic
row containment, and the fixed-CNF target cannot support a generic
circuit-bounded separating invariant.

A completed connection would need a lower bound on the same operational
quantity for every correct SAT decider, or a different faithful transport
whose required structure is proved from those computations. No such lower
bound or transport is inserted as an assumption and reported as a construction.

## Reproduction

The focused runner includes these five files after the preceding seventeen:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py
```

Use `--dependency-checkout PATH` to reuse source-matched dependencies and
`--log-dir PATH` to retain logs. The runner verifies the imported PallLean
sources and dependency configuration, builds the required targets, compiles
the focused files in dependency order, and checks printed axiom dependencies.

The combined 10 September 2026 run passed all **22 focused files** under Lean
4.28.0, with no warnings in those files. The **193 printed axiom checks** used
only subsets of `propext`, `Classical.choice`, and `Quot.sound`. All five new
files contain no proof placeholders or custom axioms.

The required dependency targets built successfully. The imported source
closure contained 422 files; imported PallLean sources and dependency
configuration matched the cache checkout byte-for-byte. Existing dependency
linter warnings are separate from the warning-free focused sources. This
validation covers the focused suite and required dependencies, not every
repository target. The previous report records the unrelated archived-module
build failure encountered during that earlier work.
