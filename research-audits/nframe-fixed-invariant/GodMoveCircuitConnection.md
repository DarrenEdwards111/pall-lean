# A compact machine-circuit connection with an explicit rank obstruction

This continuation constructs the circuit-to-characteristic connection and
accounts for the retained representation. It does **not** establish the
runtime-derived bound on the characteristic's SPDP rank or a SAT separation.
In fact, two checked counterexamples rule out generic ways of obtaining that
rank bound from circuit size and Boolean normalization.

## The constructed source

Let `φ` have all its variables below `n`. Write `E = |encodeFormula' φ|`.
The coordinate codec stores each literal's sign as one Boolean bit. Thus the
encoding of `φ` plus the `n` assignment-pinning unit clauses can be represented
once as a list of constants and the variables `a_i`.

`GodMoveSymbolicPinnedInput.lean` proves that this input template evaluates to
the actual faithful encoded pinned query, and that its common length `L` obeys

    L ≤ E + n*(2*n+9).

No assignment list is constructed. The bound uses the actual encoded original
input length and keeps the witness-variable count explicit.

`GodMoveCircuitConnection.lean` specializes the existing `circuitFor M L (T L)`
to this template. The strengthened `circuitFor_output` theorem proves exact
simulation of the supplied clocked run without any halting, language-correctness,
or polynomial-time premise. It follows that, for every assignment `a`,

    output(compactCircuit M T φ n, a) = queryOutput M T φ a.

This is one symbolic circuit for the family of pinned queries, not extraction
from the single execution of `M` on the original unpinned formula.

## Gate, arithmetic, and storage accounting

`GodMoveCircuitRuntimeCost.lean` derives a direct bound from the actual machine
simulation layers. For `q = card M.State`, put

    K_M = (q+2)*(61*q+10) + 5*q+3.

The circuit for input length `L` and supplied clock `t` has at most

    K_M * (L+t+1)^4

gates. The constant depends only on the fixed machine. This is a proved size
bound; no boundary or rank restriction is assumed.

`GodMoveCircuitArithmetization.lean` translates each Boolean gate to a local
arithmetic expression, retaining wire references. A unary/binary gate uses its
two/four local truth-table entries, which is constant work per gate rather than
enumeration of the whole input cube. The resulting DAG has at most 25 expression
nodes and 12 scalar arithmetic operations per Boolean gate. It retains exactly
one wire value per gate; every stored rational wire value on Boolean inputs is
zero or one. Shared and repeated reads are covered by the evaluation proof.

`GodMoveCircuitStorage.lean` removes invalid wire references by substituting
their semantic default `false`, preserving the complete wire sequence and gate
count. It serializes constructor tags, operation truth tables and unary indices.
The decoder has a proved exact circuit-and-suffix roundtrip. For a circuit of
`s` gates and input arity `n`, the serialized length is at most

    (9+2*(n+s))*s+1.

The input arity is supplied to the decoder as an external parameter. It can be
stored separately with polynomial overhead. No opaque function or arbitrary
natural index is counted as a single stored bit.

`GodMoveCircuitPolynomialSize.lean` combines these bounds: under `PolyBounded T`,
there are fixed constants `C,d` bounding the gate count, arithmetic source size,
and serialized bit length by `C*(E+n+1)^d`, uniformly over `φ,n`. These are representation bounds, not
a formal execution-time theorem for a compiler implemented as a
`ComposableMachine`.

## Exact polynomial and row connection

`rawPoly` is the full-ring polynomial denotation of the arithmetic DAG. Its
expanded coefficients are not the retained compact representation.
`GodMoveCircuitNormalization.lean` defines the coefficient map that sends
each monomial exponent to its support indicator, implementing `X_i^r = X_i`
for positive `r`. It proves preservation of Boolean evaluations and
multilinearity, then uses polynomial uniqueness on the Boolean cube to derive
equality with canonical interpolation.

Consequently, without a SAT-correctness premise,

    normalize(rawPoly(compactCircuit M T φ n))
      = machineQueryPolynomial M T φ.

From `Decides M SATLang T` and `VariablesBelow n φ`, the same object equals
`verifierCharacteristic n φ`. Every selected derivative/shift row and both
strict and inclusive SPDP ranks are therefore equal at the same partition and
parameters. Neither polynomial equality nor a rank bridge is assumed.
The explicitly serialized source retains this same characteristic target.

This algebraic normalizer is defined without a Boolean-assignment sum, but
that does not give it polynomial cost on an implicit DAG. Expanding the raw
polynomial or its normal form can be expensive. Exact evaluation of the normal
form away from the Boolean cube is not justified by the constant precision
of Boolean wire values. The earlier exact-counting identity still applies.

## Two proved rank obstructions

`GodMoveCircuitRankObstruction.lean` constructs an actual `CGate` circuit of
exactly `2*n+1` gates for the positive unit CNF `U_n = ∧_i x_i`. Its canonical
characteristic is `∏_i X_i`. With discrete blocks, derivative order
`floor(log₂ n)`, and zero shift, the strict and inclusive ranks have no eventual
polynomial upper bound in input count plus circuit gate count. Thus generic
compact-circuit size cannot bound this characteristic rank polynomially.
This does not disprove an implication with an additional hypothesis that
already posits a globally correct polynomial-time SAT decider.

`GodMoveNormalizationDerivativeObstruction.lean` supplies a different,
constant-size check: the legal shared circuit

    x; x AND x; (x AND x) AND x

arithmetizes to `X^3` and normalizes to `X`. At one variable, derivative order
one and zero shift, the raw strict and inclusive projected ranks are zero,
while the corresponding normalized ranks are positive. The file also proves
that normalization and differentiation do not commute.

Therefore applying a linear map to an existing row space must be distinguished
from differentiating the polynomial after that map. Linearity bounds the former
image dimension; it does not supply the latter rank inequality. Existing
results about normalized images of raw rows cannot replace this missing step.

## Remaining mathematical obligation

The retained source is now compact, has faithful operational semantics, has
explicit storage, and connects exactly to the characteristic as a mathematical
normal form. The chosen characteristic rank still lacks a runtime-derived
polynomial upper bound. The generic gate-count and normalization arguments for
that bound are false at the checked parameters. A separation needs additional
structure or a different invariant, together with its operational upper bound
and an unavoidable superpolynomial lower bound for correct SAT deciders.

No compiler-runtime theorem, efficient expanded normalization, unrestricted
off-cube rational evaluator, or hard-family lower bound was inserted as a
hypothesis and then reported as constructed. No production invariant was changed.

## Reproduction and verification

The final 10 September run passed all **17 focused files**, without warnings
in those files. Their **147 printed axiom checks** use only subsets of
`propext`, `Classical.choice`, and `Quot.sound`. The required dependency targets
also built successfully; their cached output includes pre-existing linter
warnings. The checked import closure contained 417 files, with every imported
PallLean source byte-identical to the dependency checkout. The nine new Lean
files contain no proof placeholders or custom axioms.

The focused checker builds the required dependency targets, compiles the eight
earlier handshake/calibration files and the nine new files in dependency order,
and records exit codes, warnings, and printed axiom dependencies. Run:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py
```

To reuse a different checkout's cache, pass `--dependency-checkout PATH`. The
checker first requires matching toolchain/configuration and byte-identical
imported PallLean sources. `--log-dir PATH` selects a persistent log directory.

The supported toolchain is Lean 4.28.0. The scope is focused checks with cached
dependencies, not a clean rebuild of every repository target. An exploratory
build of the older normalization module exposed pre-existing missing names in
`PallLean/Archive/Paper93Unsafe/Final_P_ne_NP_Wrapper.lean`; the final connection
does not import that module and instead proves the small coefficient map
directly using the existing squarefree basis and Mathlib's polynomial uniqueness
theorem. No archived proof was patched or used to fill the gap.
