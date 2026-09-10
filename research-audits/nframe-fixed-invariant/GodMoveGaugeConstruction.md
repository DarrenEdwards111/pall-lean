# Explicit sampled gauges and SAT reductions

This continuation replaces an arbitrary chosen complementary subspace with an
explicit projection formula built from supplied Boolean samples and a finite
inverse matrix. It provides an executable evaluator using the original circuit
wires and proves that small separating sample lists always exist.

It also identifies the missing algorithmic work precisely: constructing
suitable separating samples already supplies a SAT solver. Small-list
existence and a finite reconstruction formula do not prove efficient discovery.
**No efficient general gauge constructor or superpolynomial SAT lower bound
is established.** The prior [unrestricted-minimizer obstruction](GodMoveProductionConnection.md)
continues to apply; no production action or admissibility definition was changed.

## Projection from explicit finite data

`GodMoveSampledWireGauge.lean` defines `SampleCertificate n r`. Its supplied
data are basis polynomials `b_i`, Boolean assignments `a_j`, and rational
weights `D_ij`, together with the finite matrix identity

    sum_j D_ij * b_k(a_j) = delta_ik.

In matrix notation, with `A_jk = b_k(a_j)`, this is `D*A = I`. The identity
derives linear independence of the basis; independence and a rank bound are
not additional hypotheses.

The projection is defined directly by

    Pi(p) = sum_i (sum_j D_ij * p(a_j)) * b_i.

Lean proves that its range is exactly the supplied basis span, its rank is
exactly `r`, it is idempotent, and it fixes every polynomial in that span.
This creates an actual production `CandidateGauge`. It also proves
`Pi(normalize p) = Pi(p)`, since Boolean evaluations respect normalization.

To realize the actual computed-wire space, the certificate must additionally
establish that its basis spans that entire space. The code states this
equality explicitly. Finite matrix duality alone checks independence and
reconstruction on the supplied basis; it does not prove that every other
wire belongs to that basis span.

## Executable reconstruction from existing circuit wires

The executable rational functions `sampleCoefficients` and `reconstructValue`
implement the displayed finite matrix-vector arithmetic. Given all sample
values of `p` and basis values at the requested point, the expression uses
`r*r+r` rational multiplications and finite sums.

`GodMoveWireSampleCertificate.lean` adds a `WireCertificate`: each basis
polynomial is explicitly identified with a normalized wire at a valid index
in the original circuit. `reconstructFromCircuit` runs that Boolean circuit
once at the requested Boolean point, reads the selected wire bits, and uses
them in the rational reconstruction. `eval_projection_from_circuit` proves
that the result equals evaluation of the exact production projection.

The numeric program uses wire references and finite rational data; it does
not expand its basis or output polynomials. The caller must supply the input
polynomial's sample values. For a Boolean circuit target at Boolean samples,
those values follow from ordinary circuit evaluation. Obtaining arbitrary
sample values is not declared free.

This establishes the numeric reconstruction identity, not a bit-level
polynomial-time compiler theorem. The rational weights in the general
certificate have no proved bit-length bound here. No efficient basis/sample
selection, global spanning check, arbitrary off-cube normalized-polynomial
evaluator, or bounded-cost geometric trajectory is hidden inside the claim.

## Small sample lists exist

`GodMoveSamplingBarrier.SeparatesWires c samples` states that any polynomial
in the computed-wire span vanishing at every listed Boolean assignment must
be zero. It is a semantic property of the whole space.

`GodMoveSmallSeparatingSamples.lean` proves

    exists samples,
      samples.length <= wireRank(c)
      and SeparatesWires(c,samples).

Since `wireRank(c) <= length(c)`, at most one sample per circuit gate is
needed. The proof restricts Boolean evaluation functionals to the wire space,
selects a basis from their span, and chooses an assignment for each selected
functional. Every polynomial in the wire space is multilinear, so vanishing
at all Boolean assignments forces it to be zero.

The proof uses classical basis selection and choice. It bounds the number of
necessary samples, not the time required to locate them. It also does not
construct a complete wire-index/inverse-matrix certificate with bounded
rational serialization; that is a separate deliverable.

## Finding those samples already solves SAT

The normalized circuit target belongs to its wire space. A separating list
therefore hits the accepting set of the circuit whenever that set is nonempty.
`GodMoveSamplingBarrier.lean` proves this for every circuit and then applies
it to the direct fixed-CNF verifier:

    Satisfiable(phi)
      iff samples.any(output(verifierCircuit n phi)) = true.

The sample list may depend on the entire circuit or formula. The proof
does not require a universal, formula-independent hitting set. The condition
`VariablesBelow n phi` ensures that all occurring variable indices are present.

`GodMoveWireSampleCertificate.certificate_decides_SAT` proves the same result
for the samples in a supplied full wire-space certificate. Thus complete
certificate discovery must also supply a satisfying sample whenever one exists.

`GodMoveSampledSAT.lean` makes this reduction executable. It derives the
assignment arity from the existing faithful formula encoding:

    n = 3*L*L + 3,    L = length(encodeFormula' phi).

All occurring variables lie below that bound. The program takes a sample
selector as an explicit parameter, evaluates the direct verifier on its
returned assignments, and accepts if any succeeds. Given a selector satisfying
`SeparatesWires`, Lean proves exact correctness for satisfiability. Its
decoder-based word version agrees with the repository's `SATLang` on every word.

If the returned sample count is bounded by `C*(n+gates+1)^d`, the file also
proves polynomial sample-count and actual sample-bit-storage bounds in `L`:

    count <= (C*4^d)*(L+1)^(2*d)
    bits  <= (3*C*4^d)*(L+1)^(2*d+2).

These size bounds are measured against faithful formula encoding length.
No additional size theorem relating arbitrary malformed decoder inputs to
their re-encodings is claimed.

A polynomial-time selector with polynomial output size would therefore give
a polynomial-time SAT algorithm by the ordinary evaluation of its samples.
The Lean development proves the executable correctness reduction and size
bounds; it does not construct that selector or formalize its runtime as a
machine. This identifies the unresolved work, not an unconditional impossibility
of a polynomial-time algorithm.

## Exact rank computation

`GodMoveRankIncrementSAT.lean` gives a separate concrete reduction that does
not depend on a sample-selection method. Starting with a nonempty Boolean
circuit computing `f(x)`, it introduces two fresh inputs `y,z`. After renaming
the original input indices, it appends the wires

    y; z; f(x) AND y; (f(x) AND y) AND z.

Let `prefix` omit the last gate and `extension` include it. The two circuits
have respectively `s+3` and `s+4` gates. Lean proves

    wireRank(prefix) < wireRank(extension)
      iff exists x, f(x) = true.

If there is an accepting input, the rank increases by exactly one. If there
is no accepting input, it stays equal. The proof uses the linear functional
formed from the four Boolean evaluations at `(y,z)=(1,1),(1,0),(0,1),(0,0)`.
Their alternating sum annihilates every prefix wire but evaluates the final
wire to one at an accepting `x`. With no accepting input, that final normalized
wire is zero instead.

For the direct verifier of a CNF, this gives

    Satisfiable(phi)
      iff wireRank(prefix(verifierCircuit n phi))
            < wireRank(extension(verifierCircuit n phi)).

The extended circuit has at most `length(encodeFormula' phi)+4` gates. The
transformation contains no SAT test or assignment enumeration.
`rankComparisonSAT` is an executable program with an exact-rank subroutine
supplied as a parameter; `rankComparisonSAT_correct` proves its SAT correctness.
The assignment arity is again the existing polynomial encoding bound, with
two fresh controls added by the transformation.

`GodMoveWireSampleCertificate.certificate_dimensions_decide_SAT` connects
this directly to the sampled gauge construction: complete certificates for
the two circuits have explicit dimensions `r,t`, and the formula is satisfiable
exactly when `r<t`. Thus finding those exact certificates already resolves SAT
even if only their dimensions are used.

The claim is about **exact** wire rank and certificates whose range equals
the wire space. It does not say that any larger wire-preserving projection
reveals exact rank, or that a generic implicit projection representation makes
its dimension efficiently available. No impossibility of an efficient
exact-rank algorithm is deduced without an additional complexity assumption.

## What remains

The projection can now be written explicitly from finite supplied data and
evaluated through circuit-wire references. Small separating sample lists have
a proved existence bound. The missing step is an efficient uniform method to
find the required data and establish its full semantic spanning property.

The SAT reductions explain why this step cannot be treated as routine linear
algebra on an already available small matrix: discovering the matrix's
correct samples and basis must capture the circuit's behavior over its whole
Boolean input domain. No assumption that SAT is easy or hard has been added.

The requested superpolynomial lower bound remains unproved. The existing
constant-rank obstruction for unrestricted production minimizers is not
removed by changing how a particular non-minimizing gauge is represented.

## Verification

Run the complete focused suite with:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py
```

Use `--dependency-checkout PATH` for source-matched cached dependencies and
`--log-dir PATH` for persistent per-file logs and `results.json`.

The combined 10 September 2026 run passed all **33 focused files** with Lean
4.28.0. Their **283 printed axiom checks** used only subsets of `propext`,
`Classical.choice`, and `Quot.sound`; the focused files emitted no warnings.
The six new Lean files contain no proof placeholders or custom axioms.

The required dependency targets built successfully. The checked import
closure contained 447 files, with imported PallLean sources and dependency
configuration byte-identical to the cache checkout. Existing dependency
linter warnings are separate from the focused sources. This validation is
the focused suite plus required dependencies, not every repository target.
