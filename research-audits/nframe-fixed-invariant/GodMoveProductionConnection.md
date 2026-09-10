# Production gauge connection and a genuine linear SAT lower bound

This continuation constructs an exact algebraic bridge from computed-wire rank
to the existing production gauge and action definitions. It derives a linear
SAT lower bound on that same rank, uniformly over all circuits deciding an
encoded input slice. **It does not prove a superpolynomial SAT lower bound.**

It also proves a stronger obstruction to the proposed variational endpoint:
every unrestricted minimizer of `FullLagrangianFixed` has bounded projection
rank for fixed nonnegative weights with positive rank weight. At unit
rank/barrier weights and nonnegative edge weight, every
minimizer is the zero projection. Thus the requested growing lower bound for
those unrestricted minimizers is false under the current definitions.

No production invariant, action, admissibility predicate, or machine model
was changed. This extends the [previous rank continuation](GodMoveRankConnection.md).

## Exact realization in the production gauge

The production `CandidateGauge N` is an idempotent linear map on
`MvPolynomial (Fin N) Q` with finite-dimensional range. `ObserverGauge N`
adds an independent real coordinate field. These are the types used by
`fullLagrangianFixed`, not newly introduced replacement gauge types.

`GodMoveProductionGaugeBridge.lean` uses a chosen linear complement to project
onto any finite-dimensional subspace. On the actual normalized wire span it
constructs `wireGauge c`, proving

    range((wireGauge c).projection) = wireSpace c
    rank((wireGauge c).projection)  = wireRank c.

The projection fixes every normalized wire and the output. For the actual
unrolled circuit of a globally correct SAT decider it therefore fixes
`satDecisionTarget N`, the decision polynomial over encoded formula-input
bits. This is the decision predicate, not the assignment verifier of a fixed CNF.

The existing operational upper bounds transfer to this exact production rank:

    rank(wireGauge(circuitFor M N t)) ≤ K_M*(N+t+1)^4.

A polynomial clock gives a polynomial bound. Appending one circuit gate
increases the rank by at most one. The coordinates are zero, as the current
type permits, so evaluating the unchanged production action gives exactly

    fullLagrangianFixed(alpha,beta,gamma,G,wireGauge c)
      = beta*r + gamma/(1+r),    r = wireRank c.

At unit rank/barrier weights this is at most `length(c)+1`.

This is an **algebraic** construction using classical choice of a complement.
It does not supply an efficient basis-selection procedure, compact encoding
of the projection, bounded-cost update of its coefficients, or geometric
descent of the gauge. The wire polynomials are symbolic denotations across
an input slice. The circuit's compact representation and size bounds do not
make expansion of those polynomials or construction of their projection free.

## A genuine lower bound on the same operational quantity

`GodMoveComputedWireLowerBound.lean` proves that every essential input of a
circuit's output forces a variable-read gate. That gate emits `X_i`, Boolean
normalization fixes it, and the distinct coordinate polynomials are linearly
independent. Hence, for any circuit computing `f`,

    number of essential inputs of f ≤ wireRank(c).

The repository's `SATFamilyDenseFloor.depSet_card_ge_dense` theorem supplies
actual encoding-and-decoding witnesses showing that every bit from position
22 onward is essential for the exact encoded SAT decision slice. Combining
the results gives

    computes(c, SATFamily N)  ==>  N-22 ≤ wireRank(c).

Here subtraction is natural-number subtraction. The theorem applies to
**every circuit** computing the slice, with no derivative containment,
transport assumption, polynomial clock, or stipulated rank lower bound.

For the constructed production gauge of an actual correct SAT machine, the
combined `actualSAT_gauge_rank_bounds` theorem proves

    N-22 ≤ rank(wireGauge(circuitFor M N (T N)))
         ≤ K_M*(N+T(N)+1)^4.

These bounds are compatible. Essential-input counting is at most `N`, so
this argument cannot yield superpolynomial growth. In the particular unrolled
simulator, all input variables are loaded even for machines deciding trivial
languages; its linear input-loading rank is not additional SAT hardness. The
substantive lower-bound statement is the quantifier over every SAT circuit.

## Exact minimization with an explicit wire-preservation restriction

`GodMoveProductionConnection.lean` states `PreservesComputedWires c g`
explicitly: the gauge fixes every emitted normalized wire. Linear closure
then proves `wireSpace c` is contained in its projection range, and therefore

    wireRank(c) ≤ rank(g).

Since `wireGauge c` has exactly that range, it achieves the minimum rank on
this restricted set. For `alpha >= 0` and unit rank/barrier weights, it also
minimizes the unchanged action on the same set: `r+1/(1+r)` is nondecreasing
for nonnegative `r`, and the chosen zero coordinates have zero edge energy.

This preservation restriction is **additional** to production admissibility.
The result does not claim that the unrestricted variational problem selects
a wire-preserving gauge. It does show precisely how the operational rank
connects to production rank when the actual computation is preserved.

## Unrestricted minimizers cannot carry the requested large rank

`GodMoveProductionMinimizerBarrier.lean` compares any minimizer with the
existing trivial observer gauge. The latter has zero edge energy, rank zero,
and action `gamma`. For `alpha >= 0`, `beta > 0`, and `gamma >= 0`, the other
action terms are nonnegative, so any gauge no more expensive than this
competitor must obey

    beta*rank(g) ≤ gamma
    rank(g) ≤ gamma/beta.

Every global minimizer over the existing unrestricted gauge type satisfies
this bound. With coefficients fixed independently of input length, this is
a uniform constant bound regardless of graph size or SAT semantics.

For `beta=gamma=1`, a positive integer rank would contribute at least one
plus a strictly positive barrier, exceeding the trivial action of one.
Thus **every** minimizer has rank zero. The finite-range field then implies
that its entire projection is zero, so it cannot fix any nonzero polynomial.

The earlier audit showed that the zero gauge is a global minimizer at these
weights. This result strengthens that existence statement to all minimizers,
and supplies the fixed-weight bound for general positive rank weight.

Combining this with the genuine SAT floor proves
`sat_preserving_gauge_not_global_minimum`: for `N >= 23`, no gauge preserving
all computed wires of any correct SAT circuit can simultaneously be an
unrestricted global minimizer at the unit weights.

These statements concern the actual structural action with barrier
`1/(1+rank)`. They do not refute a different analytic log-determinant action,
or a model with separately justified restrictions on its feasible gauges.

## Unit and output preservation alone still permit rank two

`GodMoveUnitOutputGauge.lean` checks the existing stronger
`UnitPreservingAdmissibleGauge` predicate, which excludes the zero projection.
For every polynomial `p`, projection onto `span{1,p}` is an actual admissible
gauge fixing both one and `p`, with rank at most two. This also holds for the
SAT decision polynomial itself.

Thus excluding zero and requiring output preservation alone still cannot
force a large range dimension. Preserving the complete computation imposes
more information than preserving its final output.

| Gauge requirement | Checked conclusion |
| --- | --- |
| Unrestricted global minimizer, fixed nonnegative weights and positive rank weight | Rank at most `gamma/beta`; zero at unit rank/barrier weights |
| Unit-preserving admissibility and one fixed output | A gauge of rank at most two always exists |
| Fix every computed wire of a particular circuit | Rank at least `wireRank(c)`; constructed gauge attains equality |
| Fix every wire of any circuit deciding `SATFamily N` | Rank at least `N-22`, a linear bound |

## Remaining mathematical frontier

The production type/range/action bridge is now proved algebraically, and the
same operational rank has a genuine linear SAT lower bound. Efficient
construction of the projection and an unavoidable **superpolynomial** lower
bound remain unproved. Such a wire-rank lower bound for every SAT circuit would
imply a superpolynomial Boolean circuit-size lower bound, since wire rank is
at most gate count.

The desired lower bound cannot be obtained for the current unrestricted
minimizers: the checked constant upper bound contradicts it. A successful
variational route would need justified operational restrictions or different
analytic definitions, along with proofs of their cost and preservation
properties. Adding a hard-rank requirement to admissibility would not derive
SAT hardness, and no such premise was added here.

## Verification

Run the focused suite with:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py
```

`--dependency-checkout PATH` permits reuse only after imported PallLean sources
and dependency configuration match byte-for-byte. `--log-dir PATH` retains
dependency output, per-file logs, and the machine-readable results.

The combined 10 September 2026 run passed all **27 focused files** with Lean
4.28.0. All **236 printed axiom checks** used only subsets of `propext`,
`Classical.choice`, and `Quot.sound`; the focused files emitted no warnings.
The five new Lean sources contain no proof placeholders or custom axioms.

The required dependency targets also built successfully. The checked source
closure contained 441 files, with imported PallLean sources and dependency
configuration byte-identical to the cache checkout. Existing dependency
linter warnings are separate from the focused sources. This is a focused
verification with required dependencies, not a clean build of every target
in the repository.
