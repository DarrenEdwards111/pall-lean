# Exact compact projector construction and its remaining runtime gap

2026-09-10. Continuation of `36d81cba`, incorporating the runtime-barrier
proof from [`75e2b351`](https://github.com/DarrenEdwards111/pall-lean/commit/75e2b351).
The latter was cherry-picked as `683a4571`; its original branch is unchanged.

The new result is an executable compact descriptor of the exact existing
production row projector. Its factors and shared references have a proved
polynomial node count. This removes subset enumeration from constructing
that descriptor. It does **not** reduce the projector's rank or prove
polynomial-time application to a succinct SAT source. Separation remains
unproved.

## The exact kernel and executable descriptor

Write `q_S` for the actual multilinear projected derivatives of the designated
sheet `Q = ∏ᵢ(1-Xᵢ+Xᵢ²)`. The local-operator module proves

```
q_S(X) = ∏_{i∈S}(2X_i-1) · ∏_{i∉S}(1-X_i).
```

The following generating product has an exact coefficient identity:

```
K_k(X,Y) = [z^k] ∏_i ((1-X_i)Y_i + z(2X_i-1))
         = ∑_{|S|=k} q_S(X) Y^(Sᶜ).
```

Here the `Y` variables index input coefficients and the `X` variables are
output variables. Pairing the coefficient of `Y^d` with the coefficient of
`Y^d` in `p(1-Y)` gives precisely the existing `rowProjection m k p`, hence
the projection field of the unchanged production `boundaryGauge m k`.
`descriptor_contract` proves this identity for **every** polynomial `p`.
Neither equality nor rank preservation is an added hypothesis.

The executable constructor stores the two small factors at each coordinate
as arithmetic syntax, and a layered DAG implementing

```
r'_j = A_i r_j + B_i r_(j-1),   r_0 initially 1, all other entries 0.
```

Each layer references previously stored registers; it does not duplicate
expression trees. The selected final register denotes `[z^k]∏(A_i+zB_i)`.
`descriptor_kernel` identifies it with `K_k` above. The expanded subset sum
appears only in the correctness proof, not in syntax generation.

The exact count is

```
descriptor.nodes = 2 + 3m(k+1) + 11m.
```

The `11m` counts the actual stored input expressions: six nodes for each
`(1-X_i)Y_i` and five for each `2X_i-1`. At `k = log₂ m`, Lean proves
`descriptor.nodes ≤ 16(m+1)²`.

This descriptor-cost calibration uses `k = log₂ m`. The dense-output result
below uses `m = n/3` and `k = log₂ n`. The exact descriptor/kernel identities
hold for every `m,k`; these displayed asymptotic specializations use different
windows and are not combined into a source/target rank sandwich.

This is a bound on stored arithmetic syntax, with an executable generator.
It is not a formal machine-clock or bit-complexity bound. Register arrays,
index serialization, and input/output representations require their own
accounting. The parameters here are the number of variables and requested
degree, not the bit length of binary integers naming those parameters.
Evaluating the descriptor into an expanded multivariate polynomial can be
expensive even though constructing the descriptor is small.

## What happens to the dimension and production action

The denoted gauge has **exactly the same** production projection, rank,
idempotence, coordinate map, and action as before. In particular,

```
rank(boundaryGauge m k) = choose(m,k).
```

`no_eventual_polynomial_rank_in_descriptor` proves that at `k = log₂ m`
this rank exceeds every eventual fixed polynomial in the descriptor node
count. The corresponding result also holds for the actual production
action with unit rank/barrier weights, for any supplied production graph
family and edge-energy weight: this gauge's coordinate field is zero.

Thus a compact description coexists with large semantic rank. Counting
description nodes cannot be substituted for the N-Frame rank term. This
does not refute a theorem with additional SAT-specific hypotheses; deriving
such a theorem remains necessary. The compact kernel is independent of a
SAT machine and does not supply the missing computation-dependent bound.

The earlier expander/positive boundary remains useful for preserving the
minor and decoding its coordinates. The compact descriptor above represents
the designated-row projector; it is not an efficient routine emitting all
coordinates of the positive Vandermonde boundary. No smaller faithful
boundary dimension or new amplituhedron theorem is claimed.

## Connecting the supplied runtime barrier to actual machine steps

`75e2b351` proves that superpolynomial boundary growth rules out a polynomial
constructor clock under the numerical premise `q(n) ≤ c*T(n)+b`. Its proof
does not derive that premise from SAT correctness.

The new operational module derives the following bound from legal machine
steps and an exact dense-output serialization contract:

```
q(n) ≤ L(n) + T(L(n)).
```

The clock is measured in encoded input length `L(n)`. If both `L` and `T`
are polynomially bounded, their composition and the initial tape allowance
are polynomial in `n`, contradicting the proved boundary growth.

The concrete specialization uses actual encoded pinned-unit inputs, proves
`L(n) ≤ 23(n+1)²`, and supplies linear independence for the existing
complete-graph positive boundary with `q(n)=choose(n/3,log₂ n)`. The output
contract need only hold for `n ≥ 2²⁰`. Coordinate records must be nonempty;
the length argument alone does not establish a codec's decoding correctness.

This rules out polynomial-time **dense output** of this boundary on those
inputs. SAT correctness does not require that output, and compact syntax
does not satisfy that output contract. The complete-graph specialization
uses growing degree, as in the earlier calibration.

## Proof files

| File | New result |
| --- | --- |
| [GodMoveGaugeLocalOperators.lean](GodMoveGaugeLocalOperators.lean) | Actual local derivative/evaluation maps commute on distinct coordinates; designated row factorization. |
| [GodMoveProjectorKernel.lean](GodMoveProjectorKernel.lean) | Generating product coefficient is the row kernel; contraction equals the production projection. |
| [GodMoveOperatorSubsetDAG.lean](GodMoveOperatorSubsetDAG.lean) | Executable shared-reference program, exact node count, coefficient correctness, kernel-checked numeric examples. |
| [GodMoveCompactGaugeCost.lean](GodMoveCompactGaugeCost.lean) | Quadratic descriptor budget; superpolynomial actual rank/action in that budget. |
| [GodMoveCompactProjector.lean](GodMoveCompactProjector.lean) | Explicit factor syntax and descriptor; counted compact construction denotes the exact production projection. |
| [GodMoveOperationalBoundaryBarrier.lean](GodMoveOperationalBoundaryBarrier.lean) | Actual machine output bound, encoded-length composition, and concrete dense-construction lower bound. |

## Remaining separation requirements

The coefficient contraction is still a mathematical linear map. No
polynomial-time algorithm for applying it to an arbitrary succinct SAT
source is proved here. Nor is it proved that a correct SAT computation
must realize this gauge with its large semantic action.

The SAT-specific runtime-controlled source bound, preservation of the hard
structure by that bounded construction, and the resulting faithful
`SAT_not_in_P` conclusion remain unproved. The earlier equivalence between
the restricted runtime-rank frontier and separation remains an equivalence,
not an independent proof of either side.

## Verification

The full source-matched audit passed on Lean 4.28.0:
103 modules, 522 files in the source closure, 823 printed axiom checks,
and zero warnings. The only reported axioms were `propext`,
`Classical.choice`, and `Quot.sound`. The six new modules account for
45 of those checks; the incorporated runtime-barrier module adds three.
The command was:

```
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/implicit-gauge-checks
```

The checker includes the supplied runtime-barrier module and all six new
modules in dependency order. The local `results.json` records
`all_passed: true`; individual module logs contain the axiom traces.
`git diff --cached --check` also passed. No production definitions were changed.
