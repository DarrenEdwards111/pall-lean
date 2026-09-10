# Expander protection and positive boundary coordinates for the God-Move

2026-09-10. This continuation connects actual graph expansion and positive
external data to the existing SAT and designated-sheet derivative minors.
The maps preserve those minors with a proved dimension cost. They do not
establish a polynomial SAT-runtime rank bound or separation.

## The constructed connection

Write `a = choose(m,k)`. The unit-query extraction of a faithful SAT-machine
source is the full monomial `P = product_i X_i`. Its `k`-subset derivative
rows have an actual `a` by `a` coefficient identity minor. The designated
production sheet is `Q = product_i (1-X_i+X_i^2)`; its projected derivative
rows also expose that identity after the explicit complementation below.

1. **Protect the labels with actual edge parities.** For a production
   `TseitinGraph G`, a subset `S` labels the parity sum of its vertex
   constraints. The difference of the screens for `S` and `T` is exactly
   the screen of their symmetric difference. If `G.HasExpansion c` and
   `4k <= m`, distinct `k`-subsets have Hamming distance at least `2c`.
   Erasing fewer than `2c` edge coordinates therefore preserves every
   label. Label preservation is proved from the graph, not supplied as a
   field in a geometric certificate.

2. **Use an external matrix with proved positive minors.** Encode each retained
   binary screen as a distinct finite index `i` and set
   `Z[i,j] = (i+1)^j` over the rationals. Every ordered maximal minor of
   this rectangular Vandermonde matrix is strictly positive. Any `a`
   selected rows remain independent when `q >= a` columns are retained.
   Selecting the first `a` columns and inverting their Vandermonde minor
   gives an explicit decoder. The proofs reconstruct arbitrary signed
   row coordinates, as well as nonnegative ones. If `E` is the selected
   encoder and `D` its decoder, the actual square boundary projector
   `Pi = D E` satisfies `Pi^2 = Pi`, `E Pi = E`, and `rank(Pi) = a`.
   Neither the decoder nor this projector is asserted to have only
   nonnegative entries.

3. **Apply that matrix to actual coefficient rows.** The linear map
   `B(p) = sum_S coeff(X^(S-complement),p) * Z[screen(S),-]` sends each
   unit-monomial derivative row to its corresponding external row.
   `sat_boundary_rows_linearIndependent` obtains those rows from actual
   SAT correctness and the existing exact unit-query extraction.
   `decode_minor_combination` reconstructs every coordinate of every
   linear combination of the selected rows.

4. **Carry the designated sheet's derivative data.** For
   `qRow(S) = mlProj(partial_S Q)`, the proved identity is

   ```text
   qRow(S)(1-X) = product_{i in S}(1-2X_i) * product_{i outside S} X_i.
   ```

   For `S,T` of the same size, the coefficient of `X^(T-complement)` in
   this expression is exactly `1` when `S=T` and `0` otherwise. Hence
   `designatedBoundary = B composed with affineComplement` sends the
   actual designated rows to the same independent external rows.
   Separate theorems instantiate the actual production
   `cookLevinStrictFOBTarget` and the sheet extracted from a faithful SAT
   machine. No inverse Gram matrix or choice of an ambient basis is needed.

These are linear maps on derivative-row coefficient spaces. They are not
claimed to preserve SPDP rank under arbitrary variable mixing. The exact
whole-sheet extraction remains the previously proved
[`sheetExtraction`](GodMoveSATDesignatedExtraction.lean). The boundary map
reconstructs selected derivative data: for example, `B(P)=0` when `k>0`,
so `B` itself is not an encoding of every source polynomial.

## What is Ramanujan and what is amplituhedron geometry here?

[`GodMoveRamanujanCalibration.lean`](GodMoveRamanujanCalibration.lean)
links the matrix `A = J-I` to the existing six-edge `K4` endpoint graph,
proves degree three, and computes `A x = -x` for every mean-zero vector.
Consequently its actual squared operator norm on that subspace satisfies
`||Ax||^2 <= 4(3-1)||x||^2`. The same graph has the existing proved
`HasExpansion 2`. The concrete boundary example retains four independent
singleton rows after any three of its six edges are erased.

[`GodMoveExpanderBoundaryExamples.lean`](GodMoveExpanderBoundaryExamples.lean)
also proves the adjacency and Ramanujan bound for the actual complete graph
on every `m >= 3` vertices. Its degree is explicitly `m-1`, so this is a
growing-degree family. The existing complete-graph expansion theorem with
constant one instantiates the boundary construction at all sizes, allowing
one erased edge. The paper window `m = floor(n/3)`, `k = floor(log_2 n)`
satisfies `4k <= m` for `n >= 2^20`, as proved in the same module.

This uses the adjacency-based Ramanujan criterion, rather than an unrelated
scalar spectral field. Infinite families with **fixed** degree require
additional construction; the distinction is explicit in the primary
[Ramanujan-graph reference](https://arxiv.org/abs/1304.4132). No LPS or MSS
family theorem is assumed by these Lean checks.

The positive external matrix and the map `c -> cZ` implement the rational
cone version of the **Grassmannian rank-one** positive map: nonzero
nonnegative input has a strictly positive first output coordinate. This
rank-one parameter is separate from the derivative order `k` above.
After projectivization, this is the moment-curve case of the generalized
amplituhedron construction. The formalization proves the matrix and cone
statements; it does not build the projective quotient, higher Grassmannian
cells, canonical forms, or a physical holographic duality. The geometric
reference defines the map through positive external data and `Y=CZ`:
[Arkani-Hamed and Trnka, *The Amplituhedron*](https://arxiv.org/abs/1312.2007).

## Capacity and the remaining separation obligation

For any linear boundary map preserving all `a` independent rows,
`a <= q`. This is proved both by finite-dimensional linear independence
and, for an encoder/decoder pair, by `E D = I` and matrix rank. At
`k = floor(log_2 m)`, the existing binomial estimates imply that preserving
this entire minor exceeds every fixed polynomial boundary dimension.
At the unchanged paper window, the new example proves
`n^(floor(log_2 n)/4) <= q` with natural-number division in the exponent
for `n >= 2^20` whenever all its selected rows remain independent.
Expansion protects the labels; positivity and the decoder preserve their
linear combinations. Neither result reduces the dimension they occupy.

The full `k`-subset derivative family is admissible for discrete blocks.
For a production coupled partition, only its block-admissible subfamily
contributes to that partition's SPDP rank. The new map preserves every
such subfamily because it preserves the larger family. This does not claim
that all `a` rows are admissible for every partition, nor replace the
existing coupled-partition hard-minor theorem with a larger lower bound.

The definitions enumerate both finite screens and subset labels using
`Fintype.equivFin`; the coefficient sum has `a` terms. These noncomputable
finite definitions supply no polynomial-time discovery or evaluation
algorithm. As elementary size accounting, with `r` retained edge bits
there are `2^r` possible screens, a node is at most `2^r`, and moment
coordinate `j` is at most `2^(r*j)`. Its unsigned binary representation
therefore uses at most `r*j+1` bits. These explanatory bit estimates are
not a proved complexity analysis of the encoder or rational decoder.

The requested runtime-derived polynomial bound remains unproved. The
[preceding runtime audit](GodMoveSATRuntimeBoundAudit.md) shows its precise
polynomial-clock SAT formulation is equivalent to the faithful separation
target. This continuation supplies neither an independent proof of that
bound nor a superpolynomial SAT runtime lower bound. It supplies a concrete
geometric transport of existing derivative information with its cost exposed.

The new square projector acts on rational boundary vectors. No theorem
identifies its matrix rank with a runtime-controlled production N-Frame
action, or proves that legal machine evolution constructs this projector.
That connection still needs a mathematical construction and cost bound.

## Files and verification

| Module | Proved contribution |
| --- | --- |
| [GodMoveExpanderScreen](GodMoveExpanderScreen.lean) | Graph-dependent distance and erasure protection |
| [GodMoveRamanujanCalibration](GodMoveRamanujanCalibration.lean) | Actual K4 adjacency, spectrum, degree and expansion |
| [GodMovePositiveBoundaryMap](GodMovePositiveBoundaryMap.lean) | Positive maximal minors, exact decoding and an idempotent of known rank |
| [GodMoveExpanderPositiveProjection](GodMoveExpanderPositiveProjection.lean) | Actual SAT unit-minor transport and dimension cost |
| [GodMoveDesignatedComplementRows](GodMoveDesignatedComplementRows.lean) | Explicit complemented quadratic-sheet row factorization |
| [GodMoveDesignatedPositiveBoundary](GodMoveDesignatedPositiveBoundary.lean) | Actual designated-sheet and extracted SAT-sheet row transport |
| [GodMoveExpanderBoundaryExamples](GodMoveExpanderBoundaryExamples.lean) | Concrete instances and matching paper-window parameters |

Run the source-matched focused suite from this checkout:

```sh
python3 research-audits/nframe-fixed-invariant/check_godmove_circuit.py \
  --dependency-checkout /home/darre/pall-lean \
  --log-dir /home/darre/godmove-audit-20260910/expander-positive-checks
```

The full focused suite passed under Lean 4.28.0: **90 modules, 712 printed
axiom checks, zero warnings**. The checker matched the 509-file source
closure and dependency configuration before building. Every printed
dependency was among `propext`, `Classical.choice`, and `Quot.sound`.
The seven new modules contribute 63 of those checked declarations. The
machine-readable result is in the command's log directory as `results.json`.
No production definitions are weakened or replaced by the audit modules.
