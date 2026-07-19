# Single-run restriction compression: falsification audit

## Question

Can a polynomial-time SAT decider's computation on one formula be compressed into a
polynomial-size object that determines the SAT answers of exponentially many restrictions of
that formula, so that residual richness forces a time lower bound?

This note audits that proposal before any Lean interface is added. The conclusion is negative
for the naive statement: depending on what the decoder may do, the proposal is either trivial,
false from correctness alone, or exactly a general circuit lower bound.

## Semantic setup

Fix a CNF family `Phi_m(z,y)`, where `z` selects a restriction/residual instance and `y` is the
remaining witness block. Its residual SAT function is

```text
R_Phi(z) = 1  iff  exists y, Phi_m(z,y) = 1.
```

Thus `R_Phi` is an NP/poly Boolean-function family. A claimed SAT decider `D` computes each bit
`R_Phi(z)` by running on the encoded restricted formula `Phi_m|z`.

A proposed sketch consists of an object `S(D,Phi)` and a decoder `A` satisfying

```text
A(S(D,Phi), z) = R_Phi(z)  for every z.
```

The proposal has three materially different readings.

## Case 1: unrestricted decoder -- trivial compression

If `A` may perform unrestricted computation, take

```text
S(D,Phi) = (code(D), Phi).
```

On query `z`, the decoder constructs `Phi|z` and reruns `D`. The sketch is polynomial-size even
when `R_Phi` has exponentially many distinct residual behaviours. Therefore residual count does
not lower-bound unrestricted description size.

This is the same capacity wall already visible in
`ComputationalDepthSubfunctionCapacityWall.lean`: one semantic object may compactly specify a
function with exponentially many residuals.

## Case 2: polynomial-size circuit decoder -- the general circuit frontier

If `A(S,-)` must be a polynomial-size circuit, a polynomial-time `D` already supplies such a
circuit by the standard time-to-circuit unrolling of

```text
z |-> D(encode(Phi|z)).
```

Consequently, proving that an explicit residual family `R_Phi` has no polynomial-size decoder is
a general circuit lower bound for an NP/poly family. For a universal NP-complete family, this is
the `NP not subset P/poly` frontier, stronger than `P != NP`.

The compression formulation has not weakened the missing theorem; it has renamed it.

## Case 3: decoder from one actual run -- not forced by correctness

Suppose `S(D,Phi)` must be extracted from the trace of `D` on the single master input `Phi`.
Correctness on `Phi` constrains one output bit. It does not force that trace to encode the answers
on the different inputs `Phi|z`.

The corpus already contains two exact warnings:

* `ComputationalDepthPvsNPResidualObserverNoGo.lean`: SAT self-reduction succeeds with a Boolean
  prefix oracle. It adaptively follows one path and does not require simultaneous distinction of
  all residual branches.
* `ComputationalDepthPvsNPDynamicTraceGeometryNoGo.lean`: `DecidesSAT` alone cannot make an
  arbitrary polynomial boundary sound on a residual fooling family; the constant projection is a
  counterexample.

To recover all residual answers, one may run `D` separately on all restrictions, but that creates
an exponential-size multi-run transcript. The P-side compression is then lost.

## Why OR-compression does not rescue the proposal

For restrictions of one formula,

```text
SAT(Phi) = OR_z SAT(Phi|z),
```

but `Phi` itself is already a short representation of this OR. The restricted instances are
highly correlated; they are not arbitrary SAT instances. Hence their exponential number does not
imply incompressibility.

Known instance-compression lower bounds concern substantially stronger compression of arbitrary
collections/instances. Fortnow--Santhanam show that the relevant OR-compression for NP-complete
problems would imply `NP subset coNP/poly`; Drucker extends limits to randomized/quantum
compression; Dell--van Melkebeek prove strong sparsification lower bounds for `d`-SAT under a
polynomial-hierarchy collapse assumption. These results reinforce the diagnosis: a useful
arbitrary-instance compression theorem is itself collapse-strength, while the correlated
restriction family is trivially represented by its master formula.

There is an even sharper obstruction. For every polynomial-size Boolean circuit `C(z)`, a
Tseitin-style encoding gives a polynomial-size CNF `Phi_C(z,y)` such that

```text
C(z) = 1  iff  exists y, Phi_C(z,y) = 1.
```

Thus residual SAT functions of polynomial-size master formulas already include all
polynomial-size circuit functions. They may have exponentially many distinct restriction
answers while retaining the master circuit/CNF itself as a polynomial description. Therefore
the number or diversity of residual answers alone cannot establish a lower bound. One must prove
that a particular explicit residual function lacks small circuits, which is already the general
circuit-lower-bound frontier.

Primary references:

* Fortnow and Santhanam, *Infeasibility of Instance Compression and Succinct PCPs for NP*,
  DOI: https://doi.org/10.1145/1374376.1374398
* Drucker, *New Limits to Classical and Quantum Instance Compression*,
  DOI: https://doi.org/10.1109/FOCS.2012.71
* Dell and van Melkebeek, *Satisfiability Allows No Nontrivial Sparsification Unless the
  Polynomial-Time Hierarchy Collapses*, DOI: https://doi.org/10.1145/1806689.1806725

## Falsification verdict

The naive single-run restriction-compression route does not survive:

1. unrestricted decoder: polynomial sketch exists trivially;
2. efficient general decoder: hard side is a general circuit lower bound;
3. actual single-run trace: simultaneous residual decoding is not implied by SAT correctness;
4. all-restrictions multi-run trace: exponential P-side cost;
5. OR of correlated restrictions: already compressed by the master formula.

No Lean theorem should package the naive proposal as a new P-vs-NP bridge.

## Surviving theorem shape

A nontrivial route would require an additional operational normalization theorem:

```text
Every polynomial-time SAT decider can be transformed, with polynomial overhead,
into a solver whose one-run state belongs to a restricted representation class C,
and SAT correctness forces that C-state to answer a hard family of residual queries.
```

Then one would need a lower bound for class `C`.

The normalization theorem is the load-bearing obligation. Without it, the result is only a
restricted-model lower bound. With unrestricted `C`, the lower bound is the general circuit/time
lower bound again. Re-computation and representation changes are the immediate falsification
tests for every proposed `C`.

This exposes a normalization trilemma:

1. If `C` is trace-sensitive, arbitrary recoding, padding, and recomputation defeat universality.
2. If `C` is semantic and admits arbitrary polynomial circuits, the desired hard side is a
   general circuit lower bound.
3. If `C` is genuinely intermediate, the missing universal normalization theorem is itself the
   breakthrough and must be proved before any lower-bound counting begins.

## Next research criterion

Do not select the next proxy by where it lies numerically between space and time. Select it only
if SAT correctness supplies a plausible semantic forcing mechanism on one computation. Before
formalization, require explicit answers to:

1. Why must one run encode information about other restricted inputs?
2. Why can the solver not recompute that information on demand?
3. What normalization puts every polynomial-time solver in the restricted representation class?
4. Does the hard-side theorem already imply a known general circuit lower bound?
5. Is the chosen hard family resistant to algebraic/global shortcuts rather than merely rich in
   residual labels?

Until a candidate passes these checks, the honest result is a restricted-model theorem or a
restatement of the open separation.
