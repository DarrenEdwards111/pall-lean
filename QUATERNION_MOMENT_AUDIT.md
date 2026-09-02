# P vs NP “Quaternion Moment” Audit

**Date:** 2026-09-02
**Status:** one candidate family isolated and falsified; one narrower research target survives.  This is not a proof of `P ≠ NP`.

## 1. The proposed change of language

The most literal implementation of the Hamilton analogy is to replace scalar
Möbius mass/rank by an **operator-valued interaction object**.  Given a search
state `s`, let `R(i,b)` mean “restrict variable `i` to bit `b` and simplify”.
The tempting invariant is a commutator/holonomy quantity

```text
H(i,j;b,c) = R(i,b)R(j,c) - R(j,c)R(i,b).
```

Independent contradictory unit-pairs appear separable, so one hopes their
operators commute, while globally coupled SAT instances create non-zero
holonomy.  This is the cleanest genuinely noncommutative version of the
“quaternion moment”.

## 2. Exact result: semantic restriction is always flat

For distinct variables `i ≠ j`, overwriting coordinate `i` and overwriting
coordinate `j` commute.  Therefore, for **every** Boolean function—not just easy
instances—semantic restrictions commute:

```text
f|x_i=b|x_j=c = f|x_j=c|x_i=b.
```

This has now been machine-checked in
`ComputationalDepthRestrictionCommutatorNoGo.lean` as
`restrictAt_comm` with no custom axioms.  Hence the literal semantic
commutator is identically zero on unit-pairs, XOR-SAT, and general 3SAT alike.
It cannot separate them.

## 3. Why solver-state noncommutativity does not fix it

One can instead define `R(i,b)` on a solver's internal state: learned clauses,
pivot order, cache, proof log, or compiled tableau.  Such updates need not
commute.  But then the quantity is representation-dependent and faces three
countertests:

1. **Unit-pair test.** A deliberately awkward polynomial-time solver can make
   independent unit-pairs look highly noncommutative merely by changing its
   bookkeeping order.
2. **XOR/Tseitin test.** Gaussian-elimination pivot and row operations can be
   noncommutative on globally coupled expander systems, yet XOR-SAT is in `P`.
3. **Canonicalization test.** Minimizing holonomy over all equivalent solver
   representations asks whether *some* polynomial computation removes it.  The
   universal minimization is the original algorithmic lower-bound problem in
   disguise.

So the operator idea has a precise trilemma:

```text
semantic operators       => commute identically (zero invariant)
implementation operators => can be large on easy P computations
minimum over algorithms  => separation-strength universal quantifier
```

Noncommutativity alone is therefore not the missing invariant.

## 4. What survives: quotient obstruction, not raw interaction

The useful distinction exposed by the counterexamples is not “local versus
global” and not “commuting versus noncommuting”.  It is whether interaction can
be eliminated by a **known algebraic quotient**:

- unit-pairs: component decomposition;
- 2SAT: implication-graph/SCC quotient;
- Horn-SAT: closure under forward chaining;
- XOR/Tseitin: affine quotient by Gaussian elimination;
- bounded-treewidth SAT: separator/dynamic-programming quotient.

General SAT has no known universal polynomial quotient, but proving that none
exists is exactly the hard part.  The honest surviving target is therefore:

> Find an explicit SAT family and a narrowly specified quotient class `Q`
> for which every `Q`-quotient leaves super-polynomial residual
> non-mergeability, while every computation in a correspondingly restricted
> algorithmic class induces a polynomial `Q`-quotient.

This can yield a **restricted lower bound** without circularly quantifying over
all polynomial-time algorithms.  Only after such calibrations work in several
strictly stronger classes would a general machine-completeness bridge be worth
stating.

## 5. Barrier filter

Any replacement candidate must pass all of these before being connected to the
main theorem:

| Filter | Required outcome |
|---|---|
| Unit-pairs / 2SAT / Horn-SAT | polynomial after their canonical quotient |
| XOR/Tseitin | polynomial after affine elimination, even on expanders |
| Trivial Cook–Levin tableau | compilation scaffolding contributes zero or polynomial cost |
| Randomized bookkeeping | invariant unchanged by harmless solver-state encodings |
| Natural proofs | hardness property is non-large or non-constructive |
| Relativization/algebrization | claimed general bridge must explicitly be non-relativizing and non-algebrizing |
| Scale | lower bound must be super-polynomial in the original input length |

The last two conditions are compulsory: P versus NP requires techniques beyond
relativization and algebrization, while a constructive large truth-table
property encounters the natural-proofs barrier.

## 6. Research decision

**Rejected:** raw Möbius mass; raw compiled SPDP rank; semantic restriction
commutators; arbitrary solver-state holonomy; “minimum over all algorithms”.

**Retained:** quotient-relative residual non-mergeability for explicitly
restricted algorithm classes, beginning with a class strictly beyond the
already-closed `AC⁰[p]` calibration.  This is an honest lower-bound programme,
not a completed `P ≠ NP` proof.

The next concrete theorem should have the restricted form

```text
small solver in class C
  ⇒ polynomial quotient in Q
  ⇒ low residual non-mergeability,

explicit SAT family
  ⇒ high residual non-mergeability under every quotient in Q,

therefore SAT ∉ C.
```

The forbidden leap is replacing `C` by all polynomial-time machines without an
independently proved machine-to-quotient theorem.

## 7. Capstone result: the first restricted version already exists

The repository audit found that the proposed restricted quotient programme was
already formalized under the **crossing-state** vocabulary:

- `CrossingStateModel.subfunctionCount_le_width` proves that every computation
  whose left-side influence factors through a finite state quotient has at most
  that many residual subfunctions.
- `crossing_width_ge_exponential` gives a genuine exponential lower bound for
  equality in this restricted model.
- `crossing_bottleneck_must_blow_up` proves that the naive extension to general
  efficient computation is false: the polynomial-time storage-access function
  already forces exponentially many crossing residuals.

These results and `restrictAt_comm` are now assembled in
`ComputationalDepthQuaternionMomentCapstone.lean`.  The capstone is
`sorry`-free and has no custom axioms.  It establishes the exact three-part
frontier:

```text
semantic noncommutativity      = flat (dead)
finite crossing quotient       = valid restricted lower-bound method
small quotient for all of P    = false for this quotient notion
```

Therefore the next general candidate cannot merely count residual functions
across a fixed cut.  It must allow efficient random access/re-reading (so it
compresses storage access) while still charging an explicit NP-complete family.
Finding and proving such a **multi-access, reuse-aware** invariant remains the
open mathematical step.
## Sources used for the barrier check

- S. Aaronson and A. Wigderson, *Algebrization: A New Barrier in Complexity Theory*, ECCC TR08-005.
- A. Atserias and M. L. Bonet, *On the Automatizability of Resolution and Related Propositional Proof Systems*, ECCC TR02-010.
- S. Aaronson, *P =? NP*, ECCC TR17-004 (survey and barrier map).
