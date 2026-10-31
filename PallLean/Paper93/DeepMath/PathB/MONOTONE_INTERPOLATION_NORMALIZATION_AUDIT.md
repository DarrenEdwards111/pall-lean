# Monotone/interpolation normalization: second breakthrough audit

## Question

Can clause monotonicity supply the missing universal normalization theorem?

UNSAT is monotone under adding clauses: once a CNF is unsatisfiable, adding clauses cannot make it
satisfiable.  Unlike residual counting, this gives a genuine semantic direction.  Monotone circuit
lower bounds and monotone feasible interpolation can then prove exponential lower bounds in several
restricted circuit and proof systems.

The hoped-for bridge is:

```text
polynomial-time SAT decider
    -> polynomial-size local computation/refutation trace
    -> polynomial-size monotone interpolant
    -> contradiction with a monotone lower bound.
```

This note audits both arrows before adding a Lean interface.  The verdict is negative for arbitrary
SAT deciders.  The first arrow is valid.  The second is the entire missing theorem and does not follow
from locality, correctness, or monotonicity of the decided predicate.

## Candidate A: monotonize the SAT circuit directly

A time-`T` decider can be unrolled into an ordinary Boolean circuit of size polynomial in `T`.  On a
clause-incidence encoding, the UNSAT function is monotone.  It is tempting to replace the ordinary
circuit by a monotone one and then apply a monotone lower bound.

That replacement is not a semantics-preserving normal form theorem.  Negations may create an
exponential advantage even when the computed function itself is monotone.  Tardos constructed a
monotone Boolean function with polynomial ordinary circuit complexity and exponential monotone
circuit complexity.  Therefore no theorem of the form

```text
every small ordinary circuit computing a monotone function
has a polynomially related monotone circuit
```

can hold.

This is a direct failure of universal normalization, not merely an absence of a known proof.  The
monotonicity of UNSAT constrains input/output behaviour; it does not constrain the signs of the
intermediate gates used by an arbitrary algorithm.

Primary references:

* A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean functions* (1985),
  https://www.mathnet.ru/eng/dan9192
* E. Tardos, *The gap between monotone and non-monotone circuit complexity is exponential* (1988),
  https://www.cs.cornell.edu/~eva/Gap.Between.Monotone.NonMonotone.Circuit.Complexity.is.Exponential.pdf

## Candidate B: turn rejecting runs into proofs, then interpolate

For a deterministic SAT decider `D`, an UNSAT computation can be packaged as a polynomially checkable
trace.  If `D` runs in polynomial time, every UNSAT formula has a polynomial-size `D`-trace.  In
Cook--Reckhow language this yields a polynomially bounded proof/certificate system tailored to `D`.

For proof systems with monotone feasible interpolation, a short refutation of a split contradiction
`A(x,y) AND B(x,z)` yields a small monotone circuit separating the corresponding disjoint sets.  A hard
CLIQUE/COLORING-style separator then gives a proof-size lower bound.  This is a real and successful
method for restricted proof systems such as resolution.

But an arbitrary computation-trace proof system need not have monotone feasible interpolation.  The
trace verifier may use negations, arbitrary auxiliary gates, global recomputation, and a representation
tailored to `D`.  Tseitin locality does not repair this: every ordinary circuit, including one exploiting
the Tardos monotone/non-monotone gap, has a polynomial-size local Tseitin encoding.  Local constraints
therefore do not imply a small monotone interpolant.

Equivalently, adding

```text
every polynomial-time SAT-decider trace system has polynomial monotone feasible interpolation
```

would be the load-bearing lower-bound theorem, not routine normalization.  Combined with known
monotone separator lower bounds it would rule out a polynomial-time SAT decider.  It cannot be assumed
from the existence or local checkability of the trace.

This also explains why resolution lower bounds do not automatically lower-bound arbitrary SAT
algorithms.  Resolution has an interpolation theorem because of its inference rules.  A general
algorithm is not forced to emit, simulate, or be efficiently translated into resolution (or any other
fixed interpolating proof system).

Primary references:

* S. Cook and R. Reckhow, *The relative efficiency of propositional proof systems* (1979),
  https://doi.org/10.2307/2273702
* J. Krajicek, *Interpolation by a game* (1997),
  https://eccc.weizmann.ac.il/report/1997/015/
* P. Pudlak, *Lower bounds for resolution and cutting plane proofs and monotone computations*,
  https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/lower-bounds-for-resolution-and-cutting-plane-proofs-and-monotone-computations/3AE7865B0EF6CB26B4CF7AB8C15E0DB4

## The SAT-specific escape hatch

The Tardos gap kills a *general* monotonization theorem.  It does not logically exclude a theorem
specialized to a particular encoding of SAT.  A surviving route would have to prove all of the
following:

1. every polynomial-time SAT decider can be transformed with polynomial overhead into a representation
   that respects clause addition;
2. the transformation controls intermediate negations strongly enough to yield a small monotone
   circuit or monotone interpolant;
3. the target SAT family is hard in exactly that monotone representation;
4. the transformation is not defeated by recomputation, auxiliary variables, or a different SAT
   encoding.

This is much stronger than observing that UNSAT itself is monotone.  It is a SAT-specific
order-preserving normalization theorem for arbitrary algorithms.  No such theorem is supplied by the
current corpus or by the standard circuit-unrolling/Cook--Levin construction.

There is also an immediate falsification test for any proposed version: compose it with an
order-preserving reduction from a monotone function known to have a large monotone/ordinary gap.  If
the reduction and normalization together produced a small monotone circuit for that function, at
least one claimed preservation property is false.

## Verdict

The second breakthrough candidate does not survive in its universal form:

1. UNSAT monotonicity is genuine semantic structure;
2. ordinary polynomial-time computation normalizes only to ordinary circuits/local traces;
3. ordinary-to-monotone normalization is unconditionally false in general;
4. trace-to-monotone-interpolant normalization holds for restricted proof systems because of their
   rules, not for arbitrary deciders because of SAT correctness;
5. asserting it for every SAT decider would insert the desired separation at the bridge.

No Lean theorem should package universal monotone normalization or universal feasible interpolation as
an available bridge.

## Refined next target

The remaining research target is narrower than the previous `restricted representation class C`
slogan:

```text
Find a SAT encoding and an order-sensitive operational invariant I such that

  (a) I is preserved under arbitrary polynomial-time implementation changes,
  (b) small time implies small I without monotonizing every gate, and
  (c) a known monotone/interpolation lower bound forces large I.
```

Condition (a) is the danger point.  If `I` observes gate signs or a chosen proof language, it is
representation-dependent.  If `I` forgets the implementation and becomes fully semantic, condition
(c) is again a general lower bound for the SAT function.  A successor must exhibit an actual invariant
that escapes this dichotomy before formalization.
