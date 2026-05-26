# Observer K^t Frontier

## Status

The observer-boundedness route should be read as a K^t / computational-depth
framing of the remaining P vs NP lower bound, not as a completed separation.

The useful correction is the resource axis.  Width, SPDP rank, communication
rank, holographic boundary complexity, entropy, area, gravitational capacity,
and live-slot capacity are all capacity-style quantities.  They measure how
much information fits or is represented.  A brute-force SAT searcher can keep
only polynomial live state while spending exponential time, so capacity alone
cannot separate P from NP.

The surviving observer invariant must live on the time axis:

```text
tau = computational time budget
K^tau = time-bounded description/search cost
depth = structure that is short in principle but expensive to extract
```

In this reading, a polynomial-time observer is a polynomial-tau observer, and
the SAT lower-bound target is:

```text
No polynomial-tau uniform observer produces satisfying witnesses for SAT.
```

That is the metacomplexity / K^t form of the P vs NP question.

## Lean Anchors

The right-axis object is already present in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthFraming.lean
```

There, `ShallowSearch` names the existence of a uniform polynomial-budget
producer, and `DeepSearch := not ShallowSearch` names the lower-bound target.

The later God-Move capacity branch was useful as an audit.  It shows that
capacity variants do not provide a new separator:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthGodMoveUpperBoundNoGo.lean
PallLean/Paper93/DeepMath/PathB/ComputationalDepthGodMoveRuntimeCapacity.lean
PallLean/Paper93/DeepMath/PathB/ComputationalDepthRuntimeFaithfulConstructionNoGo.lean
PallLean/Paper93/DeepMath/PathB/ComputationalDepthRuntimeFaithfulEquivalence.lean
```

The final equivalence is:

```text
RuntimeFaithfulGodMoveLowerBoundConstruction
  iff DeepSATSearch
  iff not CanonicalSATDecisionInP
```

So the runtime-faithful God-Move construction is not a remaining mechanical
Lean task.  It is the separation theorem in this formulation.

## Why Gravity Does Not Close It

The N-Frame gravity story identifies gravity with boundary entropy / horizon
area / information capacity.  In the route this is the capacity socket:

```text
GodMoveSolverCapacity
boundaryComplexity
solverCapacity
```

That is paper-faithful, but it is still a capacity measure.  It can explain why
an observer boundary has finite information capacity.  It does not by itself
prove a SAT time lower bound.

To make gravity load-bearing, one would need an additional theorem:

```text
irreducible SAT witness-search mass forces superpolynomial time-bounded cost
```

That theorem is the P vs NP lower bound again.

## Barrier Placement

The framework's original instruments are rank, log-det action, boundary
capacity, and locality-based geometry.  Those instruments are natural and local
in the relevant complexity-theoretic sense: they define efficiently checkable
or algebraic largeness/capacity properties.

That is why they repeatedly collapse into one of two outcomes:

1. The P-side upper bound is false, because easy objects can have high rank or
   high static complexity.
2. The SAT-side lower bound is exactly P vs NP, because it says no polynomial
   time observer can produce SAT witnesses.

Moving to K^t fixes the resource axis, but it does not remove the known
barriers.  The missing theorem must be non-natural, non-local, and genuinely
time-sensitive.  Rank, log-det, entropy, area, and capacity can be useful
diagnostics, but they are not the load-bearing separator.

## Correct Final Framing

The framework's defensible contribution is:

```text
Observer boundedness, made precise on the correct resource axis,
is the K^t / computational-depth frontier for SAT witness search.
```

The framework does not currently advance that frontier with a new lower-bound
technique.  It faithfully re-encodes the hard target:

```text
SAT has no uniform polynomial-time witness producer.
```

That target is the P vs NP lower bound.

## Remaining Breakthrough

The only positive theorem that would close the route is a concrete,
non-natural, time-axis lower bound:

```text
For every uniform polynomial-tau observer M,
there is a satisfiable CNF phi such that M fails to produce a satisfying witness
within its polynomial tau budget.
```

Equivalently:

```text
DeepSearch
not ShallowSearch
not CanonicalSATDecisionInP
```

All capacity, gravity, rank, and live-slot refinements should be treated as
audits or diagnostics unless they supply that time-axis theorem without
assuming it.
