# Full-action extraction status

`FullActionRankExtraction.lean` passed Lean v4.28.0, with only propext,
Classical.choice and Quot.sound reported for all three theorems.

For the repository's `fullLagrangianFixed`, holding the graph and gauge fixed:

    L(alpha,beta+1,gamma,g) - L(alpha,beta,gamma,g)
      = finrank(range(g.projection)).

Taking the natural-number floor recovers that rank exactly. The same equality
holds at every time for a supplied gauge trajectory g(t).

This uses the full functional in `Paper93/Concrete/FullLagrangianFixed.lean`,
not the earlier tape-mask kinetic surrogate. However, that functional ALREADY
contains projection rank as its beta-weighted term. Recovering this coefficient
is an algebraic identity, not an independent discovery of a computational
invariant or a construction of its gauge. It is not the same as deriving rank
from the original sign/parity-and-log-determinant action without an explicit
rank term, nor is it differentiation through a gauge minimizer.

No theorem here connects a complete DTM configuration to a semantically
adequate gauge, bounds the resulting rank on every polynomial-time machine,
or proves a SAT-specific superpolynomial lower bound. A supplied time-indexed
gauge does not by itself establish any of these facts. Thus the requested
complete dynamic-rank derivation and separation remain unproved.

Included in the follow-up reconstruction audit commit; not part of the earlier 5b5b4a84 push.
