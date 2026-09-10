# Boundary dimension versus decision runtime

This continuation does not prove SAT separation. The existing theorem
`satPolynomialClockRankBound_iff_separation` already proves that the requested
SAT-specific polynomial runtime/rank estimate has exactly the strength of the
repository's faithful SAT-not-in-P target. It is not an independent lemma
whose proof can be obtained just by transporting the minor.

The new module isolates a genuinely valid restricted implication:

1. An actual family of linear boundaries preserving the paper-window rows
   has dimension q(n) at least n^(floor(log2(n))/4).
2. Such q has no eventual fixed-polynomial bound.
3. If a computation has the explicit write budget q(n) <= c*T(n)+b for
   fixed c,b, its clock T is not polynomial in n.

Step 3 is numerical cost accounting, not a formal machine-emission semantics.
The write budget is an explicit hypothesis. It applies when all q coordinates
must be emitted at bounded throughput; it is not justified for decision-only
SAT machines, succinct operators, lazy boundaries, or a decoder queried only
at selected entries. Costs for larger coefficients would only add obligations.

The scope is polynomial time in n. A concrete machine bridge must additionally
relate n to encoded input length with both directions needed for the intended
asymptotic transfer. No identification with a production N-Frame action is
introduced here.

Remaining unrestricted obligation: derive unavoidable computational work from
SAT correctness for every legal machine, without presupposing emission of
this chosen representation. Neither positivity, expander erasure resilience,
exact decoding, nor idempotence establishes that necessity. Replacing this
obligation by a field of a certificate does not discharge it.

Validation: the new module compiled under Lean 4.28.0 with no warnings.
Its three printed theorems use only propext, Classical.choice and Quot.sound.
The 431-file imported source closure and dependency configuration matched
/home/darre/pall-lean. The module was added to the focused checker; the entire
91-module suite was not rerun in this continuation.
