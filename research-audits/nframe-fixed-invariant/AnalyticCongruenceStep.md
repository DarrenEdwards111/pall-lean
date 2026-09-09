# Existing congruence operation: exact analytic N-Frame step

The repository already studies A -> U^T A U in
`PallLean/Paper93/DeepMath/NFrame/BarrierOrthogonalInvariant.lean`.
This attempt retains `S_NF` and generalizes its barrier calculation.

For invertible U, positive definiteness is preserved. If det A and det U are
positive, the exact barrier drop is 2 log(det U). With adj, phi, chi and all
coefficients held fixed, the full analytic action drop is 2 lambda log(det U).
In particular, determinant-one updates preserve that full fixed-field action.

This supplies an explicit geometric operation with domain preservation, not a
machine-to-gauge simulation. It does not prove all holographic admissibility
conditions. It does not establish a per-step bound on det U for arbitrary machine
execution. An upper bound det U <= exp(r/(2 lambda)), for positive lambda, would
bound this fixed-field drop by r, but must itself be derived from machine steps.
Changes to phi, adjacency or charges require additional estimates.

Determinant-one congruences alone cannot discharge this fixed-field action.
This is a useful constraint on a proposed evolution, not a refutation of an
evolution that changes the other terms or uses other geometric operations.

No SAT-specific initial cost, terminal condition, universal simulation, or
superpolynomial lower bound is proved here.

Verification: `lake env lean research-audits/nframe-fixed-invariant/AnalyticCongruenceStep.lean`.
