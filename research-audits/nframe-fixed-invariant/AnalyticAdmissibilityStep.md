# Analytic admissibility versus machine-step control

The N-Frame invariant is unchanged: this check imports the existing analytic `S_NF`.
For a one-dimensional positive-definite gadget matrix A(s) = [exp(s)], its existing
barrier equals -s. Holding adjacency, phi, chi and all coefficients fixed gives

S_NF(A(s)) - S_NF(A(t)) = lambda * (t-s).

For every positive lambda and proposed bound r, choose s=0 and t=(r+1)/lambda.
Both matrices are positive definite, yet the full action drop is r+1 > r.
`AnalyticAdmissibilityStep.lean` formalizes these statements.

## Scope

This does not assert that this pair is a legal machine transition, nor that it
satisfies every intended holographic constraint. It proves that positive
definiteness of the gadget matrix alone cannot provide a uniform step bound,
even for the full analytic action with its other terms held fixed. It does not
refute a bound on a properly defined machine-induced subset of transitions.

The inspected `SNF.lean` takes the gadget matrix as an independent input.
`StrictDynamicNFrameLagrangianInvariant.lean` supplies `configActionRank` as a
field; it does not derive this matrix from a machine configuration. The canonical
invariant supplies its binomial scale by construction. None of these definitions
establishes the needed machine-selected analytic transition rule.

Still required: construct the intended machine-to-gauge map; prove all geometric
constraints and domain preservation; derive bounds on determinant ratios and
changes of the other terms from a single actual machine operation; prove the
SAT-specific initial/terminal conditions. This attempt does not construct that
map or establish the SAT lower bound. Adding an arbitrary map or a step-bound
field would not discharge those obligations.

Verification command (from repository root):

    lake build PallLean.Paper93.DeepMath.NFrame.SNF
    lake env lean research-audits/nframe-fixed-invariant/AnalyticAdmissibilityStep.lean
