# Decision-invariant repair: bounded research attempt

Base: `razborov-recoverRho-wip`, commit `688fb6629d17e490f2d00573a4b8017a8ca5faec`.

## Outcome

No P ≠ NP proof was found. This attempt tests proposed ways to repair the
trace-to-time bridge rather than assuming such a bridge. It adds a small
standalone Lean obstruction module, not a new separation theorem.

## Candidate 1: use the decision function's split-matrix rank

Rejected using existing code, not claimed as new work. The existing
`ComputationalDepthHankelGeneralCircuitNoGo.lean` combines equality rank 2^n
with the explicit formula-size bound 10n+1. Thus removing witness traces and
using a semantic matrix still does not make raw rank a general time/size
lower bound. This does not rule out logarithmic-rank bounds for appropriate
communication models or other, more constrained invariants.

## Candidate 2: a decision-only invariant dominates all verifier trace ranks

New module: `PallLean/Paper93/DeepMath/PathB/DecisionInvariantTraceRankAudit.lean`.

For any predicate P with an accepted input x, define a verifier presentation

    accepts(x,w,t) := P(x) and w=t,  w,t in Fin(k+1).

Its existential projection is exactly P. At x its rational acceptance matrix
is the identity, so its rank is k+1. A finite invariant B depending only on P
cannot bound this rank for every k: choose k=B(P).

This gives `no_decision_only_rank_upper_bound`. The statement concerns
witness/trace acceptance matrices at a fixed input, not automatically every
SPDP or observer quantity in the repository. Any application to those objects
requires a separate checked identification.

## Candidate 3: minimize over all equivalent verifier presentations

Without a resource restriction, the proposed repair is degenerate. Put all
work into the acceptance predicate:

    accepts(x,(),()) := P(x).

The projected predicate is P, and the one-by-one matrix has rank at most 1.
`semantic_normalization_rank_le_one` proves this existence result; it does
not define a computable minimization procedure. In particular it does NOT
show that P is easy to evaluate or that the presentation is a polynomial-time
NP verifier. Those are precisely the constraints that unrestricted semantic
normalization forgets.

The paired theorem `equivalent_presentations_rank_gap` exhibits equivalent
presentations with arbitrarily separated ranks on an accepted input.

## Candidate 4: constrain the normalization by actual computation resources

This is not refuted by the preceding theorems, but no SAT lower bound for it
was obtained. A viable next proposal must specify a fixed non-oracle machine
model, encoding, evaluation cost, and a proved connection from the invariant
to all relevant algorithms. It cannot obtain that connection merely by naming
an interface field `runtimeFaithful` or supplying the desired lower bound as
an assumption.

The existing `ComputationalDepthRuntimeFaithfulEquivalence.lean` proves the
current runtime-faithful construction target equivalent to `DeepSATSearch`
and to absence of a canonical polynomial SAT decider. This equivalence was
rechecked locally; only standard Lean axioms were reported. It does not prove
either side. The general textbook-class connection in
`ComputationalDepthUniversalModelPvsNPCashout.lean` also explicitly requires a
`UniversalCNFSATModelBridge`; a conditional bridge is not a constructed
universal-model adequacy proof.

## Honest significance

The new result excludes two tempting representation-based repairs. It is
small elementary mathematics, not a claimed novel complexity-theory breakthrough.
It does not exclude all approaches, establish a new general SAT time lower
bound, or measure percentage progress toward P ≠ NP. The missing positive
argument remains open.

## Validation

Validation completed successfully (exit 0) using Lean 4.28.0 and Mathlib v4.28.0.
All four printed theorem dependencies were exactly `propext`, `Classical.choice`,
and `Quot.sound`; no custom axioms or `sorryAx` were reported.

Command (run from the existing dependency-equipped checkout):

```sh
lake env lean /home/darre/pall-lean-decision-audit/PallLean/Paper93/DeepMath/PathB/DecisionInvariantTraceRankAudit.lean
```
The file includes `#print axioms` for its four main conclusions. No new axioms,
`sorry`, changes to the existing theorem statements, or external publication
are part of this attempt. A successful check of this file is not a full-repo
build or an audit of all existing modules.
