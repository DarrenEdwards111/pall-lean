# Dynamic Lagrangian rank attempt — 2026-09-08

## What was attempted

Replace observer-supplied numerical `stateActionRank` by a matrix rank computed
from the existing kinetic operator and the actual complete DTM configuration.
This is a candidate definition, not a claim to have uniquely derived the
intended full N-Frame invariant.

For a run configuration c, let D(c) be diagonal with entry 1 on true tape
cells and 0 on false tape cells. Let H be the repository's
`kineticTermHessian 1 (tapeSize M n)`. Set

    A(c) = D(c) H D(c)
    liveRank(M,x,t) = rank A(run(M,x,t)).

The tape mask is an explicit new modelling choice. No SAT semantics,
superpolynomial lower bound, or free natural-number rank enters the definition.
Only the kinetic component is used, not the full parity or barrier terms.

## Verification

Built `PallLean.Paper93.DeepMath.PathB.CompiledGadgetIsHessian`: success,
1176 Lake jobs reported (not 1176 newly rebuilt source modules).

`LiveKineticRank.lean` then passed Lean v4.28.0. All four printed theorem
dependencies are only propext, Classical.choice, Quot.sound.

Proved for every machine, every input, every time:

- liveRank <= tapeSize = n^M.timeBound + 1;
- peak rank through any horizon <= n^M.timeBound + 1;
- summed rank through T <= (T+1)(n^M.timeBound+1);
- any other square matrix on the same coordinates has the same rank ceiling.

The independent exact rational two-cell example in `mask-example.json` gives
rank 0 for tape 00 and rank 1 for tape 10, demonstrating nonconstant dependence
on configurations. This small example does not prove a SAT lower bound.

## Result and scope

The candidate is dynamic but its peak and polynomial-horizon accumulation are
polynomial. It cannot establish the desired superpolynomial hardness while
retaining that polynomial-time calibration. Enlarging the indexing space to
implicit residual functions, higher derivatives or other objects would require
a separate definition, a soundness proof, and a SAT lower-bound proof.

An arbitrary scalar Lagrangian value does not uniquely specify a linear map or
its rank. The full parity term involves sign and is not globally smooth; the
repository's kinetic Hessian is an algebraic closed-form definition, not a
formal differentiation theorem for the full three-term action. Those
distinctions must not be hidden by calling this candidate the full invariant.

The requested full Lagrangian-to-live-rank derivation and SAT-specific lower
bound were NOT obtained. No existing dynamic invariant was overwritten, and
no changes were pushed.
