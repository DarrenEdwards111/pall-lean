# From parity inconsistency to local activity: an explicit missing coupling

This test uses the existing `localEnergy` and `parityViolation` without
changing the N-Frame invariant or its coefficients.

On the three-cycle, put charge -1 at every vertex. If x,y,z label its
edges, the signed vertex constraints are xy=-1, yz=-1, zx=-1. Multiplying
gives (xyz)^2=-1, impossible even over the reals. In particular no signed
Boolean edge assignment satisfies these constraints.

Nevertheless the unconstrained vertex field Phi(v)=-1 has localEnergy=0
at every vertex: all edge differences vanish and each field sign matches
its charge. Thus it clears no positive activity threshold, for any alpha
and beta. This is not an assignment satisfying the edge constraints.

The distinction is constructive: when Phi is instead explicitly induced
from signed edges as [xy,yz,zx], the SAME parityViolation function has total
violation at least 2. The accompanying Lean theorem checks every signed
edge case. So an incidence constraint can make the local violation detect
this contradiction; allowing an arbitrary vertex field loses that connection.

Scope:
* This is a three-cycle consistency test, not an expander-family lower bound.
* It does not show that the constant field is reachable by the intended
  holographic machine-to-field map or satisfies additional admissibility rules.
* It shows parity inconsistency alone cannot force activity for arbitrary
  Phi in the implemented interface.
* The induced-field result is a constant violation bound, not a runtime bound.
  An arbitrary SAT decider need not maintain this signed-edge realization.

The desired next derivation therefore has two distinct obligations: establish
the actual machine-to-field incidence/admissibility constraint, and prove the
quantitative activity/cost forced along every correct computation. Neither
is supplied by the analytic log-det inequalities or proved in this audit.

No existing definition is patched and no new hardness assumption is introduced.
The proof imports only BridgeALocalEnergy and Mathlib, avoiding the archived
Route B wrapper. Verification commands:

    lake build PallLean.Paper93.Paper283.BridgeALocalEnergy
    lake env lean research-audits/nframe-fixed-invariant/LocalEnergyParityGap.lean
