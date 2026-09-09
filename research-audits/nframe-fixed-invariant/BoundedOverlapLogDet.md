# An overlap-tolerant sufficient condition for the Route B lower bound

This attempt retains the existing Route B quantity log det(I + theta A).
For A PSD and theta > 0, suppose:

* every theta*eigenvalue(A) is at most L, with L >= 0;
* theta*trace(A) >= mu*R.

Then the checked estimate is:

    log det(I + theta A) >= (mu/(1+L))*R.

Proof: for x >= 0, log(1+x) >= x/(1+x). For x <= L the latter is
at least x/(1+L). Sum over eigenvalues and use the repository's exact
positive-definite logdet spectral expansion and trace identity.

The formal matrix theorem is stated on B itself: B is positive definite, its
eigenvalues lie in [1,1+L], and trace(B)-N >= mu*R. It concludes
log det(B) >= mu*R/(1+L). For B=I+theta*A these are the corresponding shifted
spectral conditions. The new file does not derive that affine eigenvalue
correspondence; it keeps the conditions explicit.

Unlike summing standalone local log-determinants, this allows overlaps and
explicitly accounts for them through the maximum eigenvalue. The result needs
no positive lower bound on every eigenvalue and permits a nontrivial kernel.

## Potential application, not established SAT semantics

If the intended global matrix is a sum of PSD local gadgets, trace is additive.
A proved local trace budget can then supply the mass hypothesis even when the
local ranges overlap. A separate bound on the global maximum eigenvalue is
needed to keep the loss factor 1+L under control. This conditional application
must use the same actual global matrix as the Route B upper bound.

For m repeated unit contributions in one direction, L=m and mass=m, so the
new lower bound is only m/(1+m); it correctly avoids the false linear lower
bound exposed by ShiftedLogDetOverlap. Disjoint unit directions have L=1 and
mass=m, giving a valid m/2 bound. Neither case proves SAT necessity.

The remaining research task is to derive the matrix coupling, local mass budget,
and global overlap bound from the intended geometry and actual machine traces,
and show that SAT forces sufficiently many contributions. No such derivation or
superpolynomial time lower bound is claimed. This is standard spectral analysis
formalized as a sufficient condition, not a completed separation theorem.

Verification:
    lake build PallLean.Paper93.DeepMath.NFrame.LogDetEigenvalues
    lake env lean research-audits/nframe-fixed-invariant/BoundedOverlapLogDet.lean

## Dependency check

An attempt to build RouteBBridgeALogDetProgress failed in the pre-existing
archived file PallLean/Archive/Paper93Unsafe/Final_P_ne_NP_Wrapper.lean: lines
41 and 48 reference the unavailable identifier
PaperFaithfulSeparation.P_ne_NP_via_theorem207_from_narrow_gauge.
No archived proof was patched or assumed. The checked result imports only the
narrow LogDetEigenvalues module. The full Route B dependency build did NOT pass.
