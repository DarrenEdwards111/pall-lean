# Algebraic SPDP Pivot

This directory is the positive home for the SPDP/God-Move machinery.

It is not a Boolean `P` versus `NP` proof route.  The Boolean route fails
because a SAT decider can present the computation without carrying the
high-rank SPDP object.  In algebraic complexity the target is a fixed
polynomial family, so the SPDP rank is intrinsic and cannot be hidden by a
decider presentation.

## Current artifact

`ArithmeticCircuitSPDPPivot.lean` proves the conversion layer:

1. an analytic lower bound on the shifted-partial-derivative rank of an
   explicit polynomial gives `analyticLower <= Gamma_{kappa,ell}(f)`;
2. a homogeneous depth-3 circuit with `s` product gates has

   `Gamma_{kappa,ell}(f) <= s * choose(degree,kappa) * M(numVars,ell)`;

3. therefore

   `analyticLower <= s * choose(degree,kappa) * M(numVars,ell)`.

The hard theorem is isolated as `NWSPDPIndependenceCertificate`: a
Nisan-Wigderson support/leading-monomial independence proof.  This is the
real analytic lower-bound target.

## Calibration script

`scripts/algebraic_spdp_nw_depth3.py` computes exact small SPDP ranks over
`QQ` for `perm_3`, `det_3`, and the small NW design polynomial
`NW_{d=3,q=3,e=2}`.  It confirms the expected small signal:

- `Gamma_{1,0}(perm_3) = choose(3,1)^2 = 9`;
- `Gamma_{2,0}(perm_3) = choose(3,2)^2 = 9`;
- at `(kappa,ell)=(1,1)`, `perm_3 = 86`, `NW = 84`, and `det_3 = 74`.

These finite ranks are calibration only.  The frontier result requires an
asymptotic NW support-independence theorem, not brute-force exact rank
computation.

