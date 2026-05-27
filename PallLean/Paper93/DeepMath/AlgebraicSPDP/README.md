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

The file now proves the support/leading-monomial engine:

- `leadingSupport_linearIndependent`: private pivot monomials imply linear
  independence of the selected shifted partial rows;
- `leadingSupport_card_le_spdpRank`: if those rows lie in the SPDP row space,
  their count lower-bounds the SPDP rank;
- `NWSPDPIndependenceCertificate.ofLeadingSupport`: enough private pivots
  construct the NW independence certificate used by the depth-3 lower-bound
  conversion.

The remaining NW-specific asymptotic work is no longer linear algebra.  It is
the combinatorial construction of enough private pivot rows from the actual
NW design/intersection property.

`NWSupportIndependence.lean` proves the first NW-specific combinatorial
layer.  In the graph-code model of the NW polynomial, low agreement of
distinct codewords implies:

- every derivative window larger than the agreement bound contains a
  disagreement, so differentiating by one graph kills the other monomial;
- every outside window larger than the agreement bound gives injective
  residual graph supports, hence private leading monomials;
- these residual pivots construct `NWSPDPIndependenceCertificate` once the
  polynomial-calculus identification supplies containment in the actual SPDP
  row space.

The file also proves the finite-support polynomial-calculus bridge:

- `nwDerivativeWindowRows` is the coefficient row obtained by differentiating
  the NW polynomial by one label's graph over the derivative window;
- `nwDerivativeWindowRows_eq_residualIndicator_of_lowAgreement` proves that,
  under low agreement and a large enough derivative window, this actual
  derivative row is exactly the residual private-pivot indicator row;
- `NWSPDPIndependenceCertificate.ofLowAgreementDerivativeRows` lets the final
  certificate be stated using the actual derivative-window rows.

The remaining formal theorem is now only the ambient encoding/containment
step: embed these finite support coefficient rows into the project’s concrete
`MvPolynomial`/`SPDP.spdpSubspace` representation and prove their row-span
rank is bounded by the actual SPDP rank.

## Calibration script

`scripts/algebraic_spdp_nw_depth3.py` computes exact small SPDP ranks over
`QQ` for `perm_3`, `det_3`, and the small NW design polynomial
`NW_{d=3,q=3,e=2}`.  It confirms the expected small signal:

- `Gamma_{1,0}(perm_3) = choose(3,1)^2 = 9`;
- `Gamma_{2,0}(perm_3) = choose(3,2)^2 = 9`;
- at `(kappa,ell)=(1,1)`, `perm_3 = 86`, `NW = 84`, and `det_3 = 74`.
- for the honest `d=4` prime-field instance `NW_{d=4,q=5,e=2}`,
  `Gamma_{1,1} = 417` and the depth-3 denominator is `84`, giving the
  calibration bound `s >= 5`.

`scripts/algebraic_spdp_nw_leads.py` checks the actual derivative-window
leading monomials behind the Lean bridge.  It confirms:

- at `d=3,q=3,e=2`, no derivative window can make both the differentiated
  window and outside residual window larger than the agreement bound, so the
  simple residual-pivot bridge fails for a precise finite-size reason;
- at `d=4,q=5,e=2,D={0,1}`, the actual NW derivative-window rows exactly
  equal the residual indicator rows, residual supports are injective, and the
  leading monomials match the residual graph pivots for all 25 labels.

These finite ranks are calibration only.  The frontier result requires an
asymptotic NW support-independence theorem, not brute-force exact rank
computation.
