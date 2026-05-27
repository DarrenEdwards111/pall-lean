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
- `distinctLeadingMonomial_linearIndependent`: the triangular version used by
  shifted NW rows.  Rows may share lower monomials; distinct maximal monomials
  under a term order still force linear independence.
- `distinctLeadingMonomial_card_le_spdpRank` and
  `NWSPDPIndependenceCertificate.ofDistinctLeadingMonomials`: the matching
  row-count/certificate constructors for the shifted-leading model.

The remaining NW-specific asymptotic work is no longer linear algebra.  It is
the combinatorial construction of enough distinct leading monomials from the
actual NW design/intersection property.

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

The ambient rank bridge is now factored into its honest concrete shape:

- `NWDerivativeRowsActualSPDPBridge` carries a coefficient-projection map from
  the concrete `MvPolynomial` space into the finite-support row model, plus
  the realization proof that every selected derivative-window row is the image
  of an actual element of `SPDP.spdpSubspace`;
- `nwDerivativeWindowRows_finrank_le_actual_spdpRank` proves that such a
  realization bounds the finite-support row rank by the actual
  `SPDP.spdpRank`;
- `NWSPDPIndependenceCertificate.ofLowAgreementActualSPDP` composes the
  low-agreement/window hypotheses with this concrete bridge, so the final
  certificate is stated against the real SPDP rank of an ambient
  `MvPolynomial`, not a free numerical rank.
- `squarefreeSupportExponent`, `nwCoefficientProjection`, and
  `nwDerivativeWindowList` define the concrete coefficient-extraction and
  derivative-window objects.
- `NWDerivativeRowsActualSPDPBridge.ofProjectedDerivativeRows` proves the
  actual SPDP membership part: if the projected derivative-row coefficient
  identity holds, then the finite-support rows are images of elements of
  `SPDP.spdpSubspace`.
- `nwMvMonomial` and `nwMvPolynomial` define the actual encoded
  Nisan-Wigderson polynomial inside the project's `MvPolynomial` universe.
- `NWProjectedDerivativeRowIdentity` names the remaining concrete
  coefficient identity for that polynomial, with the required
  `Function.Injective enc` side condition included in the interface, and
  `NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial` composes it into
  the actual SPDP certificate.  The bridge is therefore no longer phrased for
  an arbitrary ambient polynomial.

The remaining formal theorem is now the coefficient identity for the concrete
NW `MvPolynomial`: prove the encoding is injective, and prove that applying
`nwCoefficientProjection` to the actual iterated derivative over a window `D`
gives exactly `nwDerivativeWindowRows code D a`.  This closes the modest
window-row lower bound.  The stronger shifted-leading lower bound still needs
the analogous projection/membership construction for shifted rows.

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
- over all six `kappa=2` point windows for `NW_{d=4,q=5,e=2}`, the unshifted
  leading-monomial count is `150`, exactly matching the real
  `Gamma_{2,0} = 150`;
- after allowing all degree-`<=1` shifts, the selected shifted family has
  `3150` candidate rows but `1550` distinct leading monomials, exactly
  matching the real `Gamma_{2,1} = 1550`.

These finite ranks are calibration only.  The frontier result requires an
asymptotic NW support-independence theorem, not brute-force exact rank
computation.
