# Route W bottom-socket analysis

Date: 2026-05-23

## Claim under audit

The row-indexed / fixed-project Route W sockets ultimately require the actual Cook-Levin generated rows

```lean
project (mlProj (shift * g))
```

for `g ∈ boundedProfileClassifiedSet ...` to land in a bounded profile subspace (or, equivalently, to admit finite same-profile slot expansions).  In the paper-faithful row-indexed API this is:

```lean
CookLevinRouteWRowIndexedGeneratorExpansion_paperScale
```

and in the fixed-project API it is the corresponding projected generator/profile containment used to build a `BoundaryQuotientCompressionCertificate`.

## Critical observation

This is not just a bridge lemma.  Once combined with the existing boundary-quotient closeouts, the bottom socket yields a polynomial P-side rank bound for the projected Cook-Levin product.

The relevant Lean chain is:

```lean
CookLevinRouteWRowIndexedGeneratorExpansion_paperScale
  -> cookLevinRouteWRowIndexedNaturallyProfiledGeneratorContainment_paperScale_of_expansion
  -> cookLevinShiftAugmentedBoundaryQuotientCertificate_paperScale_of_rowIndexed_uniformised
  -> cookLevinShiftAugmentedProjectedWithinProfileFinrank_paperScale_of_rowIndexed_uniformised
```

This is exactly the P-side compression target, not merely infrastructure.

## Consistency condition

If the same projection also preserves the NP-side identity minor, then the projected polynomial has both:

1. Polynomial upper bound from the Route W bottom socket / boundary quotient certificate.
2. Superpolynomial lower bound from identity-minor preservation.

At `n = 2^804` the existing arithmetic sandwich gives contradiction (`n^201 ≤ n^200`).  This is the same failure mode documented in `ARCHITECTURE-BUG.md`: an upper bound on an object that still contains/preserves the renamed hard witness is false.

## Consequence

The next task is not to add another bridge.  The real fork is:

- prove the actual Route W projection destroys/quotients the hard identity-minor witness enough that NP-side preservation no longer applies to that projected object; or
- prove NP-side preservation for the projected object, in which case the bottom socket cannot be true for the actual Cook-Levin factors; or
- identify a different target polynomial/sheet so P-side compression and NP-side lower bound are not asserted on the same object.

Until one of these is resolved, `CookLevinRouteWRowIndexedGeneratorExpansion_paperScale` should be treated as the load-bearing P-side claim and likely false if paired with identity-minor preservation.

## Verdict

Darren's objection is correct: the bottom socket is the theorem/axiom boundary.  Building more adapters around it risks hiding the same contradiction rather than proving the missing mathematics.
