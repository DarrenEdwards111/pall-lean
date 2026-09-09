# Route B separation attempt, 2026-09-09

Result: the separation is not proved. This attempt adds a checked consequence
of the existing concrete constructor and identifies the mathematical premises
still needed. It does not change the N-Frame invariant or insert a hardness
assumption to obtain a theorem named separation.

The inspected baseline is `2cec4129` on `codex-asymmetric-observers`, which
contains the cited `1c241adf` and four subsequent local-energy audit commits.
Work was performed in an isolated checkout; the original checkout was preserved.

## New checked result: the concrete local rate loses the pocket-size factor

`ConcreteRateDilution.lean` uses the existing `compiledGadget` and `pocketFamily`.
For alpha > 0, kappa > 0 and gadgetN >= 1, it proves

    pocketRank = kappa * gadgetN
    (log(1 + theta * eta) / pocketRank) * kappa
      = log(1 + theta * eta) / gadgetN.

Thus the `hdelta_rate` premise of
`bridgeA_rankLogDetLowerHypotheses_of_cookLevinPocket_compiledGadget_log_div_pocketRank`
in `RouteBBridgeAConcreteBudget.lean` is exactly

    delta <= log(1 + theta * eta) / gadgetN.

For delta > 0 the new file also proves

    gadgetN <= log(1 + theta * eta) / delta.

Increasing kappa cannot improve this local floor. If theta, eta and a positive
delta are fixed across a family, gadgetN is bounded. Pointwise positivity of
delta alone is not a uniform lower bound: delta may shrink with gadgetN.
Allowing the spectral parameters to grow also changes the bound and must be
accounted for. This is a restriction on this particular rate schedule, not
a refutation of every possible N-Frame argument.

## What still prevents separation

The concrete floor is not the only remaining premise:

1. `PallLean/Paper93/Paper283/BridgeALogDetLower.lean` defines
   `BridgeARankLogDetLowerHypotheses`. Its fields include both
   `delta_le_rankLogRate_kappa` and `rankLogRate_totalRank_le_logDet`.
   The analytic assembly proves consequences of these fields.
2. `PallLean/Paper93/Paper283/RouteBMatrixToSATGauge.lean` defines
   `RouteBMatrixToSATGaugeFunctoriality`. Its fields separately require
   SPDP image containment, transport to a P-side rank upper bound, and
   transport to a projected NP-side rank lower bound. The scalar log-det
   estimates do not prove these transports.
3. `PallLean/Paper93/Paper283/RouteBFinalAssembly.lean` proves
   `noBoundedSATDeciderAtPaperScale_of_routeBCertificates` **assuming** a
   uniform family of `RouteBPerInstanceCertificate`. It does not construct
   those certificates from `DecidesSAT`.

For a runtime argument along this route, the missing work includes a map
from actual SAT computations to the intended admissible geometric objects,
proof that machine transitions pay the required cost, and input-length
scaling that makes the lower bound beat every polynomial. These are
mathematical obligations, not omitted Lean tactic invocations. In particular,
neither SAT correctness nor an injective encoding of configurations implies
the proposed geometric cost by itself.

The existing `OverlapBudgetCeiling` result remains in force: the normalized
trace certificate is at most ambient dimension. It cannot itself supply a
superpolynomial lower bound when that dimension is polynomial. The stronger
log-det ceiling also needs a bound on log(1+L). No assumption about the
intended matrix dimension or spectral scaling is silently supplied here.

## Verification and limits

The new audit file compiles under Lean 4.28.0. All five printed theorem axiom
lists are exactly `[propext, Classical.choice, Quot.sound]`. The existing
`OverlapBudgetCeiling.lean` was also checked successfully. The narrow imported
module sources agree with the cached home checkout used for these checks.

Commands used from `/home/darre/pall-lean`:

```sh
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/ConcreteRateDilution.lean
lake env lean /tmp/pall-separation-o8uSzb/research-audits/nframe-fixed-invariant/OverlapBudgetCeiling.lean
```

This is focused verification, not a successful build of the entire historical
repository or a proof of its final separation claim. A standard-axiom audit
checks a theorem's proof dependencies; it does not discharge hypotheses in
the theorem statement. No GitHub changes were published by this attempt.
