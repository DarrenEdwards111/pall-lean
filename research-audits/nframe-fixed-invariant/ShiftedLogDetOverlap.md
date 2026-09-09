# Route B local aggregation: overlap and exact marginal cost

Target: the existing `log det(I + theta A)` in
`Paper283/RouteBBridgeALogDetProgress.lean`, at the legal specialization theta=1.
This is not a replacement for the N-Frame action. It tests the lower log-det
estimate used by its Route B rank bridge. Its sign is positive log-det, unlike
the raw analytic barrier's negative log-det; no equivalence of these costs is
assumed.

Attempt: derive the missing local-to-global lower estimate from positive local
gadgets and the natural additive coupling A = sum(local gadgets).

In one shared direction, local positive-definite matrices [a] and [b] give:

    global = log(1+a+b) < log(1+a) + log(1+b), for a,b > 0.

Thus even positivity plus additive coupling cannot justify summing standalone
local log-det values as a lower bound on the global log-det. This does not refute
the repository's theorem: `active_logDet_sum_le_global` is an explicit hypothesis,
and its abstract localLogDet need not mean the standalone values tested here.
It rules out this attempted way of discharging that field without overlap control.

The actual marginal contribution when [b] is added after [a] is

    log(1+a+b) - log(1+a) = log(1+b/(1+a)).

For a,b >= 0, an exact condition for a lower bound delta is:

    delta <= marginal  iff  (exp(delta)-1)*(1+a) <= b.

The accompanying Lean file proves all these statements. In particular, repeated
unit contributions have decreasing marginals log(1+1/(1+a)). Their sum telescopes
to log(1+m), not m*log(2). This latter general telescoping explanation is prose,
not an additional formal theorem in the file.

A possible repair is to use actual marginals in the lower account and prove
SAT-specific control of overlaps/relative contributions. That property must be
derived for the intended global matrix along all relevant computations; assigning
fresh independent directions to every local gadget simply imposes it. No such
necessity theorem, machine-to-gauge map, or separation is obtained in this attempt.

Verification:
    lake env lean research-audits/nframe-fixed-invariant/ShiftedLogDetOverlap.lean
