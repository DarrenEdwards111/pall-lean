# Scope of the overlap-tolerant certificate

The invariant remains Route B's log det(B), with B = I + theta A.
No replacement energy, rank, or observer restriction is introduced.

For N shifted eigenvalues x_i in [0,L], the previous sufficient lower
certificate is sum(x_i)/(1+L). But sum(x_i) <= N L, so that certificate
is at most N L/(1+L) <= N. In particular, adding a local mass condition
mu R <= sum(x_i) cannot make mu R/(1+L) exceed N.

The same spectral cap gives an upper bound on the invariant itself:

    log det(B) <= N log(1+L).

OverlapBudgetCeiling.lean formalizes the normalized mass ceiling and the
matrix log-det upper bound using the narrow existing spectral import.
It does not depend on the broken archived Route B wrapper.

Consequences are conditional on parameter scaling: if N is polynomial in
encoded input length, the normalized-mass certificate cannot be
superpolynomial. If additionally log(1+L) is polynomially bounded, this
log-det value is polynomially bounded too. These observations do NOT show
the intended holographic dimension has such a bound, nor refute a separation
argument obtaining incompatible upper and lower bounds under a hypothetical
polynomial-time SAT decider. They limit what follows from the current
analytic sufficient condition alone.

Inspected concrete application:
PallLean/Paper93/Paper283/RouteBBridgeAConcreteBudget.lean uses
log(1+theta*eta)/pocketRank as its rankLogRate and still explicitly assumes
delta <= rankLogRate*kappa. Its constructor does not establish a uniform
positive delta independently of that budget. The abstract bridge also
receives its PSD matrix and local gadget family separately, with the
spectral lower inequality passed as a hypothesis.

Outstanding: derive the intended SAT-dependent coupling and its quantitative
parameter scaling. Neither a universal machine-to-gauge necessity theorem
nor a superpolynomial SAT lower bound is proved here. This is a checked
limitation of the latest sufficient estimate, not a completed separation.
