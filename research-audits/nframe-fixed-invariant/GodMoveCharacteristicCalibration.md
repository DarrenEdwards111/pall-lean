# Characteristic-target calibration: compact products need not have small rank

The requested general efficient extraction, polynomial common span, and
hard-family minor have **not** been established together. The new checks
sharpen the obstruction: the characteristic target can have large SPDP rank
even on a very easy family, while an unsatisfiable formula gives exactly the
zero target. These are restrictions on this representation, not a proof or
disproof of P versus NP.

## A constructed product and identity minor on the same target

`GodMoveUnitCharacteristic.lean` defines the signed CNF

    U_n = (x_0) AND ... AND (x_(n-1)).

It proves that the formula has `n` clauses, all its variables are below `n`,
and its only satisfying `n`-bit assignment is the all-true assignment.
The canonical characteristic polynomial is therefore exactly

    verifierCharacteristic(n, U_n) = P_n = product_(i<n) X_i.

This is an equality of ordinary polynomials, not just agreement on Boolean
inputs. A concrete product program reads each variable once and multiplies
into an initial `1`. Its evaluation is proved to equal this very target,
and its counts are exactly `n` variable references and `n` multiplications.
These are arithmetic-operation counts, not a Turing-machine bit-complexity
theorem or a general-purpose extraction algorithm for arbitrary SAT inputs.

`GodMoveMonomialMinor.lean` constructs rows indexed by `k`-subsets `S` of
the `n` variables. Differentiating `P_n` once in every variable of `S` leaves
the squarefree monomial on the complement. At the corresponding coefficient
columns the selected matrix has entries

    coeff(complement(S), derivative_T(P_n)) = if S=T then 1 else 0.

This is a literal identity minor with `choose(n,k)` rows and columns.
Its rows are proved admissible for the discrete block partition, with zero
shift, in the repository's actual strict SPDP subspace. Linear independence
is proved using the monomial basis; it is not a certificate assumption.
Consequently, for every `n`, `k`, and shift allowance `ell`,

    choose(n,k) <= strict SPDP rank(P_n),
    choose(n,k) <= inclusive SPDP rank(P_n).

The unit-formula file transfers the very same identity and rank bounds to
`verifierCharacteristic(n,U_n)`. Any finite-dimensional common span containing
these rows also has dimension at least `choose(n,k)`. Finite dimensionality
is explicit: Lean's natural-number `finrank` must not be used to bound an
infinite-dimensional polynomial space.

The quantitative calibration is also checked. With `k = floor(log_2 n)`,
for every fixed natural exponent `d`,

    n >= 2^(max(20, 4*(d+1))) -> n^d < rank(P_n).

For example, `n >= 2^804` suffices for the `n^200` comparison. Both strict
and inclusive ranks satisfy the lower bound for every shift allowance.
Lean further proves that no constants `C`, `d`, and starting size `n0` give
an eventual upper bound `rank(P_n) <= C*n^d`, even with zero shift. The same
no-polynomial-bound statements are proved for the unit-CNF characteristic
target. Every finite common span retaining these logarithmic-order rows
must likewise exceed `n^d` beyond the displayed threshold.

Faithful SAT-query correctness also transfers this lower bound to the
constructed `machineQueryPolynomial`. That statement applies to any correct
clocked SAT decider, regardless of running time; it supplies no P-side upper
bound.

This is a **minor on an easy unit-CNF family**, not the required minor for
the paper's designated hard family. In particular, high rank of this target
does not by itself measure computational hardness, and a short arithmetic
product program does not imply a polynomial global SPDP rank bound.

## An unsatisfiable formula cannot supply this characteristic minor

`GodMoveCharacteristicUnsat.lean` proves, for genuine signed CNF semantics,

    NOT Satisfiable(phi) -> verifierCharacteristic(n,phi) = 0.

No variable-bound assumption is needed for that direction. Both strict and
inclusive SPDP ranks are therefore zero at all parameters. With the usual
variable bound and faithful machine correctness, the pinned-query source is
also exactly zero, with both ranks zero.

This prevents using an unsatisfiable Tseitin contradiction as a positive-minor
example for this specific characteristic target. It does not say that a raw
gadget product is zero, or that a satisfiable family cannot have a minor.

The distinction matters in the desktop paper: section 23.2, printed pages
122–123, defines the characteristic polynomial by summing over satisfying
assignments and suggests Tseitin contradictions as examples. Section 25.1,
printed page 126, explicitly starts from contradictions and asserts a
positive characteristic-rank lower bound in Theorem 117. An unsatisfiable
instance cannot satisfy that assertion for the defined polynomial. In
contrast, Lemma 189 on printed page 177 concerns **satisfiable** padded-hard
instances, and the legacy `PaperFaithfulSeparation.GodMoveHardInstanceData`
in `GodMoveCore.lean` also includes a satisfiability hypothesis.
The zero theorem is not a refutation of those
different, satisfiable targets.

## Remaining separation obligation

For a genuine hypothetical polynomial-time SAT decider, a valid separation
still requires a specified source with a runtime-derived polynomial rank
bound, a justified rank-nonincreasing extraction, and a lower bound for the
same extracted hard target at the same parameters. The new finite product
program and easy-family minor do not supply that combination.

Nor is the intended conditional contradiction itself an error: if justified
upper and lower bounds conflict under a hypothetical polynomial-time decider,
that is the desired conclusion. The failure exposed here is the unsupported
inference from a compact product presentation to small global SPDP rank.

## Verification

The three new files are standalone research checks and do not alter the
production compiler, invariant, or theorem hypotheses. All three compile
without warnings, and their 32 printed theorem-axiom checks contain only
subsets of `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholder
or custom axiom was added. Focused checks use Lean 4.28.0 and cached repository
dependencies; relevant imported source
files match this worktree. This is not a fresh full-repository build.

See [GodMoveHandshake.md](GodMoveHandshake.md#lean-checks) for commands that
build the handshake dependencies and check all six related audit modules.
