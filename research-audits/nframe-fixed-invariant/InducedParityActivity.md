# General induced-field activity and its scaling

## Lean-verified constructive step

For signed edges x indexed by Fin N and any permutation sigma, define
Phi(v)=x(v)x(sigma(v)). The product of Phi is 1: each edge label occurs
twice. This product compatibility is proved from the map, not assumed.

For any signed charge chi with product -1, Phi must disagree with chi at
some vertex. The repository's unchanged parityViolation is exactly 2 there.
With alpha >= 0, the nonnegative gradient term therefore gives

    exists v, localEnergy alpha beta G chi Phi v >= 2 beta.

Thus for beta > 0 and threshold <= 2 beta there is an active vertex.
InducedParityActivity.lean proves the product identity, forced violation,
and local-energy bound for all N. The generic graph G in the energy is not
asserted to have sigma as its adjacency: the conclusion only uses its
gradient term's nonnegativity, so holds in particular when G is that cycle.

This derives one genuine consequence from explicit incidence compatibility.
It does NOT derive that compatibility from arbitrary SAT machine execution.
The intended N-Frame functional is unchanged.

## Why the current family does not amplify activity

On an odd cycle N >= 3 with all negative charges, put x_i=(-1)^i and use
cyclic successor for sigma. Then Phi_i=-1 for i<N-1 and Phi_(N-1)=+1.
Exactly one site has parity violation 2. Exactly two cycle edges have
squared field difference 4. The local-energy definition counts each of
these directed stored edges at both endpoints. Consequently

    sum_v localEnergy(v) = 16 alpha + 2 beta.

For positive alpha,beta only three vertices have positive local energy,
independently of N. This is an explicit uniform upper construction, not
a claim that it minimizes the full energy for every N. In particular
it rules out an unbounded lower bound on this summed local energy over
all edge-induced fields in this cycle family with fixed coefficients.

The formula for all odd N is the written algebra above, not Lean-verified.
odd_cycle_activity.py checks it exactly for odd N=3,...,1001 with alpha=beta=1
(total 18). It also exhaustively checks the forced violation and energy
bound on 10,920 signed edge assignments over odd sizes 3,...,13.

## Remaining scope

Cycles are not an expander-family test. Nothing here rules out a stronger
result using additional graph geometry or a constrained dynamic trajectory.
No runtime cost, SAT-to-machine map, global log-det coupling, or P versus NP
separation follows from this local activity theorem. Those steps remain open
in this attempt. We do not require a correct decider to search for a zero-
energy field on an inconsistent instance: it can instead establish inconsistency.

Verification:

    lake env lean research-audits/nframe-fixed-invariant/InducedParityActivity.lean
    python3 research-audits/nframe-fixed-invariant/odd_cycle_activity.py

Lean completed with only propext, Classical.choice, and Quot.sound.
