# Uniform bound for the existing signed-field local energy

This attempt keeps localEnergy and parityViolation unchanged. For every
signed charge pattern, signed vertex field Phi(v) in {-1,+1}, and
nonnegative alpha,beta, SignedEnergyCeiling.lean proves

    sum_v localEnergy(v) <= N (4 alpha |E| + 2 beta).

Each squared difference is at most 4, each parity penalty is at most 2,
and the incident edge set is a subset of the stored edge set E. The
bound is intentionally loose: it suffices to establish polynomial scaling
without choosing an edge-orientation or regularity convention.

This is universal over signed charge patterns and signed fields, not just
the single-defect examples. Any field induced by products of signed edges
is signed and hence falls within this bound. It follows that, if N, |E|,
alpha and beta are polynomially bounded in encoded input length, this
instantaneous summed local energy cannot be superpolynomial. Changing the
charge pattern cannot evade that statement within this model.

Scope is essential: the theorem does not bound unrestricted real-valued
fields, an implicitly exponential holographic graph, the coupled gadget
matrix, or the full analytic N-Frame action. It does not show that arbitrary
machines use signed incidence fields. It does not exclude a genuinely
dynamic lower bound; that would need independently proved constraints on
the trajectory and its duration. No universal SAT hardness is asserted.

This closes the particular attempt to obtain a superpolynomial static
local-energy cost by varying signed charges on polynomial-size explicit
graphs. The intended full machine-to-gauge coupling remains unproved.

Verification:

    lake env lean research-audits/nframe-fixed-invariant/SignedEnergyCeiling.lean
