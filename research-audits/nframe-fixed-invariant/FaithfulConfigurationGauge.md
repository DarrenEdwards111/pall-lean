# Configuration-faithful gauge does not by itself force action cost

We retain the repository's analytic S_NF unchanged. For a real configuration code c,
let U(c) = [[1,c],[0,1]] and A(c) = U(c)^T U(c) = [[1,c],[c,c*c+1]].
A(c) is positive definite, has determinant one, and retains c exactly in entry (0,1).
Thus any injective configuration code gives an injective map into this domain.
Natural-number configuration codes can be embedded in the reals by ordinary cast.

For any state transition step, send code(s) to A(code(s)) and its successor to
A(code(step(s))). Holding adjacency, phi and chi fixed, S_NF is constant on this
entire trajectory. Its barrier is -log(1)=0. No state information is discarded.

This is a deliberately explicit test map, NOT a derivation of the intended
holographic God-Move gauge. In particular it does not prove the SAT-minor,
geometric admissibility beyond positive definiteness, locality, finite-precision
cost or physical-realizability requirements. We do not treat exact real arithmetic
as a unit-cost machine model. The argument is about what the abstract action and
injectivity conditions alone imply, not the bit complexity of evaluating a map.

It refines the previous zero-gauge warning: requiring the map to preserve all
configuration information and stay positive definite still does not force a
nonzero action drop. Merely attaching a gauge to every machine configuration
cannot finish the intended derivation. The actual relation tying phi, chi,
adjacency and gadget matrices to computation and SAT structure is essential.

The Lean file proves positivity, determinant one, injectivity, and zero action
drop for every transition under these fixed-field conditions. No universal SAT
lower bound or intended machine-to-holographic-gauge construction is claimed.

Verification:
    lake env lean research-audits/nframe-fixed-invariant/FaithfulConfigurationGauge.lean
