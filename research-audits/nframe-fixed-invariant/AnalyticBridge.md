# Actual analytic N-Frame barrier: step-cost bridge

2026-09-09. No production invariant replaced. No SAT separation.

The repository already has two distinct implementations: Concrete/FullLagrangianFixed uses the bounded structural rank penalty; DeepMath/NFrame/SNF uses the analytic single-minor barrier -log(det A). The previous zero-gauge minimization result must not be applied to the latter without a separate argument.

For positive determinants, the exact analytic drop is

    B(A_t) - B(A_{t+1}) = log(det(A_{t+1})/det(A_t)).

Consequently det(A_{t+1})/det(A_t) <= exp(r) suffices for a drop of at most r. This is a condition on actual consecutive matrices, not a bound derived from a Turing-machine transition. The new Lean file verifies the identity and conditional implication using the existing barrier definition unchanged.

For a sum over a fixed minor family, sum these identities; with nonnegative weights, weighted per-minor bounds give a weighted total bound. Choosing a minor family or multiplicities from SAT hardness is not justified by this algebra.

The full S_NF action also includes the coordinate edge term and sign/mismatch term. Bounding the barrier drop alone does not bound the full action drop. Nor does positivity of det imply the determinant ratio bound: consecutive positive determinants can have an arbitrarily large ratio.

Domain issue: Lean's real logarithm is totalized with log(0)=0. Therefore the raw real-valued barrier returns zero at singular matrices. Its divergence theorem explicitly concerns approach through strictly positive determinants. Minimization and trajectories must stay in the intended domain or use an extended-valued domain-enforcing action. A positive-definite-domain type can enforce the condition, but proving that the machine's gauge matrices satisfy it is separate mathematics, not obtained by inserting it as a field.

Still needed: construct A_t (and each selected minor) from the actual machine-to-gauge map, prove domain preservation, derive a determinant-ratio bound per machine step, control the other action terms, and derive SAT-specific initial/terminal behavior. None is assumed proved here.
