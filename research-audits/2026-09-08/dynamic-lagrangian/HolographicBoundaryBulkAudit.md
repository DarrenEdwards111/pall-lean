# Boundary-to-bulk dynamic-rank audit

2026-09-08. Scope: the user's intended holographic reconstruction, not the earlier kinetic tape mask.

## Located implementation

In `pall-lean-holographic/PallLean/Paper93/DeepMath/PathC/`:

- `PiPlusHolographicBoundaryBulkPivot.lean` defines `HolographicBoundaryLayer` and `HolographicBulkLayer`. Their ranks are supplied natural numbers. The 2D/3D/4D distinction is an enumerated dimension tag, not a geometric space or reconstruction law.
- `PiPlusHolographicFaithfulLiftSemantics.lean` defines `BoundaryBulkFaithfulDecoder` as an injection `Fin bulk.rank → Fin (liftCost boundary.rank)`. This codes bulk witness indices; it is not an executable boundary-state-to-bulk-state reconstruction map.
- `exists_decoder_iff_faithful_boundary_to_bulk` proves decoder existence equivalent to `bulk.rank ≤ liftCost boundary.rank`.
- `HolographicBoundaryBulkDecoderPivotData` still requires boundary upper bound, bulk lower bound, faithful decoder for SAT deciders, and a lift-capacity gap as fields.

## Consequence

The user's intended boundary/bulk interpretation is explicitly present. It is not yet derived from geometry or the full Lagrangian in these definitions. Repackaging a cardinal inequality as an injection does not establish that SAT correctness forces reconstruction, nor does `liftCost` currently measure executed machine operations.

## Concrete construction needed

Specify boundary states, bulk states, and a reconstruction map R with a proved relationship to the N-Frame action. For a machine transition step and boundary encoding E, derive the corresponding bulk evolution, rather than freely supplying a trajectory. Define rank on the resulting bulk object, and prove a bound in terms of actual runtime and encoded input length. Separately prove that SAT correctness forces the required rank on this same object.

The first missing computational claim is not merely injectivity: a SAT decider must be shown to require the relevant bulk reconstruction or an equivalent operation. Deciding one Boolean answer does not by definition reconstruct all witnesses. A large implicit bulk alone supplies no runtime lower bound.

No new reconstruction or SAT lower-bound proof was obtained in this audit. No replacement invariant is asserted to be the user's intended one.

## Follow-up: necessity and cost (Lean checked)

`ReconstructionNecessity.lean` proves that exact continuation-answer factorization through a boundary encoding forces different codes for inputs separated by some continuation. A finite pairwise-separated family therefore has at most `2^bits` members when boundary codes have `bits` Boolean coordinates. Given the additional machine-specific bound `bits ≤ initial + rate * time`, its cardinality is at most `2^(initial + rate*time)`.

This is a conditional code-capacity theorem, not a SAT time lower bound or a matrix-rank theorem. In a machine application, factorization must account for all later input access, and the space/time premise must be proved for that machine model. Bulk witness labels are not automatically pairwise distinguishable input continuations. The logarithmic bit cost of distinguishing labels must not be substituted for a linear-algebra rank charge, or vice versa.

The file also proves a simple exact-decision-without-reconstruction counterexample on a two-element domain. Its scope is logical: Boolean correctness alone does not entail lossless reconstruction. It does not refute the possibility of a stronger SAT-specific necessity theorem.

Verification: `lake env lean ../research-audits/dynamic-lagrangian/ReconstructionNecessity.lean` exited successfully; printed theorem dependencies contain only standard axioms. The desired full reconstruction theorem remains unproved.
