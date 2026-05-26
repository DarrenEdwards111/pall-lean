# Theorem 207 paper→Lean extraction audit (frontier-only)

## Target from pvsnp1
Paper spine (Theorem 92 + Theorem 94 + Theorem 207):
- P-side polynomial upper bound
- NP-side identity-minor/binomial lower bound
- instance-uniform rank-monotone extraction
- contradiction at matched parameters

## Already formalized in current strict route
1. Strict endpoint equivalence:
   - `theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding`
2. Non-vacuous Book-1 low-action obstruction:
   - `lowAction_book1BoundaryObstruction`
   - `universalBook1BoundaryBudgetObstructionLowAction_theorem`
3. Global God-Move capacity surface (calibrated):
   - `GlobalGodMoveCapacityWitness`
   - `book1_obstruction_at_globalGodMoveCapacityExponent`
   - `no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_globalGodMoveCapacity`
4. Canonical restricted unconditional route:
   - `CanonicalStrictGodMovePort`
   - `noCanonicalStrictGodMoveSATDecider_of_canonicalStrictGodMovePort`

## Legacy / quarantined
- Same-sheet legacy bridge remains in:
  - `ComputationalDepthTheorem207SameSheetLegacyPort.lean`
- Old seam axiom remains in legacy module:
  - `GlobalGodMoveGauge.exists_theorem207_semantic_identity_minor_gap_source_transport_data`

## Exact missing frontier for full unconditional strict-class closure
A. Full strict-class global God-Move theorem (coverage/capacity):
- Need theorem of shape:
  - strict observers are uniformly controlled by one global finite-capacity law
  - sufficient to derive `UniversalBook1BoundaryBudgetObstruction enc` non-vacuously

B. Then strict port discharges no-decider unconditionally via existing endpoint:
- `no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_universalBook1Obstruction`

## Practical line-by-line conversion queue from paper claims
1. Formalize one explicit global capacity functional tied to paper’s global God-Move gauge.
2. Prove uniform upper bound on strict live-boundary rank from that functional.
3. Prove matched-parameter NP lower bound dominates that upper bound uniformly.
4. Compose contradiction into no-decider endpoint.

## Current blocker status
- Route plumbing is complete.
- Remaining theorem is load-bearing and equivalent in strength to the separation frontier in this formal model.
