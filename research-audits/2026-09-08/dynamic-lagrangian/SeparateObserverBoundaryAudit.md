# Separate observer-boundary attempt — 2026-09-08

User interpretation: the P decider and NP verifier each have their own thermodynamic boundary. Do not combine them into a joint boundary or demand witness reconstruction by the decider.

## Existing route found

`ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction.lean` already formalizes this interpretation at `NPVerifierGodEyePerspective`, `PDeciderBoundaryPerspective`, and `AsymmetricDecisionInvariantBridge`. The NP view receives an instance and witness. The P view receives only an instance. The only stated semantic relation is existential acceptance.

The asymmetry is therefore not missing from the repository. However, the NP observer's `verifierSound` and `ramanujanWitnessGeometry` fields are supplied propositions with proofs, not concrete verification or geometric laws. The P observer's `capacityBits` is supplied with a polynomial bound, not tied by these fields to the cardinality of its boundary.

## Attempted cost derivation

The route's `TowerSpringDecisionPayload` supplies an energy sequence, initial energy, positive service rate and threshold. It requires a large initial load, a bounded per-step discharge, termination discharge under correctness, and a superpolynomial threshold. The generic telescoping argument turns these premises into a time lower bound. None of the inspected definitions constructs these premises from the two observers' machine executions or from `traceEnergy`.

The existing theorem `asymmetricObserverBridge_iff_no_SATDecisionInP` calibrates the universal bridge's strength as exactly the no-polynomial-SAT-decider claim for its model. This equivalence is not a disproof of the approach; it means that constructing the certificate remains the main theorem.

## Thermodynamic route

`ComputationalDepthThermodynamicObserverBarrier.lean` defines energy from a supplied trace as scaled erasures plus active energy. The costs are computed from the trace, but the internal bridge's record does not establish that the trace is an execution of the claimed procedure. Its erasure-free guardrail correctly prevents deriving positive erasure cost without an erasure lower bound.

`ComputationalDepthSpacetimeObserverBoundary.lean` has separate local P and nonlocal NP observer classes. The NP realization ability and the local spacetime lower bound are fields. These are not derivations of ordinary NP verification or of an unrestricted deterministic runtime lower bound.

## Outcome

No separate-observer SAT cost gap was derived. The missing argument is a machine-faithful construction proving large initial cost, limited discharge per actual step, and necessary terminal discharge on the same P execution, while independently modelling witness verification on the NP side. Separate boundaries do not justify any of these premises by themselves. No new conditional separation theorem was added, and no completion is claimed.
