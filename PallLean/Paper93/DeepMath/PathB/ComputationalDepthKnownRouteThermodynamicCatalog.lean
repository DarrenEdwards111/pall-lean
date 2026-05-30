import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermodynamicObserverBarrier

/-!
# Thermodynamic catalog for the known N-frame/God-Move routes

This file records the finite-scope claim requested in the discussion:

* not "all possible future proof methods";
* only the route families already audited in this repository;
* for that finite known catalog, any boundary-closing bridge either exceeds the
  thermodynamic/P-observer budget or exposes the already-isolated frontier
  obstruction.

The catalog is intentionally explicit.  A new route is covered only after it is
added as a constructor and supplied with an audit registry theorem.  This keeps
the statement method-relative and prevents it from becoming an absolute
unprovability claim.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Known route families -/

/-- The finite list of N-frame/God-Move route families currently audited in
Path B.  This is not a universe of all possible proof techniques. -/
inductive KnownNFrameRouteFamily : Type
  | spdpGodMoveRank
  | strictLiveBoundaryPort
  | runIndexedEKP
  | capacityGravityMass
  | groundedCookLevinBulk
  | counterfactualTriAspect
  | remainderTriAspect
  | observerBoundarySchema
  deriving DecidableEq, Repr

/-- The kind of obstruction isolated for each known route family. -/
inductive KnownNFrameRouteObstruction : Type
  | endpointEquivalent
  | runWindowCountingBound
  | wrongResourceAxis
  | groundedSameObjectRankSandwich
  | semanticTransportFrontier
  | remainderTransportFrontier
  | observerBoundaryFrontier
  deriving DecidableEq, Repr

/-- Paper-facing classification of the currently known route families. -/
def KnownNFrameRouteFamily.defaultObstruction :
    KnownNFrameRouteFamily -> KnownNFrameRouteObstruction
  | .spdpGodMoveRank => .endpointEquivalent
  | .strictLiveBoundaryPort => .endpointEquivalent
  | .runIndexedEKP => .runWindowCountingBound
  | .capacityGravityMass => .wrongResourceAxis
  | .groundedCookLevinBulk => .groundedSameObjectRankSandwich
  | .counterfactualTriAspect => .semanticTransportFrontier
  | .remainderTriAspect => .remainderTransportFrontier
  | .observerBoundarySchema => .observerBoundaryFrontier

/-! ## Audit registry for a finite known-route universe -/

/-- A registry saying that the thermodynamic observer frame under discussion is
restricted to known, audited route families.

The field `everyClosureEitherExceedsOrExposes` is the only load-bearing audit:
for every bridge in this *known-route universe*, closure either exceeds the
finite observer budget or exposes the obstruction already assigned by the
audit.

This is deliberately weaker than a universal statement about all possible
proof techniques. -/
structure KnownRouteAuditRegistry
    (enc : SignedFormulaEncoding)
    (F : ThermodynamicPObserverFrame enc) : Type where
  familyOf : ThermodynamicInternalBridge enc F -> KnownNFrameRouteFamily
  obstructionOf :
    KnownNFrameRouteFamily -> KnownNFrameRouteObstruction
  obstruction_matches_family :
    forall family : KnownNFrameRouteFamily,
      obstructionOf family = family.defaultObstruction
  ExposesKnownFrontier : ThermodynamicInternalBridge enc F -> Prop
  everyClosureEitherExceedsOrExposes :
    forall B : ThermodynamicInternalBridge enc F,
      B.closesBoundary ->
        ExceedsThermodynamicBudget B \/ ExposesKnownFrontier B

namespace KnownRouteAuditRegistry

/-- A known-route audit registry is exactly a thermodynamic bridge barrier with
the frontier predicate specialized to the known-route obstruction. -/
def toThermodynamicBridgeBarrier
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (R : KnownRouteAuditRegistry enc F) :
    ThermodynamicBridgeBarrier enc F where
  ExposesNPFrontier := R.ExposesKnownFrontier
  everyClosureEitherExceedsOrExposes := R.everyClosureEitherExceedsOrExposes

/-- Uniform barrier for the finite known-route catalog:
no clean bridge inside the observer's thermodynamic budget closes. -/
theorem thermodynamicUnprovability_for_knownRouteCatalog
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (R : KnownRouteAuditRegistry enc F) :
    ThermodynamicObserverRelativeUnprovability
      F R.toThermodynamicBridgeBarrier :=
  thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
    F R.toThermodynamicBridgeBarrier

/-- Single-bridge readout for the finite catalog. -/
theorem noClosure_of_knownRouteCatalog_inBudget_clean
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (R : KnownRouteAuditRegistry enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B)
    (hclean : Not (R.ExposesKnownFrontier B)) :
    Not B.closesBoundary :=
  noClosure_of_withinBudget_cleanThermodynamicBridge
    R.toThermodynamicBridgeBarrier B hbudget hclean

/-- Contrapositive readout: any known-route bridge that closes while staying
inside budget exposes the audited frontier obstruction. -/
theorem exposesKnownFrontier_of_knownRouteCatalog_inBudget_closes
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (R : KnownRouteAuditRegistry enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B)
    (hclose : B.closesBoundary) :
    R.ExposesKnownFrontier B :=
  exposesNPFrontier_of_withinBudget_closes
    R.toThermodynamicBridgeBarrier B hbudget hclose

end KnownRouteAuditRegistry

/-! ## Route-file anchors

The route-specific audits are intentionally not imported here.  Some legacy
route files live next to archived unsafe wrappers, and importing the whole
legacy chain would make this clean catalog depend on those wrappers.  The
finite constructors above are the formal scope of this file; the corresponding
route audits live in:

* `MinimizerSPDPFieldsFrontier.lean`
  (`minimizerDerivedSPDPFields_iff_no_bounded_sat_decider`);
* `ComputationalDepthTheorem207StrictPort.lean`
  (`theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding`);
* `ComputationalDepthEKPSemanticForceAudit.lean`
  (`runIndexedEKPForce_iff_no_DTMDecidesSATWithEncoding`);
* `ComputationalDepthIrreducibleMassGravity.lean`
  (`noCanonicalSATDecisionInP_of_irreducibleMassGravityObstruction`);
* `ComputationalDepthGroundedCookLevinObstruction.lean`
  (`no_theorem207Witness_grounded_to_actualCookLevinBulk`);
* `ComputationalDepthRemainderTriAspectSemanticInterface.lean`
  (`sheetEssentialityAfterDeletion_of_canonicalSignedRemainderBridge`).

Keeping those as references rather than imports makes the catalog a small,
kernel-clean scope theorem: once a concrete observer frame is declared to range
only over these audited known routes, the thermodynamic barrier applies.
-/

/-! ## Kernel-only axiom trace -/

#print axioms KnownRouteAuditRegistry.thermodynamicUnprovability_for_knownRouteCatalog
#print axioms KnownRouteAuditRegistry.noClosure_of_knownRouteCatalog_inBudget_clean
#print axioms KnownRouteAuditRegistry.exposesKnownFrontier_of_knownRouteCatalog_inBudget_closes

end PallLean.Paper93.DeepMath.PathB
