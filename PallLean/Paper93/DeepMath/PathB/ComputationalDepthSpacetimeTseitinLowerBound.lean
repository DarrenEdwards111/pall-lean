import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpacetimeObserverBoundary

/-!
# Spacetime lower-bound reducer for signed Tseitin/Mikoshi boundaries

The energy route is blocked by reversible computation.  The stronger physics
axis is locality: a local observer has a finite communication lightcone.  This
file records the first honest lower-bound reducer on that axis.

If every realization of a signed Tseitin parity-flip boundary must inject its
independent parity-flip directions into distinct local communication slots,
then every realization uses at least as much communication bandwidth as the
number of directions.  A P-class local observer whose lightcone capacity is
below that direction count cannot locally realize the boundary.

This still does not prove classical `P ≠ NP`.  The load-bearing asymptotic
payload is the communication-injection theorem for an actual signed
Tseitin/Mikoshi expander family.  The point of this file is to make that
payload precise and immediately reusable by the spacetime observer theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Direction-to-communication embeddings -/

/-- A realization communicates each independent signed-Tseitin direction in a
distinct local bandwidth slot.

This is the locality payload.  It is intentionally stronger and more concrete
than a generic resource-cost assertion: a direction is counted only when it is
assigned to a distinct physical communication slot of the realization trace. -/
structure DirectionCommunicationEmbedding
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (R : PhysicalBoundaryRealization T) : Type where
  slotOf : Fin T.coverage.directionCount -> Fin R.usage.bandwidth
  slotOf_injective : Function.Injective slotOf

/-- A realization that injects all directions into bandwidth slots must have
at least as many bandwidth slots as signed-Tseitin directions. -/
theorem directionCount_le_bandwidth_of_embedding
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    {R : PhysicalBoundaryRealization T}
    (E : DirectionCommunicationEmbedding T R) :
    T.coverage.directionCount <= R.usage.bandwidth := by
  have hcard :
      Fintype.card (Fin T.coverage.directionCount) <=
        Fintype.card (Fin R.usage.bandwidth) :=
    Fintype.card_le_of_injective E.slotOf E.slotOf_injective
  simpa [Fintype.card_fin] using hcard

/-- Every physical realization of the boundary communicates the independent
directions through distinct local bandwidth slots.

This is the concrete theorem an asymptotic signed Tseitin/Mikoshi locality
argument must prove.  It does not assert hardness by definition; it supplies a
physical injection from semantic directions to local communication slots. -/
structure EveryRealizationCommunicatesDirections
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  embedding :
    forall R : PhysicalBoundaryRealization T,
      DirectionCommunicationEmbedding T R

/-! ## Communication lower bound to spacetime observer boundary -/

/-- Direction communication gives a local-spacetime lower bound with the
required communication equal to the signed-Tseitin direction count. -/
def localSpacetimeLowerBound_of_directionCommunication
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (Hcomm : EveryRealizationCommunicatesDirections T)
    (hgap : O.budget.localityLightconeLimit < T.coverage.directionCount) :
    LocalSpacetimeBoundaryLowerBound O T where
  requiredSpacetimeVolume := 0
  requiredCommunication := T.coverage.directionCount
  every_realization_requires_spacetime := by
    intro R
    exact Nat.zero_le (realizationSpacetimeVolume R)
  every_realization_requires_communication := by
    intro R
    exact directionCount_le_bandwidth_of_embedding (Hcomm.embedding R)
  local_gap := Or.inr hgap

/-- If every realization has to communicate all independent directions, and
the observer's local lightcone is smaller than the direction count, the local
observer cannot realize the boundary. -/
theorem not_canLocallyRealizeBoundary_of_directionCommunicationGap
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (Hcomm : EveryRealizationCommunicatesDirections T)
    (hgap : O.budget.localityLightconeLimit < T.coverage.directionCount) :
    Not (CanLocallyRealizeBoundary O T) :=
  not_canLocallyRealizeBoundary_of_spacetimeLowerBound O
    (localSpacetimeLowerBound_of_directionCommunication O T Hcomm hgap)

/-- P-class/NP-class observer boundary from direction communication and a
local lightcone gap. -/
theorem spacetimeObserverBoundaryAt_of_directionCommunicationGap
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (Hcomm : EveryRealizationCommunicatesDirections T)
    (hgap : P.observer.budget.localityLightconeLimit <
      T.coverage.directionCount) :
    SpacetimeObserverBoundaryAt P N T :=
  spacetimeObserverBoundaryAt_of_localLowerBound P N
    (localSpacetimeLowerBound_of_directionCommunication
      P.observer T Hcomm hgap)

/-! ## Concrete one-edge specialization -/

/-- One-edge sanity specialization of the direction-communication reducer.

For real scaling this seed must be replaced by an asymptotic signed
Tseitin/Mikoshi family whose direction count exceeds the observer's local
lightcone capacity. -/
theorem oneEdgeTseitin_spacetimeObserverBoundary_of_directionCommunicationGap
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M)
    (Hcomm :
      EveryRealizationCommunicatesDirections
        (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM))
    (hgap :
      P.observer.budget.localityLightconeLimit <
        (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM).coverage.directionCount) :
    SpacetimeObserverBoundaryAt P N
      (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM) :=
  spacetimeObserverBoundaryAt_of_directionCommunicationGap
    P N (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM) Hcomm hgap

/-! ## Kernel-only axiom trace -/

#print axioms directionCount_le_bandwidth_of_embedding
#print axioms localSpacetimeLowerBound_of_directionCommunication
#print axioms not_canLocallyRealizeBoundary_of_directionCommunicationGap
#print axioms spacetimeObserverBoundaryAt_of_directionCommunicationGap
#print axioms oneEdgeTseitin_spacetimeObserverBoundary_of_directionCommunicationGap

end PallLean.Paper93.DeepMath.PathB
