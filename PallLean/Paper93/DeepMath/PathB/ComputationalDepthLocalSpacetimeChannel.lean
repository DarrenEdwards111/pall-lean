import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAsymptoticTseitinSpacetime

/-!
# Local spacetime channel semantics for signed Tseitin boundaries

The previous spacetime files isolated the payload:

`EveryRealizationCommunicatesDirections T`.

This file lowers that payload by one semantic layer.  Instead of assuming an
injective map from directions to communication slots, we model a local channel
trace with a slot assignment and a collision rule:

* if two parity-flip directions are read through the same local slot, then the
  slot semantics identify their parity-flip coordinates;
* the signed Tseitin boundary already carries injective parity-flip
  coordinates;
* therefore different directions cannot share a slot.

This is still not a proof of the asymptotic expander lower bound.  It is the
structured local-channel theorem that such a lower bound should instantiate.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Local channel traces -/

/-- A local communication-channel trace for one realization of a signed
Tseitin parity-flip boundary.

`slotReadsParityCoordinate` is a named semantic certificate: the local slot is
actually being used to read the parity-flip coordinate, not an arbitrary label.
The proof uses the stronger collision law, which is the part a concrete local
spacetime model must justify. -/
structure LocalDirectionChannelTrace
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (R : PhysicalBoundaryRealization T) : Type where
  slotOf : Fin T.coverage.directionCount -> Fin R.usage.bandwidth
  slotReadsParityCoordinate : Prop
  slotReadsParityCoordinate_cert : slotReadsParityCoordinate
  collision_preserves_parityCoordinate :
    forall d e : Fin T.coverage.directionCount,
      slotOf d = slotOf e ->
        T.parityFlipCoordinate d = T.parityFlipCoordinate e

/-- A local channel trace induces the injective direction-to-communication
embedding needed by the spacetime reducer. -/
def directionCommunicationEmbedding_of_localChannelTrace
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    {R : PhysicalBoundaryRealization T}
    (C : LocalDirectionChannelTrace T R) :
    DirectionCommunicationEmbedding T R where
  slotOf := C.slotOf
  slotOf_injective := by
    intro d e hslot
    apply T.parityFlipCoordinate_injective
    exact C.collision_preserves_parityCoordinate d e hslot

/-- Every realization has a local direction-channel trace. -/
structure EveryRealizationHasLocalDirectionChannel
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  traceOf :
    forall R : PhysicalBoundaryRealization T,
      LocalDirectionChannelTrace T R

/-- Local channel traces discharge the previous communication-injection
payload. -/
def everyRealizationCommunicatesDirections_of_localDirectionChannel
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : EveryRealizationHasLocalDirectionChannel T) :
    EveryRealizationCommunicatesDirections T where
  embedding := by
    intro R
    exact directionCommunicationEmbedding_of_localChannelTrace (H.traceOf R)

/-! ## Asymptotic family principle -/

/-- Local-channel version of the asymptotic Tseitin communication principle.

This is the target for a concrete expander/locality theorem: for every scale
and every realization of the induced boundary, there is a local channel trace
whose collisions preserve parity-flip coordinates. -/
structure TseitinExpanderLocalChannelPrinciple
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc) : Type where
  hasLocalChannel :
    forall (M : DTM) (hM : SignedDTMDecidesSAT enc M)
      (n : Nat) (hn : n >= 1),
        EveryRealizationHasLocalDirectionChannel
          (F.boundaryAt M hM n hn)

/-- A local-channel principle implies the communication principle used by the
asymptotic spacetime theorem. -/
def TseitinExpanderLocalChannelPrinciple.toCommunicationPrinciple
    {enc : SignedFormulaEncoding}
    {F : AsymptoticSignedTseitinExpanderFamily enc}
    (H : TseitinExpanderLocalChannelPrinciple F) :
    TseitinExpanderCommunicationPrinciple F where
  communicatesDirections := by
    intro M hM n hn
    exact everyRealizationCommunicatesDirections_of_localDirectionChannel
      (H.hasLocalChannel M hM n hn)

/-- A scale at which the family direction count exceeds a P-observer's local
lightcone capacity. -/
structure AsymptoticTseitinLightconeGap
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc)
    (P : PClassLocalPhysicalObserver) : Type where
  n : Nat
  hn : n >= 1
  lightcone_gap :
    P.observer.budget.localityLightconeLimit < F.directionCountAt n hn

/-- Local channel semantics plus a lightcone gap gives the spacetime observer
boundary at the selected asymptotic scale. -/
theorem spacetimeObserverBoundaryAt_of_asymptoticTseitinLocalChannelGap
    {enc : SignedFormulaEncoding}
    (F : AsymptoticSignedTseitinExpanderFamily enc)
    (H : TseitinExpanderLocalChannelPrinciple F)
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (G : AsymptoticTseitinLightconeGap F P) :
    SpacetimeObserverBoundaryAt P N (F.boundaryAt M hM G.n G.hn) :=
  spacetimeObserverBoundaryAt_of_asymptoticTseitinLightconeGap
    F H.toCommunicationPrinciple P N M hM G.n G.hn G.lightcone_gap

/-! ## Kernel-only axiom trace -/

#print axioms directionCommunicationEmbedding_of_localChannelTrace
#print axioms everyRealizationCommunicatesDirections_of_localDirectionChannel
#print axioms TseitinExpanderLocalChannelPrinciple.toCommunicationPrinciple
#print axioms spacetimeObserverBoundaryAt_of_asymptoticTseitinLocalChannelGap

end PallLean.Paper93.DeepMath.PathB
