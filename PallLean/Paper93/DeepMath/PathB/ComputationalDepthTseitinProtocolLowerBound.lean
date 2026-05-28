import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFaithfulSpacetimeTseitin

/-!
# Restricted Tseitin protocol lower bound

This file is the first leverage layer after the observer/spacetime reframing.
It does **not** claim a lower bound for arbitrary P-time SAT deciders.  Instead
it isolates a restricted local protocol model where the usual communication
lower-bound mechanism is meaningful:

* a protocol transcript has finitely many local message slots;
* solving the signed Tseitin boundary assigns each independent parity-flip
  direction to a transcript slot that distinguishes it;
* the protocol is faithful only if two directions sharing a slot must have the
  same parity-flip coordinate;
* because the boundary coordinates are injective, the slot assignment is
  injective; hence transcript bandwidth is at least the direction count.

This is the restricted-model theorem the spacetime files were missing.  It is a
real pigeonhole/fooling-set style lower bound for the protocol model, not a
route to unrestricted `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Local protocol model -/

/-- A finite local transcript for a restricted Tseitin boundary protocol. -/
structure LocalProtocolTranscript : Type where
  bandwidth : Nat
  rounds : Nat
  localMemory : Nat

namespace LocalProtocolTranscript

/-- Coarse local spacetime usage of the protocol. -/
def spacetimeVolume (τ : LocalProtocolTranscript) : Nat :=
  τ.rounds * τ.localMemory

end LocalProtocolTranscript

/-- A restricted local Tseitin protocol realization of a signed parity-flip
boundary.

The `slotOf` field says which transcript slot carries the information needed
for a direction.  The `collision_preserves_parityCoordinate` field is the
faithfulness/fooling-set condition: if two independent directions are routed
through the same slot, then the transcript cannot distinguish them, so they must
have the same parity-flip coordinate.  For an injectively labelled Tseitin
boundary this forces distinct directions to use distinct slots. -/
structure LocalTseitinProtocolRealization
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  transcript : LocalProtocolTranscript
  slotOf : Fin T.coverage.directionCount -> Fin transcript.bandwidth
  solvesBoundary : Prop
  solvesBoundary_cert : solvesBoundary
  collision_preserves_parityCoordinate :
    forall d e : Fin T.coverage.directionCount,
      slotOf d = slotOf e ->
        T.parityFlipCoordinate d = T.parityFlipCoordinate e

/-- Core protocol lower bound: any faithful local protocol solving the boundary
has transcript bandwidth at least the number of independent directions. -/
theorem directionCount_le_protocolBandwidth
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (P : LocalTseitinProtocolRealization T) :
    T.coverage.directionCount <= P.transcript.bandwidth := by
  have hcard :
      Fintype.card (Fin T.coverage.directionCount) <=
        Fintype.card (Fin P.transcript.bandwidth) :=
    Fintype.card_le_of_injective P.slotOf (by
      intro d e hslot
      apply T.parityFlipCoordinate_injective
      exact P.collision_preserves_parityCoordinate d e hslot)
  simpa [Fintype.card_fin] using hcard

/-- A bounded protocol cannot solve a boundary whose independent direction count
exceeds the available transcript bandwidth. -/
theorem no_localProtocolRealization_of_bandwidthGap
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (bandwidthLimit : Nat)
    (hgap : bandwidthLimit < T.coverage.directionCount) :
    Not (exists P : LocalTseitinProtocolRealization T,
      P.transcript.bandwidth <= bandwidthLimit) := by
  rintro ⟨P, hbw⟩
  have hdir : T.coverage.directionCount <= P.transcript.bandwidth :=
    directionCount_le_protocolBandwidth P
  exact Nat.not_lt_of_ge (Nat.le_trans hdir hbw) hgap

/-! ## Independent asymptotic family consequence -/

/-- A local protocol boundary at a selected independent asymptotic scale. -/
structure LocalProtocolBoundaryAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1)
    (bandwidthLimit : Nat) : Prop where
  no_bounded_local_protocol :
    Not (exists P : LocalTseitinProtocolRealization
      (F.boundaryAt M hM n hn),
        P.transcript.bandwidth <= bandwidthLimit)

/-- Independent asymptotic Tseitin boundary gives a restricted local-protocol
lower bound whenever the direction count exceeds the protocol bandwidth limit.

This is the leverage statement: a genuine restricted theorem, not an
unrestricted physical/P-observer claim. -/
theorem localProtocolBoundaryAt_of_independentDirectionGap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1)
    (bandwidthLimit : Nat)
    (hgap : bandwidthLimit < F.directionCountAt n hn) :
    LocalProtocolBoundaryAt F M hM n hn bandwidthLimit where
  no_bounded_local_protocol := by
    have hgap' :
        bandwidthLimit <
          (F.boundaryAt M hM n hn).coverage.directionCount := by
      simpa [IndependentAsymptoticSignedTseitinExpanderFamily.boundaryAt,
        IndependentAsymptoticSignedTseitinExpanderFamily.directionCountAt,
        IndependentSignedTseitinExpanderScale.toParityFlipBoundary,
        SignedTseitinExpanderScale.toParityFlipBoundary,
        SignedTseitinExpanderScale.toCoverage] using hgap
    exact no_localProtocolRealization_of_bandwidthGap
      (F.boundaryAt M hM n hn) bandwidthLimit hgap'

/-! ## Relation to faithful spacetime boundary -/

/-- A P-class local observer's lightcone is a protocol bandwidth limit. -/
abbrev ObserverLightconeBandwidthLimit
    (P : PClassLocalPhysicalObserver) : Nat :=
  P.observer.budget.localityLightconeLimit

/-- Restricted protocol lower bound at the observer's lightcone scale.

This is the restricted-model counterpart to the faithful spacetime boundary:
it says there is no faithful local protocol whose transcript fits inside the
observer's lightcone. -/
theorem no_lightconeBoundedProtocol_of_independentAsymptoticGap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1)
    (hgap : ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn) :
    Not (exists P : LocalTseitinProtocolRealization
      (F.boundaryAt M hM n hn),
        P.transcript.bandwidth <= ObserverLightconeBandwidthLimit Pobs) :=
  (localProtocolBoundaryAt_of_independentDirectionGap
    F M hM n hn (ObserverLightconeBandwidthLimit Pobs) hgap).no_bounded_local_protocol

/-! ## Kernel-only axiom trace -/

#print axioms directionCount_le_protocolBandwidth
#print axioms no_localProtocolRealization_of_bandwidthGap
#print axioms localProtocolBoundaryAt_of_independentDirectionGap
#print axioms no_lightconeBoundedProtocol_of_independentAsymptoticGap

end PallLean.Paper93.DeepMath.PathB
