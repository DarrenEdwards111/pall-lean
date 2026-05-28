import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLocalSpacetimeChannel

/-!
# Faithful spacetime Tseitin boundary

This file fixes the definedness bug in the unrestricted spacetime payload.

The earlier `TseitinExpanderCommunicationPrinciple` quantified over all
`PhysicalBoundaryRealization`s.  That is too broad: the raw physical
realization type permits an empty trace with `realizesBoundary := True`, so a
positive-direction communication lower bound cannot hold for every raw
realization.

The corrected statement is model-restricted.  A *faithful local realization*
is a physical realization together with a local direction-channel trace.  This
excludes the empty-trace artifact by structure: if the boundary has positive
direction count and the trace has zero bandwidth, there is no map
`Fin directionCount -> Fin 0`.

This is a restricted local-protocol lower bound, not classical `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Faithful local realizations -/

/-- A model-faithful local realization of a signed Tseitin parity-flip
boundary.

It is not just a raw trace plus an arbitrary `Prop`; it includes the local
direction channel that reads parity-flip coordinates.  This is the restricted
protocol model against which the spacetime lower bound is meaningful. -/
structure FaithfulLocalBoundaryRealization
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  physical : PhysicalBoundaryRealization T
  channel : LocalDirectionChannelTrace T physical

/-- Observer `O` can faithfully and locally realize boundary `T` if it has a
faithful local realization whose underlying physical trace fits the local
spacetime budget. -/
def CanFaithfullyLocallyRealizeBoundary
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop :=
  exists R : FaithfulLocalBoundaryRealization T,
    WithinLocalSpacetimeBudget O R.physical

/-- A faithful local realization forces the direction count to fit inside the
realization's bandwidth. -/
theorem directionCount_le_bandwidth_of_faithfulLocalRealization
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : FaithfulLocalBoundaryRealization T) :
    T.coverage.directionCount <= R.physical.usage.bandwidth :=
  directionCount_le_bandwidth_of_embedding
    (directionCommunicationEmbedding_of_localChannelTrace R.channel)

/-- If the P-observer lightcone is smaller than the boundary direction count,
then no faithful local realization can fit in that observer's local spacetime
budget. -/
theorem not_canFaithfullyLocallyRealizeBoundary_of_lightconeGap
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (hgap : O.budget.localityLightconeLimit < T.coverage.directionCount) :
    Not (CanFaithfullyLocallyRealizeBoundary O T) := by
  rintro ⟨R, hbudget⟩
  have hdir :
      T.coverage.directionCount <= R.physical.usage.bandwidth :=
    directionCount_le_bandwidth_of_faithfulLocalRealization R
  have hbw :
      R.physical.usage.bandwidth <= O.budget.localityLightconeLimit :=
    realizationCommunication_le_lightcone O R.physical hbudget
  exact Nat.not_lt_of_ge (Nat.le_trans hdir hbw) hgap

/-! ## Faithful observer boundary -/

/-- A nonlocal/NP-class observer with the stipulated ability to realize
faithful local-channel boundary protocols.  This is a restricted observer-class
hypothesis, not a classical complexity theorem. -/
structure NPClassNonlocalFaithfulBoundaryObserver : Type where
  np_boundary_channel : Prop
  np_boundary_channel_cert : np_boundary_channel
  realizes_faithful_signed_tseitin_boundaries :
    forall {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
      (T : SignedTseitinParityFlipBoundary enc M n),
        Nonempty (FaithfulLocalBoundaryRealization T)

/-- Faithful local-spacetime observer boundary at one signed Tseitin instance. -/
structure FaithfulSpacetimeObserverBoundaryAt
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalFaithfulBoundaryObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop where
  p_observer_cannot_faithfully_locally_realize :
    Not (CanFaithfullyLocallyRealizeBoundary P.observer T)
  np_observer_can_faithfully_realize :
    Nonempty (FaithfulLocalBoundaryRealization T)

/-- Main faithful spacetime boundary theorem. -/
theorem faithfulSpacetimeObserverBoundaryAt_of_lightconeGap
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalFaithfulBoundaryObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n)
    (hgap : P.observer.budget.localityLightconeLimit <
      T.coverage.directionCount) :
    FaithfulSpacetimeObserverBoundaryAt P N T where
  p_observer_cannot_faithfully_locally_realize :=
    not_canFaithfullyLocallyRealizeBoundary_of_lightconeGap
      P.observer T hgap
  np_observer_can_faithfully_realize :=
    N.realizes_faithful_signed_tseitin_boundaries T

/-! ## Independent asymptotic signed Tseitin families -/

/-- A scale whose counterfactual directions are independent at the input-pair
level.

This prevents the cosmetic one-edge padding failure mode: repeating the same
SAT/UNSAT pair with fresh tags cannot satisfy `inputPair_injective` once there
are two distinct directions. -/
structure IndependentSignedTseitinExpanderScale
    (enc : SignedFormulaEncoding) (n : Nat) : Type where
  scale : SignedTseitinExpanderScale enc n
  inputPair_injective :
    Function.Injective
      (fun d : Fin scale.directionCount =>
        (scale.positiveInput d, scale.negativeInput d))

namespace IndependentSignedTseitinExpanderScale

/-- The independent scale produces the same parity-flip boundary as its
underlying signed Tseitin expander scale. -/
def toParityFlipBoundary
    {enc : SignedFormulaEncoding} {n : Nat}
    (S : IndependentSignedTseitinExpanderScale enc n)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M) :
    SignedTseitinParityFlipBoundary enc M n :=
  S.scale.toParityFlipBoundary M hM

/-- Distinct independent directions cannot reuse the same input pair. -/
theorem inputPair_ne_of_ne
    {enc : SignedFormulaEncoding} {n : Nat}
    (S : IndependentSignedTseitinExpanderScale enc n)
    {d e : Fin S.scale.directionCount}
    (hne : d ≠ e) :
    (S.scale.positiveInput d, S.scale.negativeInput d) ≠
      (S.scale.positiveInput e, S.scale.negativeInput e) := by
  intro hpair
  exact hne (S.inputPair_injective hpair)

end IndependentSignedTseitinExpanderScale

/-- An asymptotic signed Tseitin/Mikoshi family with genuine independent input
pairs at every scale. -/
structure IndependentAsymptoticSignedTseitinExpanderFamily
    (enc : SignedFormulaEncoding) : Type where
  scale :
    forall n : Nat, n >= 1 ->
      IndependentSignedTseitinExpanderScale enc n
  unboundedDirections : Prop
  unboundedDirections_cert : unboundedDirections
  expanderFamilyCertificate : Prop
  expanderFamilyCertificate_cert : expanderFamilyCertificate

namespace IndependentAsymptoticSignedTseitinExpanderFamily

/-- Direction count at a scale. -/
def directionCountAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (n : Nat)
    (hn : n >= 1) : Nat :=
  (F.scale n hn).scale.directionCount

/-- Boundary at a scale for a signed SAT decider. -/
def boundaryAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1) :
    SignedTseitinParityFlipBoundary enc M n :=
  (F.scale n hn).toParityFlipBoundary M hM

end IndependentAsymptoticSignedTseitinExpanderFamily

/-- Faithful spacetime observer boundary for an independent asymptotic
Tseitin/Mikoshi scale whose direction count exceeds the P-observer lightcone. -/
theorem faithfulSpacetimeObserverBoundaryAt_of_independentAsymptoticLightconeGap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalFaithfulBoundaryObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      P.observer.budget.localityLightconeLimit <
        F.directionCountAt n hn) :
    FaithfulSpacetimeObserverBoundaryAt P N
      (F.boundaryAt M hM n hn) := by
  have hgap' :
      P.observer.budget.localityLightconeLimit <
        (F.boundaryAt M hM n hn).coverage.directionCount := by
    simpa [IndependentAsymptoticSignedTseitinExpanderFamily.boundaryAt,
      IndependentAsymptoticSignedTseitinExpanderFamily.directionCountAt,
      IndependentSignedTseitinExpanderScale.toParityFlipBoundary,
      SignedTseitinExpanderScale.toParityFlipBoundary,
      SignedTseitinExpanderScale.toCoverage] using hgap
  exact faithfulSpacetimeObserverBoundaryAt_of_lightconeGap
    P N (F.boundaryAt M hM n hn) hgap'

/-! ## Kernel-only axiom trace -/

#print axioms directionCount_le_bandwidth_of_faithfulLocalRealization
#print axioms not_canFaithfullyLocallyRealizeBoundary_of_lightconeGap
#print axioms faithfulSpacetimeObserverBoundaryAt_of_lightconeGap
#print axioms IndependentSignedTseitinExpanderScale.inputPair_ne_of_ne
#print axioms faithfulSpacetimeObserverBoundaryAt_of_independentAsymptoticLightconeGap

end PallLean.Paper93.DeepMath.PathB
