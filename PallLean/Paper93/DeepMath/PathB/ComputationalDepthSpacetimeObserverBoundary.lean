import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPhysicalObserverBoundary

/-!
# Spacetime/locality observer boundary

The energy-only physical boundary is the wrong axis for complexity: Bennett
reversibility blocks Landauer-erasure arguments unless irreversibility is
proved separately.  This file records the sharper physical route:

* a P-class physical observer has bounded time, memory, communication, and
  locality/lightcone capacity;
* a boundary realization consumes spacetime volume (`time * peak memory`) and
  communication/lightcone volume;
* if physics/complexity proves that every realization of a boundary exceeds
  those local-spacetime capacities, then a P-class local observer cannot
  realize it, while an NP-class/nonlocal boundary observer can by hypothesis.

This is still not classical `P ≠ NP`.  The load-bearing theorem is the explicit
`LocalSpacetimeBoundaryLowerBound`; for full SAT that payload is P-vs-NP
strength.  For restricted Mikoshi/Tseitin observer models, it is a legitimate
lower-bound target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Local spacetime budgets -/

/-- A local spacetime observer budget.

`localityFanout` is the maximum amount of boundary communication the observer
can propagate per time tick through its local physical channel. -/
structure LocalSpacetimeBudget : Type where
  timeLimit : Nat
  memoryLimit : Nat
  communicationLimit : Nat
  localityFanout : Nat

namespace LocalSpacetimeBudget

/-- Time-memory spacetime volume available to the observer. -/
def spacetimeVolumeLimit (B : LocalSpacetimeBudget) : Nat :=
  B.timeLimit * B.memoryLimit

/-- Local communication lightcone capacity over the observer's time window. -/
def localityLightconeLimit (B : LocalSpacetimeBudget) : Nat :=
  B.timeLimit * B.localityFanout

end LocalSpacetimeBudget

/-- A local physical observer with bounded spacetime and communication. -/
structure LocalPhysicalObserver : Type where
  budget : LocalSpacetimeBudget

/-- A P-class local physical observer.

The proof uses only the explicit local spacetime budget; the extra fields
state the intended physical class without defining it as "cannot see NP". -/
structure PClassLocalPhysicalObserver : Type where
  observer : LocalPhysicalObserver
  classical_turing_channel : Prop
  classical_turing_channel_cert : classical_turing_channel
  no_oracle_channel : Prop
  no_oracle_channel_cert : no_oracle_channel
  no_hypercomputational_channel : Prop
  no_hypercomputational_channel_cert : no_hypercomputational_channel
  local_causal_propagation : Prop
  local_causal_propagation_cert : local_causal_propagation
  polynomial_spacetime_scaling : Prop
  polynomial_spacetime_scaling_cert : polynomial_spacetime_scaling

/-! ## Local realization predicates -/

/-- A realization fits inside a local spacetime observer's budget. -/
structure WithinLocalSpacetimeBudget
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T) : Prop where
  time_within :
    R.usage.time <= O.budget.timeLimit
  memory_within :
    R.usage.memory <= O.budget.memoryLimit
  communication_within :
    R.usage.bandwidth <= O.budget.communicationLimit
  locality_lightcone_within :
    R.usage.bandwidth <= O.budget.localityLightconeLimit

/-- Observer `O` can locally realize boundary `T` within its spacetime budget. -/
def CanLocallyRealizeBoundary
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop :=
  exists R : PhysicalBoundaryRealization T,
    WithinLocalSpacetimeBudget O R

/-- A nonlocal/NP-class boundary observer.  Its boundary channel is represented
only by an explicit ability to realize signed Tseitin boundaries, without
requiring that realization to fit a local P-class spacetime budget. -/
structure NPClassNonlocalBoundaryObserver : Type where
  np_boundary_channel : Prop
  np_boundary_channel_cert : np_boundary_channel
  realizes_signed_tseitin_boundaries :
    forall {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
      (T : SignedTseitinParityFlipBoundary enc M n),
        Nonempty (PhysicalBoundaryRealization T)

/-! ## Spacetime/locality bounds -/

/-- Trace spacetime volume of a realization. -/
def realizationSpacetimeVolume
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T) : Nat :=
  R.usage.time * R.usage.memory

/-- If a realization is within the local spacetime budget, then its spacetime
volume is within the observer's time-memory volume. -/
theorem realizationSpacetimeVolume_le_budget
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T)
    (hbudget : WithinLocalSpacetimeBudget O R) :
    realizationSpacetimeVolume R <= O.budget.spacetimeVolumeLimit := by
  dsimp [realizationSpacetimeVolume,
    LocalSpacetimeBudget.spacetimeVolumeLimit]
  exact Nat.mul_le_mul hbudget.time_within hbudget.memory_within

/-- If a realization is within the local budget, then its communication is
inside the local lightcone capacity. -/
theorem realizationCommunication_le_lightcone
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T)
    (hbudget : WithinLocalSpacetimeBudget O R) :
    R.usage.bandwidth <= O.budget.localityLightconeLimit :=
  hbudget.locality_lightcone_within

/-- Local-spacetime lower bound for realizing a boundary.

This is the serious physics payload.  It can rule out local P-class observers
by either time-memory volume or local communication/lightcone volume. -/
structure LocalSpacetimeBoundaryLowerBound
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  requiredSpacetimeVolume : Nat
  requiredCommunication : Nat
  every_realization_requires_spacetime :
    forall R : PhysicalBoundaryRealization T,
      requiredSpacetimeVolume <= realizationSpacetimeVolume R
  every_realization_requires_communication :
    forall R : PhysicalBoundaryRealization T,
      requiredCommunication <= R.usage.bandwidth
  local_gap :
    O.budget.spacetimeVolumeLimit < requiredSpacetimeVolume \/
      O.budget.localityLightconeLimit < requiredCommunication

/-- A local-spacetime lower bound excludes local realization by the bounded
observer.  This theorem does not use energy or erasure. -/
theorem not_canLocallyRealizeBoundary_of_spacetimeLowerBound
    (O : LocalPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : LocalSpacetimeBoundaryLowerBound O T) :
    Not (CanLocallyRealizeBoundary O T) := by
  rintro ⟨R, hbudget⟩
  rcases H.local_gap with hspace | hcomm
  · have hreq :
        H.requiredSpacetimeVolume <= realizationSpacetimeVolume R :=
      H.every_realization_requires_spacetime R
    have hcap :
        realizationSpacetimeVolume R <= O.budget.spacetimeVolumeLimit :=
      realizationSpacetimeVolume_le_budget O R hbudget
    exact Nat.not_lt_of_ge (Nat.le_trans hreq hcap) hspace
  · have hreq :
        H.requiredCommunication <= R.usage.bandwidth :=
      H.every_realization_requires_communication R
    have hcap :
        R.usage.bandwidth <= O.budget.localityLightconeLimit :=
      realizationCommunication_le_lightcone O R hbudget
    exact Nat.not_lt_of_ge (Nat.le_trans hreq hcap) hcomm

/-- A spacetime/locality observer boundary at one signed Tseitin parity-flip
instance. -/
structure SpacetimeObserverBoundaryAt
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop where
  p_observer_cannot_locally_realize :
    Not (CanLocallyRealizeBoundary P.observer T)
  np_observer_can_nonlocally_realize :
    Nonempty (PhysicalBoundaryRealization T)

/-- Main spacetime/locality physical boundary theorem. -/
theorem spacetimeObserverBoundaryAt_of_localLowerBound
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : LocalSpacetimeBoundaryLowerBound P.observer T) :
    SpacetimeObserverBoundaryAt P N T where
  p_observer_cannot_locally_realize :=
    not_canLocallyRealizeBoundary_of_spacetimeLowerBound P.observer H
  np_observer_can_nonlocally_realize :=
    N.realizes_signed_tseitin_boundaries T

/-! ## Concrete one-edge signed Tseitin specialization -/

/-- One-edge sanity specialization of the spacetime/locality theorem.

The asymptotic lower-bound target remains replacing this seed with a signed
Tseitin expander family and proving a genuine local-spacetime lower bound. -/
theorem oneEdgeTseitin_spacetimeObserverBoundary_of_localLowerBound
    (P : PClassLocalPhysicalObserver)
    (N : NPClassNonlocalBoundaryObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M)
    (H :
      LocalSpacetimeBoundaryLowerBound P.observer
        (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM)) :
    SpacetimeObserverBoundaryAt P N
      (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM) :=
  spacetimeObserverBoundaryAt_of_localLowerBound P N H

/-! ## Kernel-only axiom trace -/

#print axioms realizationSpacetimeVolume_le_budget
#print axioms realizationCommunication_le_lightcone
#print axioms not_canLocallyRealizeBoundary_of_spacetimeLowerBound
#print axioms spacetimeObserverBoundaryAt_of_localLowerBound
#print axioms oneEdgeTseitin_spacetimeObserverBoundary_of_localLowerBound

end PallLean.Paper93.DeepMath.PathB
