import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThermodynamicObserverBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMikoshiTseitinConcrete

/-!
# Physical observer boundary

This file formalizes the observer-physics hypothesis in a safe form.

The theorem proved here is not classical `P ≠ NP`.  It is an
observer-relative physical boundary theorem:

* a `P`-class physical observer has finite classical resources and no
  hypercomputational/oracle channel;
* an `NP`-class physical observer is allowed, by hypothesis, to physically
  realize signed counterfactual boundaries;
* if physics proves that realizing a given boundary requires more resource
  than the `P`-observer budget allows, then that `P`-observer cannot realize
  the boundary while the `NP`-observer can.

The load-bearing physics theorem is explicit:
`PhysicalBoundaryEnergyLowerBound`.  Without such a lower bound this file
does not claim that any P-class observer is excluded.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Physical observers and boundary realizations -/

/-- A physical observer with a finite resource budget. -/
structure PhysicalObserver : Type where
  budget : ThermodynamicBudget

/-- A P-class physical observer.

The first fields are the physical/classical guardrails.  The theorems below
use the finite budget directly; the other fields document the intended
observer class and prevent the term "P-class" from silently meaning "already
cannot see NP". -/
structure PClassPhysicalObserver : Type where
  observer : PhysicalObserver
  classical_turing_channel : Prop
  classical_turing_channel_cert : classical_turing_channel
  no_oracle_channel : Prop
  no_oracle_channel_cert : no_oracle_channel
  no_hypercomputational_channel : Prop
  no_hypercomputational_channel_cert : no_hypercomputational_channel
  polynomial_resource_scaling : Prop
  polynomial_resource_scaling_cert : polynomial_resource_scaling

/-- A concrete physical realization trace for a signed Tseitin parity-flip
boundary.  The `realizesBoundary` predicate is intentionally explicit: it is
the physical/semantic fact that must be supplied by a concrete model. -/
structure PhysicalBoundaryRealization
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  constants : ThermodynamicConstants
  trace : List ThermodynamicStep
  realizesBoundary : Prop
  realizesBoundary_cert : realizesBoundary

namespace PhysicalBoundaryRealization

/-- Resource usage of a realization, computed from its physical trace. -/
def usage
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T) : TraceResourceUsage :=
  traceResourceUsage R.constants R.trace

/-- Any realization's trace energy is at least its Landauer erasure component. -/
theorem energy_ge_landauer
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T) :
    traceLandauerEnergy R.constants R.trace <= R.usage.energy :=
  traceEnergy_ge_landauer R.constants R.trace

end PhysicalBoundaryRealization

/-- A realization fits inside a physical observer's finite budget. -/
def WithinPhysicalObserverBudget
    (O : PhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (R : PhysicalBoundaryRealization T) : Prop :=
  R.usage.energy <= O.budget.energyLimit /\
  R.usage.time <= O.budget.timeLimit /\
  R.usage.memory <= O.budget.memoryLimit /\
  R.usage.bandwidth <= O.budget.bandwidthLimit

/-- Observer `O` can physically realize the signed parity-flip boundary `T`. -/
def CanPhysicallyRealizeBoundary
    (O : PhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop :=
  exists R : PhysicalBoundaryRealization T,
    WithinPhysicalObserverBudget O R

/-- An NP-class physical observer: a physical observer equipped with a
witness/oracle/hyper-style channel, represented only by its stated ability to
realize the signed counterfactual boundaries in the chosen family.

This is an observer-class hypothesis, not a classical complexity theorem. -/
structure NPClassPhysicalObserver : Type where
  observer : PhysicalObserver
  np_boundary_channel : Prop
  np_boundary_channel_cert : np_boundary_channel
  realizes_signed_tseitin_boundaries :
    forall {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
      (T : SignedTseitinParityFlipBoundary enc M n),
        CanPhysicallyRealizeBoundary observer T

/-! ## Physics lower bound and separation theorem -/

/-- Physics-side lower bound for realizing a concrete boundary.

This is the load-bearing theorem a real physics argument must prove: every
physical realization of `T` costs at least `requiredEnergy`, and that required
energy exceeds the specified observer's budget. -/
structure PhysicalBoundaryEnergyLowerBound
    (O : PhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Type where
  requiredEnergy : Nat
  every_realization_requires_energy :
    forall R : PhysicalBoundaryRealization T,
      requiredEnergy <= R.usage.energy
  energy_gap :
    O.budget.energyLimit < requiredEnergy

/-- The physics lower bound excludes physical realization by the bounded
observer. -/
theorem not_canPhysicallyRealizeBoundary_of_energyLowerBound
    (O : PhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : PhysicalBoundaryEnergyLowerBound O T) :
    Not (CanPhysicallyRealizeBoundary O T) := by
  rintro ⟨R, hbudget⟩
  have hreq : H.requiredEnergy <= R.usage.energy :=
    H.every_realization_requires_energy R
  have henergy : R.usage.energy <= O.budget.energyLimit :=
    hbudget.1
  exact Nat.not_lt_of_ge (Nat.le_trans hreq henergy) H.energy_gap

/-- A physical observer boundary at one signed Tseitin parity-flip instance:
the P-class observer cannot realize the boundary, while the NP-class observer
can. -/
structure PhysicalObserverBoundaryAt
    (P : PClassPhysicalObserver)
    (N : NPClassPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    (T : SignedTseitinParityFlipBoundary enc M n) : Prop where
  p_observer_cannot_realize :
    Not (CanPhysicallyRealizeBoundary P.observer T)
  np_observer_can_realize :
    CanPhysicallyRealizeBoundary N.observer T

/-- Main physical boundary theorem.

If physics supplies a resource lower bound for the P-class observer and the
NP-class observer has the stipulated boundary channel, then the signed
Tseitin boundary separates the two physical observer classes. -/
theorem physicalObserverBoundaryAt_of_energyLowerBound
    (P : PClassPhysicalObserver)
    (N : NPClassPhysicalObserver)
    {enc : SignedFormulaEncoding} {M : DTM} {n : Nat}
    {T : SignedTseitinParityFlipBoundary enc M n}
    (H : PhysicalBoundaryEnergyLowerBound P.observer T) :
    PhysicalObserverBoundaryAt P N T where
  p_observer_cannot_realize :=
    not_canPhysicallyRealizeBoundary_of_energyLowerBound P.observer H
  np_observer_can_realize :=
    N.realizes_signed_tseitin_boundaries T

/-! ## Concrete one-edge signed Tseitin specialization -/

/-- The concrete one-edge signed Tseitin seed separates physical observer
classes whenever physics proves that realizing that seed exceeds the P-class
observer's budget.  This is a sanity specialization of the general theorem;
the asymptotic lower-bound target must replace the one-edge seed for any
serious scaling result. -/
theorem oneEdgeTseitin_physicalObserverBoundary_of_energyLowerBound
    (P : PClassPhysicalObserver)
    (N : NPClassPhysicalObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT signedThreeCNFEncoding M)
    (H :
      PhysicalBoundaryEnergyLowerBound P.observer
        (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM)) :
    PhysicalObserverBoundaryAt P N
      (signedOneEdgeTseitinParityFlipBoundary_of_decider M hM) :=
  physicalObserverBoundaryAt_of_energyLowerBound P N H

/-! ## Kernel-only axiom trace -/

#print axioms PhysicalBoundaryRealization.energy_ge_landauer
#print axioms not_canPhysicallyRealizeBoundary_of_energyLowerBound
#print axioms physicalObserverBoundaryAt_of_energyLowerBound
#print axioms oneEdgeTseitin_physicalObserverBoundary_of_energyLowerBound

end PallLean.Paper93.DeepMath.PathB
