import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementInteractiveProtocolClass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPBoundedLocalAccessCompiler

/-!
# Bounded local access is already inside the MERA entanglement branch

After four genuine restricted enlargements, the next candidate was the
repository's fixed-alphabet, bounded-fan-in, logarithmic-depth local-access
compiler.  This file checks whether that candidate actually enlarges the class.

It does not.  The existing compiler has an explicit chain

```text
bounded local access -> Ramanujan query MERA -> independent-query MERA.
```

We turn that chain into a solver-class inclusion and prove that unioning the
local-access class into the four-architecture class is pointwise identical to
the original class.  Thus its lower bound is real, but already accounted for
by the bounded-MERA branch; counting it again would overstate progress.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler
open PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler
open PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier
open PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass
open PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass
open PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass

/-- The bounded-local-access solver class in the common class interface. -/
def BoundedLocalAccessClass (U : MachineModel) : SolverClass U :=
  fun D => Nonempty (BoundedLocalAccessSATCompiler U D)

/-- Forgetting local alphabet, fan-in, expander routing and causal profile
leaves exactly an independent-query restricted-MERA compiler. -/
theorem boundedLocalAccess_subset_independentQueryMERA
    (U : MachineModel) :
    forall D, BoundedLocalAccessClass U D ->
      IndependentQueryMERAClass U D := by
  intro D h
  obtain ⟨C⟩ := h
  exact ⟨C.toRamanujan.mera, C.toRamanujan.toIndependentQueryCompiler⟩

/-- Consequently bounded local access is already contained in the existing
four-architecture union. -/
theorem boundedLocalAccess_subset_fourArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    forall D, BoundedLocalAccessClass U D ->
      FourArchitectureEntanglementClass U p m d lower D := by
  intro D hlocal
  apply threeArchitecture_subset_fourArchitecture
  apply expanded_subset_threeArchitecture
  apply independentQueryMERA_subset_expanded
  exact boundedLocalAccess_subset_independentQueryMERA U D hlocal

/-- The tempting five-label union. -/
def LocalAccessAdjoinedClass
    (U : MachineModel) (p m d lower : Nat) : SolverClass U :=
  SolverClassUnion
    (FourArchitectureEntanglementClass U p m d lower)
    (BoundedLocalAccessClass U)

/-- Adjoining bounded local access adds no machines: the candidate class is
pointwise equal to the four-architecture class. -/
theorem localAccessAdjoined_iff_fourArchitecture
    (U : MachineModel) (p m d lower : Nat)
    (D : DecisionMachine U) :
    LocalAccessAdjoinedClass U p m d lower D <->
      FourArchitectureEntanglementClass U p m d lower D := by
  constructor
  · intro h
    cases h with
    | inl hfour => exact hfour
    | inr hlocal =>
        exact boundedLocalAccess_subset_fourArchitecture
          U p m d lower D hlocal
  · intro hfour
    exact Or.inl hfour

/-- Extensional class equality: bounded local access is formally redundant. -/
theorem localAccessAdjoined_eq_fourArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    LocalAccessAdjoinedClass U p m d lower =
      FourArchitectureEntanglementClass U p m d lower := by
  funext D
  exact propext (localAccessAdjoined_iff_fourArchitecture
    U p m d lower D)

/-- The adjoined class has a lower bound only because it is the same class as
the already excluded four-architecture union. -/
theorem no_SATDecisionInClass_localAccessAdjoined
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    ¬ SATDecisionInClass (LocalAccessAdjoinedClass U p m d lower) := by
  rw [localAccessAdjoined_eq_fourArchitecture]
  exact no_SATDecisionInClass_fourArchitecture
    U p m t d lower hp2 ht1 hpt hlow hm

/-- The unrestricted lift endpoint is unchanged because the class itself is
unchanged. -/
theorem localAccessAdjoinedLift_iff_no_SATDecisionInP
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U
      (LocalAccessAdjoinedClass U p m d lower)) <->
      ¬ SATDecisionInP U := by
  rw [localAccessAdjoined_eq_fourArchitecture]
  exact fourArchitectureLift_iff_no_SATDecisionInP
    U p m t d lower hp2 ht1 hpt hlow hm

end PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit.boundedLocalAccess_subset_independentQueryMERA
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit.localAccessAdjoined_eq_fourArchitecture
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit.no_SATDecisionInClass_localAccessAdjoined
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementLocalAccessRedundancyAudit.localAccessAdjoinedLift_iff_no_SATDecisionInP
