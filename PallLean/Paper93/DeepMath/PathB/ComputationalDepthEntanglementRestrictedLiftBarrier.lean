import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementDynamicTraceEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityAC0pClass

/-!
# Restricted entanglement lift barrier

The dynamic-entanglement endpoint suggests working first in a restricted solver
class.  The repository already contains a genuine example: the
Razborov--Smolensky parity-CNF capstone proves that no SAT decider has a small
`AC0[p]` realization on the parity family.  The generic capstone adapter then
inhabits the restricted dynamic trace-invariant interface downstream of that
real lower bound.

The remaining proposal is to lift this restricted invariant to every
polynomial machine.  This file calibrates that lift exactly.

For any restricted class whose trace-invariant interface is inhabited, a
uniform lift from the restricted interface to the all-machines interface exists
if and only if `SATDecisionInP` is false.  The reverse direction simply ignores
the restricted input and uses the existing vacuous global package after
assuming the lower bound.  The forward direction applies the lift to the
inhabited restricted package and obtains the global dynamic invariant.

Instantiating this with the concrete small-`AC0[p]` parity class proves that
extending the genuine restricted capstone to all polynomial algorithms is
already the full SAT lower bound.  Thus restricted entanglement is productive,
but no generic restricted-to-P promotion remains to be proved downstream.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer
open PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass

/-! ## The generic restricted-to-all lift -/

/-- A uniform promotion of dynamic trace geometry from a restricted solver
class to every certified machine in the same model. -/
structure RestrictedToAllDynamicEntanglementLift
    (U : MachineModel) (C : SolverClass U) where
  lift : DynamicTraceInvariantForClass U C ->
    DynamicTraceInvariantFromCorrectnessForAllMachines U

/-- If the restricted interface is inhabited, a restricted-to-all lift proves
the unrestricted SAT lower bound. -/
theorem no_SATDecisionInP_of_restrictedEntanglementLift
    {U : MachineModel} {C : SolverClass U}
    (hC : Nonempty (DynamicTraceInvariantForClass U C))
    (L : RestrictedToAllDynamicEntanglementLift U C) :
    ¬ SATDecisionInP U := by
  obtain ⟨I⟩ := hC
  exact no_SATDecisionInP_of_dynamicTraceInvariant (L.lift I)

/-- Assuming the unrestricted lower bound, a lift can be manufactured by
ignoring its restricted input and returning the vacuous global package. -/
noncomputable def restrictedEntanglementLift_of_no_SATDecisionInP
    {U : MachineModel} (C : SolverClass U)
    (hNo : ¬ SATDecisionInP U) :
    RestrictedToAllDynamicEntanglementLift U C where
  lift := fun _ => dynamicTraceInvariant_of_no_SATDecisionInP hNo

/-- Exact calibration: once a real restricted invariant is available, the
existence of a promotion to all machines is equivalent to the full SAT lower
bound. -/
theorem restrictedEntanglementLift_iff_no_SATDecisionInP
    {U : MachineModel} {C : SolverClass U}
    (hC : Nonempty (DynamicTraceInvariantForClass U C)) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U C) <->
      ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨L⟩
    exact no_SATDecisionInP_of_restrictedEntanglementLift hC L
  · intro hNo
    exact ⟨restrictedEntanglementLift_of_no_SATDecisionInP C hNo⟩

/-! ## Concrete Razborov--Smolensky instantiation -/

/-- The genuine small-`AC0[p]` parity-family capstone supplies an inhabited
restricted dynamic-entanglement interface.  This is a real restricted lower
bound; the trace object is downstream of the capstone. -/
theorem smallAC0pParity_restrictedEntanglement_inhabited
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (DynamicTraceInvariantForClass U
      (SmallAC0pParityClass U p m d lower)) :=
  restrictedCapstone_supplies_restrictedInvariant
    (parityAC0pTransfer U p m t d lower hp2 ht1 hpt hlow hm)

/-- For the concrete small-`AC0[p]` class, promoting its proved restricted
entanglement package to all machines exists exactly when SAT has no polynomial
decider. -/
theorem smallAC0pParity_entanglementLift_iff_no_SATDecisionInP
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U
      (SmallAC0pParityClass U p m d lower)) <->
      ¬ SATDecisionInP U :=
  restrictedEntanglementLift_iff_no_SATDecisionInP
    (smallAC0pParity_restrictedEntanglement_inhabited
      U p m t d lower hp2 ht1 hpt hlow hm)

end PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier.no_SATDecisionInP_of_restrictedEntanglementLift
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier.restrictedEntanglementLift_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier.smallAC0pParity_restrictedEntanglement_inhabited
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier.smallAC0pParity_entanglementLift_iff_no_SATDecisionInP
