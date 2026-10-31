import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementRestrictedLiftBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge

/-!
# Expanding the restricted entanglement class: `AC0[p]` union dynamic MERA

The restricted-lift audit says useful progress must enlarge the solver class by
new class-specific lower bounds.  This file performs one honest enlargement
using two independent, already kernel-checked capstones:

1. the Razborov--Smolensky parity-CNF lower bound for machines whose answers on
   that family have a sufficiently small `AC0[p]` realization;
2. the dynamic no-merging lower bound for machines whose independent SAT-query
   batches uniformly fit one fixed bounded-bond, bounded-cone, logarithmic-depth
   MERA family.

Their union is a broader restricted class than either component by definition.
No member of the union decides SAT: each branch is discharged by its own real
lower bound.  The class therefore has a downstream dynamic-entanglement
interface.  As before, promoting this enlarged interface to all polynomial
machines is exactly equivalent to `SATDecisionInP` being false.

This is genuine restricted-class enlargement, not a claim that either
architecture contains all polynomial-time algorithms.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier

/-! ## Solver-class union -/

/-- Union of two solver classes. -/
def SolverClassUnion {U : MachineModel}
    (C1 C2 : SolverClass U) : SolverClass U :=
  fun D => C1 D \/ C2 D

/-- Lower bounds for both components give a lower bound for their union. -/
theorem no_SATDecisionInClass_union
    {U : MachineModel} {C1 C2 : SolverClass U}
    (h1 : ¬ SATDecisionInClass C1)
    (h2 : ¬ SATDecisionInClass C2) :
    ¬ SATDecisionInClass (SolverClassUnion C1 C2) := by
  rintro ⟨D, hD, hsat⟩
  cases hD with
  | inl hC1 => exact h1 ⟨D, hC1, hsat⟩
  | inr hC2 => exact h2 ⟨D, hC2, hsat⟩

/-! ## The dynamic-MERA component as a standard solver class -/

/-- Machines whose independent SAT-query batches compile into one fixed
restricted MERA family. -/
def IndependentQueryMERAClass (U : MachineModel) : SolverClass U :=
  fun D => HasIndependentSATQueryRestrictedMERA U D

/-- The dynamic no-merging theorem gives a genuine SAT lower bound for this
MERA class. -/
theorem no_SATDecisionInClass_independentQueryMERA
    (U : MachineModel) :
    ¬ SATDecisionInClass (IndependentQueryMERAClass U) := by
  intro h
  exact no_SAT_decider_with_independentQueryRestrictedMERA h

/-! ## Concrete enlarged class -/

/-- The union of the small-`AC0[p]` parity-family class and the independent
query restricted-MERA class. -/
def ExpandedEntanglementClass
    (U : MachineModel) (p m d lower : Nat) : SolverClass U :=
  SolverClassUnion
    (SmallAC0pParityClass U p m d lower)
    (IndependentQueryMERAClass U)

/-- Each original class embeds in the expanded class. -/
theorem smallAC0p_subset_expanded
    (U : MachineModel) (p m d lower : Nat) :
    forall D, SmallAC0pParityClass U p m d lower D ->
      ExpandedEntanglementClass U p m d lower D :=
  fun _ h => Or.inl h

theorem independentQueryMERA_subset_expanded
    (U : MachineModel) (p m d lower : Nat) :
    forall D, IndependentQueryMERAClass U D ->
      ExpandedEntanglementClass U p m d lower D :=
  fun _ h => Or.inr h

/-- The two independent capstones rule out SAT deciders throughout the enlarged
union class. -/
theorem no_SATDecisionInClass_expandedEntanglement
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    ¬ SATDecisionInClass (ExpandedEntanglementClass U p m d lower) :=
  no_SATDecisionInClass_union
    (no_SATDecisionInClass_smallAC0pParity
      U p m t d lower hp2 ht1 hpt hlow hm)
    (no_SATDecisionInClass_independentQueryMERA U)

/-- The enlarged class consequently has an inhabited restricted dynamic-trace
interface, downstream of the two genuine capstones. -/
theorem expandedEntanglement_restrictedInvariant_inhabited
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (DynamicTraceInvariantForClass U
      (ExpandedEntanglementClass U p m d lower)) :=
  (dynamicTraceInvariantForClass_iff_no_SATDecisionInClass).2
    (no_SATDecisionInClass_expandedEntanglement
      U p m t d lower hp2 ht1 hpt hlow hm)

/-- Even after this real enlargement, a promotion to every polynomial machine
exists exactly when the unrestricted SAT lower bound already holds. -/
theorem expandedEntanglementLift_iff_no_SATDecisionInP
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U
      (ExpandedEntanglementClass U p m d lower)) <->
      ¬ SATDecisionInP U :=
  restrictedEntanglementLift_iff_no_SATDecisionInP
    (expandedEntanglement_restrictedInvariant_inhabited
      U p m t d lower hp2 ht1 hpt hlow hm)

end PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass.no_SATDecisionInClass_union
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass.no_SATDecisionInClass_independentQueryMERA
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass.no_SATDecisionInClass_expandedEntanglement
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass.expandedEntanglement_restrictedInvariant_inhabited
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass.expandedEntanglementLift_iff_no_SATDecisionInP
