import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicTraceInvariantEquivalence

/-!
# Restricted-class dynamic trace invariant

The unrestricted global invariant target is equivalent to the full SAT lower bound:

```lean
Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) ↔ ¬ SATDecisionInP U
```

So the productive non-vacuous use is restricted-class instantiation.  This file adds the exact interface for that:

```lean
C : DecisionMachine U -> Prop
```

is a solver class (AC⁰, formulas, proof-space observers, OBDDs, etc.).  A restricted dynamic trace invariant says that
for every `D ∈ C`, correctness of `D` yields the trace-label invariant.  The cash-out is the restricted lower bound:
there is no SAT decider inside `C`.

This is where the existing capstones should plug in: they prove the restricted `invariant_of_decides` field for a concrete
class/family, not for all of P.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence

/-- A restricted solver class inside one machine model. -/
abbrev SolverClass (U : MachineModel) := DecisionMachine U -> Prop

/-- SAT has a correct decider in the restricted solver class `C`. -/
def SATDecisionInClass {U : MachineModel} (C : SolverClass U) : Prop :=
  exists D : DecisionMachine U, C D ∧ DecidesSAT U D

/-- Restricted dynamic trace-invariant theorem target.

For each `D` in the class `C`, produce the dynamic trace-label invariant conditional on SAT correctness of `D`. -/
abbrev DynamicTraceInvariantForClass (U : MachineModel) (C : SolverClass U) : Type 1 :=
  forall D : DecisionMachine U, C D -> DynamicTraceInvariantFromCorrectnessFor U D

/-- Restricted cash-out: a class-wide dynamic trace invariant rules out SAT deciders in that class. -/
theorem no_SATDecisionInClass_of_dynamicTraceInvariantForClass
    {U : MachineModel} {C : SolverClass U}
    (hInv : DynamicTraceInvariantForClass U C) :
    ¬ SATDecisionInClass C := by
  intro hC
  rcases hC with ⟨D, hClass, hD⟩
  exact (hInv D hClass).not_decidesSAT hD

/-- If there is no SAT decider in class `C`, the restricted invariant target is vacuously inhabited on `C`. -/
noncomputable def dynamicTraceInvariantForClass_of_no_SATDecisionInClass
    {U : MachineModel} {C : SolverClass U}
    (hNo : ¬ SATDecisionInClass C) :
    DynamicTraceInvariantForClass U C := by
  intro D hClass
  refine dynamicTraceInvariant_of_not_decidesSAT D ?_
  intro hD
  exact hNo ⟨D, hClass, hD⟩

/-- For any restricted class, the restricted invariant target is equivalent to the restricted SAT lower bound. -/
theorem dynamicTraceInvariantForClass_iff_no_SATDecisionInClass
    {U : MachineModel} {C : SolverClass U} :
    Nonempty (DynamicTraceInvariantForClass U C) ↔ ¬ SATDecisionInClass C := by
  constructor
  · intro hInv
    rcases hInv with ⟨hInv⟩
    exact no_SATDecisionInClass_of_dynamicTraceInvariantForClass hInv
  · intro hNo
    exact ⟨dynamicTraceInvariantForClass_of_no_SATDecisionInClass hNo⟩

/-- Any class-wide invariant and a class SAT decider are contradictory. -/
theorem dynamicTraceInvariantForClass_contradicts_SATDecisionInClass
    {U : MachineModel} {C : SolverClass U}
    (hInv : DynamicTraceInvariantForClass U C) (hC : SATDecisionInClass C) : False := by
  exact no_SATDecisionInClass_of_dynamicTraceInvariantForClass hInv hC

/-- Monotonicity: if `C₁ ⊆ C₂`, then a lower bound for `C₂` gives a lower bound for `C₁`. -/
theorem no_SATDecisionInSubclass
    {U : MachineModel} {C₁ C₂ : SolverClass U}
    (hsub : forall D : DecisionMachine U, C₁ D -> C₂ D)
    (hNo₂ : ¬ SATDecisionInClass C₂) :
    ¬ SATDecisionInClass C₁ := by
  intro hC₁
  rcases hC₁ with ⟨D, hD₁, hsat⟩
  exact hNo₂ ⟨D, hsub D hD₁, hsat⟩

/-- Invariant transfer down to subclasses. -/
def dynamicTraceInvariantForSubclass
    {U : MachineModel} {C₁ C₂ : SolverClass U}
    (hsub : forall D : DecisionMachine U, C₁ D -> C₂ D)
    (hInv₂ : DynamicTraceInvariantForClass U C₂) :
    DynamicTraceInvariantForClass U C₁ := by
  intro D hD₁
  exact hInv₂ D (hsub D hD₁)

/-- The unrestricted theorem is the special case where the class contains all machines. -/
def AllMachines (U : MachineModel) : SolverClass U :=
  fun _ => True

/-- Restricted SAT decision for `AllMachines` is equivalent to the existing `SATDecisionInP`. -/
theorem SATDecisionInClass_allMachines_iff {U : MachineModel} :
    SATDecisionInClass (AllMachines U) ↔ SATDecisionInP U := by
  constructor
  · intro h
    rcases h with ⟨D, _hAll, hD⟩
    exact ⟨D, hD⟩
  · intro h
    rcases h with ⟨D, hD⟩
    exact ⟨D, trivial, hD⟩

/-- Likewise, the class invariant for `AllMachines` is equivalent to the unrestricted invariant target. -/
def dynamicTraceInvariantAllMachines_to_unrestricted {U : MachineModel}
    (hInv : DynamicTraceInvariantForClass U (AllMachines U)) :
    DynamicTraceInvariantFromCorrectnessForAllMachines U := by
  intro D
  exact hInv D trivial

/-- The unrestricted invariant target restricts to `AllMachines`. -/
def unrestricted_to_dynamicTraceInvariantAllMachines {U : MachineModel}
    (hInv : DynamicTraceInvariantFromCorrectnessForAllMachines U) :
    DynamicTraceInvariantForClass U (AllMachines U) := by
  intro D _
  exact hInv D

/-!
## Plug-in point for capstones

For a concrete restricted class `C`, the non-vacuous theorem to prove is:

```lean
DynamicTraceInvariantForClass U C
```

or, more locally, for each `D ∈ C`:

```lean
DecidesSAT U D -> DynamicTraceLabelInvariantFor projection hardFamily.fam
```

Existing restricted lower-bound capstones should be connected by proving this field for their solver class/family.  The
cash-out above then gives `¬ SATDecisionInClass C`.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.no_SATDecisionInClass_of_dynamicTraceInvariantForClass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.dynamicTraceInvariantForClass_of_no_SATDecisionInClass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.dynamicTraceInvariantForClass_iff_no_SATDecisionInClass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.dynamicTraceInvariantForClass_contradicts_SATDecisionInClass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.no_SATDecisionInSubclass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.dynamicTraceInvariantForSubclass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.SATDecisionInClass_allMachines_iff
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.dynamicTraceInvariantAllMachines_to_unrestricted
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.unrestricted_to_dynamicTraceInvariantAllMachines
