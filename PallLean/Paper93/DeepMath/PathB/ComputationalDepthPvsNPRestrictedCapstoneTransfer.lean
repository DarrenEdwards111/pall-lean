import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRestrictedDynamicTraceInvariant

/-!
# Restricted capstone transfer into the dynamic-trace P-vs-NP interface

The unrestricted dynamic-trace invariant target was proved equivalent to the full SAT lower bound, so it is not a
smaller theorem.  The right way to use the dynamic-trace interface is downstream of a **real restricted-class
lower bound**: AC⁰[p], formulas, resolution proof-space, OBDD, sign-rank/UPP, etc.

This file formalizes that transfer step without circularity.

A restricted capstone should provide an impossible obstruction object extracted from any SAT-correct machine in the
class `C`.  Once such a capstone is available, we get:

* `¬ SATDecisionInClass C`, directly;
* `DynamicTraceInvariantForClass U C`, but only vacuously/downstream from the proved class lower bound.

So the proof direction is:

```text
class-specific capstone lower bound
        ⇒ no SAT decider in class C
        ⇒ restricted dynamic trace invariant for C
```

not the circular direction:

```text
assert dynamic trace invariant for C ⇒ lower bound.
```

This is the plug-in adapter for the existing capstones.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant

/-- A class-specific lower-bound capstone, presented as an impossible obstruction extracted from any SAT-correct
machine in the restricted class `C`.

For a concrete capstone, `Obstruction` is the forbidden object, e.g. a small AC⁰[p] circuit computing PARITY/MOD,
a formula violating a Nečiporuk lower bound, an impossible proof-space transcript, etc.  The field
`obstruction_of_decides` is the real extraction theorem for the class.  The field `no_obstruction` is the already
proved lower-bound theorem saying the forbidden object cannot exist. -/
structure RestrictedCapstoneTransfer (U : MachineModel) (C : SolverClass U) : Type 1 where
  Obstruction : Type
  obstruction_of_decides : ∀ D : DecisionMachine U, C D -> DecidesSAT U D -> Obstruction
  no_obstruction : IsEmpty Obstruction

/-- A restricted capstone immediately rules out SAT deciders in the restricted class. -/
theorem no_SATDecisionInClass_of_restrictedCapstone
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedCapstoneTransfer U C) :
    ¬ SATDecisionInClass C := by
  intro hSAT
  rcases hSAT with ⟨D, hClass, hDecides⟩
  exact cap.no_obstruction.false (cap.obstruction_of_decides D hClass hDecides)

/-- Once a real capstone proves the restricted lower bound, the restricted dynamic trace invariant follows only as a
safe downstream/vacuous consequence.  This is intentionally not a new proof of the lower bound. -/
noncomputable def dynamicTraceInvariantForClass_of_restrictedCapstone
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedCapstoneTransfer U C) :
    DynamicTraceInvariantForClass U C :=
  dynamicTraceInvariantForClass_of_no_SATDecisionInClass
    (no_SATDecisionInClass_of_restrictedCapstone cap)

/-- The capstone cannot coexist with a restricted SAT decider. -/
theorem restrictedCapstone_contradicts_SATDecisionInClass
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedCapstoneTransfer U C) (hSAT : SATDecisionInClass C) : False := by
  exact no_SATDecisionInClass_of_restrictedCapstone cap hSAT

/-- Prop-valued convenience wrapper: sometimes the capstone is most naturally stated as a forbidden proposition
rather than an explicit forbidden witness type. -/
structure RestrictedPropCapstoneTransfer (U : MachineModel) (C : SolverClass U) : Type 1 where
  Forbidden : Prop
  forbidden_of_decides : ∀ D : DecisionMachine U, C D -> DecidesSAT U D -> Forbidden
  impossible : ¬ Forbidden

/-- Prop-valued capstone cash-out. -/
theorem no_SATDecisionInClass_of_propCapstone
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedPropCapstoneTransfer U C) :
    ¬ SATDecisionInClass C := by
  intro hSAT
  rcases hSAT with ⟨D, hClass, hDecides⟩
  exact cap.impossible (cap.forbidden_of_decides D hClass hDecides)

/-- Prop-valued capstone to restricted dynamic trace invariant, again downstream from the real lower bound. -/
noncomputable def dynamicTraceInvariantForClass_of_propCapstone
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedPropCapstoneTransfer U C) :
    DynamicTraceInvariantForClass U C :=
  dynamicTraceInvariantForClass_of_no_SATDecisionInClass
    (no_SATDecisionInClass_of_propCapstone cap)

/-- A useful diagnostic: if a restricted capstone exists, the restricted invariant is inhabited for the honest reason
(the class lower bound), not because the invariant itself supplied any new geometry. -/
theorem restrictedCapstone_supplies_restrictedInvariant
    {U : MachineModel} {C : SolverClass U}
    (cap : RestrictedCapstoneTransfer U C) :
    Nonempty (DynamicTraceInvariantForClass U C) := by
  exact ⟨dynamicTraceInvariantForClass_of_restrictedCapstone cap⟩

end PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.no_SATDecisionInClass_of_restrictedCapstone
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.dynamicTraceInvariantForClass_of_restrictedCapstone
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.restrictedCapstone_contradicts_SATDecisionInClass
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.no_SATDecisionInClass_of_propCapstone
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.dynamicTraceInvariantForClass_of_propCapstone
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedCapstoneTransfer.restrictedCapstone_supplies_restrictedInvariant
