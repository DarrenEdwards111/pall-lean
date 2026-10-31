import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicTraceInvariant

/-!
# Dynamic trace-label invariant equivalence

`ComputationalDepthPvsNPDynamicTraceInvariant` identified the live target

```lean
DecidesSAT U D -> DynamicTraceLabelInvariantFor projection hardFamily.fam
```

and proved that a global version rules out `SATDecisionInP`.  This file proves the converse, in the only honest general-P
sense: if there is no SAT decision machine in the model, then the invariant theorem is vacuously inhabited for every
claimed decider.

Thus the unrestricted global invariant target is logically equivalent to the desired lower bound.  Any non-vacuous progress
must instantiate the invariant for a restricted solver class or provide a genuinely new trace-geometry theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPHardResidualFamily
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicPreservationFromCorrectness
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariant

/-- A dummy residual instance used only for vacuous/equivalence packaging. -/
def dummyResidualInstance : ResidualInstance where
  φ := { vars := 0, clauses := [] }
  pref := []

/-- A one-bit fooling family with identity labels and a syntactically constant residual instance.

The residual formulas are not hard; this object is only used in the converse direction, where `DecidesSAT` is impossible
and all invariant obligations are discharged by contradiction. -/
def dummyOneBitFoolingFamily : FoolingResidualFamily 1 :=
  identityFoolingFamily 1 (fun _ => dummyResidualInstance)

/-- A minimally annotated hard-family wrapper for the dummy one-bit family.

The payloads are `True` because this is an equivalence/vacuity construction, not a hardness construction. -/
def dummyHardSATResidualFamily : HardSATResidualFamily 1 where
  fam := dummyOneBitFoolingFamily
  residual_semantics := True
  residual_semantics_realized := trivial
  np_complete_payload := True
  np_complete_realized := trivial
  not_easy_linear_payload := True
  not_easy_linear_realized := trivial

/-- The constant one-cell projection used for vacuous packaging. -/
def vacuousProjection (U : MachineModel) (D : DecisionMachine U) :
    DynamicSPDPBoundaryProjectionFor U D 1 where
  k := 0
  dynamicTrace := PUnit
  boundary := PUnit
  fintypeBoundary := inferInstance
  rawTrace := fun _ => PUnit.unit
  boundaryOf := fun _ => PUnit.unit
  polyBoundary := by
    simp
  expGap := by
    norm_num

/-- If a particular `D` is not a SAT decider, then the invariant-from-correctness object for `D` is inhabited vacuously.

This is intentionally not a constructive preservation theorem: `invariant_of_decides` eliminates the impossible
`DecidesSAT U D` premise. -/
noncomputable def dynamicTraceInvariant_of_not_decidesSAT
    {U : MachineModel} (D : DecisionMachine U) (hD : ¬ DecidesSAT U D) :
    DynamicTraceInvariantFromCorrectnessFor U D where
  m := 1
  hardFamily := dummyHardSATResidualFamily
  projection := vacuousProjection U D
  invariant_of_decides := by
    intro hdec
    exact False.elim (hD hdec)

/-- If there is no SAT decision machine in the model, the global dynamic trace-invariant theorem is vacuously true. -/
noncomputable def dynamicTraceInvariant_of_no_SATDecisionInP {U : MachineModel}
    (hNo : ¬ SATDecisionInP U) :
    DynamicTraceInvariantFromCorrectnessForAllMachines U := by
  intro D
  refine dynamicTraceInvariant_of_not_decidesSAT D ?_
  intro hD
  exact hNo ⟨D, hD⟩

/-- The unrestricted global dynamic trace-invariant theorem is equivalent to `¬ SATDecisionInP U`. -/
theorem dynamicTraceInvariant_iff_no_SATDecisionInP {U : MachineModel} :
    Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) ↔ ¬ SATDecisionInP U := by
  constructor
  · intro hInv
    rcases hInv with ⟨hInv⟩
    exact no_SATDecisionInP_of_dynamicTraceInvariant hInv
  · intro hNo
    exact ⟨dynamicTraceInvariant_of_no_SATDecisionInP hNo⟩

/-- Non-vacuity warning: any global invariant theorem, together with an actual SAT decider, is contradictory. -/
theorem dynamicTraceInvariant_contradicts_SATDecisionInP {U : MachineModel}
    (hInv : DynamicTraceInvariantFromCorrectnessForAllMachines U) (hP : SATDecisionInP U) : False := by
  exact no_SATDecisionInP_of_dynamicTraceInvariant hInv hP

/-!
## Consequence

The general-P invariant target is now calibrated exactly:

```lean
Nonempty (DynamicTraceInvariantFromCorrectnessForAllMachines U) ↔ ¬ SATDecisionInP U
```

So proving it non-vacuously for a genuine NP-complete family is the whole lower bound.  Productive next steps should be
restricted-class instantiations of `invariant_of_decides`, where the trace-label invariant is a real lower-bound theorem
rather than a vacuous consequence of `¬ SATDecisionInP`.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence.dynamicTraceInvariant_of_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence.dynamicTraceInvariant_of_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence.dynamicTraceInvariant_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicTraceInvariantEquivalence.dynamicTraceInvariant_contradicts_SATDecisionInP
