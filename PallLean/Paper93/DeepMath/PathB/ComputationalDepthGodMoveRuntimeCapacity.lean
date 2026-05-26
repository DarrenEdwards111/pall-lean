import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveSeparateCapacity

/-
# God-Move capacity instantiated as polynomial runtime budget

This file supplies the first non-bookkeeping solver-capacity candidate for the
separated God-Move route: the actual polynomial runtime budget carried by a
`SearchMachine`.

This is the honest P-side capacity:

  solverCapacity M n := M.budget n.

The P-side upper bound is therefore provable immediately from
`SearchMachine.polyBudget`.  What remains is the real hard theorem:

  transported God-Move mass at layer n <= M.budget n.

For the current `GodMoveFrame`, whose layer is an external list of satisfiable
CNF challenges, that theorem is exactly a strong lower-bound/anti-shallow-search
statement.  This file therefore separates the proved P-side calibration from
the unproved mass-to-runtime amplification theorem.
-/

namespace SATDepthMachine

/-! ## Runtime budget as a concrete solver capacity -/

/-- The concrete live capacity given by the search machine's polynomial runtime
budget at input size `n`. -/
def GodMoveRuntimeBudgetCapacity
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) : GodMoveSolverCapacity C F where
  solverCapacity := fun M n => M.budget n

/-- The runtime-budget capacity is polynomial on every search machine by the
machine's own `polyBudget` certificate.  This is the P-side calibration. -/
theorem godMoveRuntimeBudgetCapacity_pSide
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) :
    GodMovePolynomialSolverCapacityUpperBound
      (GodMoveRuntimeBudgetCapacity C F) := by
  intro M _hM
  rcases M.polyBudget with ⟨k, c, hpoly⟩
  exact ⟨M.budget, ⟨k, c, hpoly⟩, fun n => Nat.le_refl (M.budget n)⟩

/-- The hard bridge specialized to runtime budget: every transported
God-Move challenge in layer `n` must be paid for by the live runtime budget
`M.budget n`.

This is intentionally a definition, not a theorem.  It is the non-circular
statement the N-frame/God-Move geometry would need to prove for this concrete
capacity. -/
def GodMoveTransportedMassConsumesRuntimeBudget
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame) : Prop :=
  GodMoveTransportedMassConsumesCapacity
    (GodMoveRuntimeBudgetCapacity C F)

/-! ## Conditional closure with real P-side capacity -/

/-- If the runtime-budget bridge is proved for a super-polynomial God-Move
frame, canonical SAT search is deep.  The P-side is now discharged by
`godMoveRuntimeBudgetCapacity_pSide`; only the bridge and the frame lower bound
remain. -/
theorem deepSATSearch_of_godMoveRuntimeBudget
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesRuntimeBudget C F) :
    DeepSATSearch C.toMachineModel :=
  deepSATSearch_of_godMoveSeparateCapacity
    C F (GodMoveRuntimeBudgetCapacity C F)
    hlower
    (godMoveRuntimeBudgetCapacity_pSide C F)
    hconsume

/-- Runtime-budget God-Move closure to no canonical polynomial SAT decision.
-/
theorem noCanonicalSATDecisionInP_of_godMoveRuntimeBudget
    (C : CanonicalMachineSurface)
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesRuntimeBudget C F) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (deepSATSearch_of_godMoveRuntimeBudget C F hlower hconsume)

/-- Described-surface version of the runtime-budget route closure. -/
theorem ktRoute_finalClosure_of_godMoveRuntimeBudget
    (D : DescribedCanonicalSurface)
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesRuntimeBudget D.surface F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
      (noCanonicalSATDecisionInP_of_godMoveRuntimeBudget
        D.surface F hlower hconsume))

/-! ## Guard: the runtime bridge is exactly the hard step -/

/-- If shallow SAT search exists, then no super-polynomial God-Move frame can
satisfy the runtime-budget mass-consumption theorem.  Thus the bridge is
P-vs-NP-strength, while the P-side runtime calibration is genuinely easy. -/
theorem not_godMoveRuntimeBudgetConsumption_of_shallowSearch
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hshallow : ShallowSATSearch C.toMachineModel) :
    ¬ GodMoveTransportedMassConsumesRuntimeBudget C F := by
  intro hconsume
  exact deepSATSearch_of_godMoveRuntimeBudget C F hlower hconsume hshallow

/-- Expanded guard for one correct searcher: if the runtime bridge holds, a
correct solver's polynomial runtime budget becomes super-polynomial. -/
theorem runtimeBudget_superPolynomial_of_godMoveConsumption_and_searchCorrect
    {C : CanonicalMachineSurface}
    (F : GodMoveFrame)
    (hlower : GodMoveFamilyMassLowerBound F)
    (hconsume : GodMoveTransportedMassConsumesRuntimeBudget C F)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    SuperPolynomialMass M.budget :=
  godMove_solverCapacity_superPolynomial_of_searchCorrect
    F (GodMoveRuntimeBudgetCapacity C F) hlower hconsume M hM

/-! ## Axiom trace -/

#print axioms godMoveRuntimeBudgetCapacity_pSide
#print axioms deepSATSearch_of_godMoveRuntimeBudget
#print axioms noCanonicalSATDecisionInP_of_godMoveRuntimeBudget
#print axioms ktRoute_finalClosure_of_godMoveRuntimeBudget
#print axioms not_godMoveRuntimeBudgetConsumption_of_shallowSearch
#print axioms runtimeBudget_superPolynomial_of_godMoveConsumption_and_searchCorrect

end SATDepthMachine
