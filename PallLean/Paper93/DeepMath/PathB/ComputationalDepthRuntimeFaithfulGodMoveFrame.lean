import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveRuntimeCapacity

/-
# Runtime-faithful God-Move frames

The earlier `GodMoveFrame` is only an external list of satisfiable formulas.
That is not enough to prove

  transportedMass F M n <= M.budget n

because the listed formulas are solved in separate runs.  Counting many solved
formulas does not force one size-`n` computation to pay for all of them.

This file introduces the missing certificate shape.  A runtime-faithful frame
packages, for each solver `M` and layer `n`, a list of disjoint live runtime
slots/events inside a single size-`n` computation.  The transported semantic
God-Move challenges must inject into those slots, and the slots are certified to
fit below `M.searchSteps` on the layer input.  Since `M.steps_le_budget` then
bounds search steps by `M.budget`, the desired runtime bridge follows.

This does not construct the hard frame.  It proves that this is the exact kind
of frame certificate needed to make the bridge real rather than assumed.
-/

namespace SATDepthMachine

/-! ## Live runtime slots for one layer computation -/

/-- A finite list of live runtime slots/events for machine `M` on layer `n`.
The slots are represented by natural time/state indices and certified to be
within one actual run on `input`.  `NoDup` supplies disjointness. -/
structure LiveRuntimeSlotCertificate
    {U : MachineModel}
    (M : SearchMachine U)
    (input : CNF) where
  slots : List Nat
  nodup_slots : slots.Nodup
  slots_within_steps : ∀ s : Nat, s ∈ slots -> s < U.searchSteps M.code input
  slots_length_le_steps : slots.length ≤ U.searchSteps M.code input

/-- The number of disjoint certified runtime slots is at most the actual search
step count of that run.  This is stored in the certificate so later files can
instantiate it from whatever concrete trace/event semantics they build. -/
theorem liveRuntimeSlotCertificate_length_le_steps
    {U : MachineModel}
    {M : SearchMachine U}
    {input : CNF}
    (E : LiveRuntimeSlotCertificate M input) :
    E.slots.length ≤ U.searchSteps M.code input :=
  E.slots_length_le_steps

/-! ## Runtime-faithful refinement of a God-Move frame -/

/-- A runtime-faithful refinement of a semantic God-Move frame.

`layerInput n` is the single size-`n` computation whose live runtime events are
being charged.  For every correct searcher, every transported challenge in layer
`n` is certified to occupy a distinct live runtime slot in that computation.
-/
structure RuntimeFaithfulGodMoveFrame
    (C : CanonicalMachineSurface) where
  frame : GodMoveFrame
  layerInput : Nat -> CNF
  layerInput_size : ∀ n : Nat, (layerInput n).size = n
  liveSlots :
    ∀ M : SearchMachine C.toMachineModel,
      SearchCorrect C.toMachineModel M ->
        ∀ n : Nat, LiveRuntimeSlotCertificate M (layerInput n)
  transportedMass_le_liveSlots :
    ∀ M : SearchMachine C.toMachineModel,
      (hM : SearchCorrect C.toMachineModel M) ->
        ∀ n : Nat,
          GodMoveFrame.transportedMass frame M n ≤
            (liveSlots M hM n).slots.length

/-- Runtime-faithful frames prove the live-step consumption theorem:
transported God-Move mass is bounded by the actual `searchSteps` of the single
layer computation. -/
theorem transportedMass_le_searchSteps_of_runtimeFaithful
    {C : CanonicalMachineSurface}
    (R : RuntimeFaithfulGodMoveFrame C)
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M)
    (n : Nat) :
    GodMoveFrame.transportedMass R.frame M n ≤
      C.toMachineModel.searchSteps M.code (R.layerInput n) := by
  exact Nat.le_trans
    (R.transportedMass_le_liveSlots M hM n)
    (liveRuntimeSlotCertificate_length_le_steps (R.liveSlots M hM n))

/-- Runtime-faithful frames prove the desired budget consumption bridge.  The
`layerInput_size` field connects the actual run to `M.budget n`. -/
theorem godMoveTransportedMassConsumesRuntimeBudget_of_runtimeFaithful
    {C : CanonicalMachineSurface}
    (R : RuntimeFaithfulGodMoveFrame C) :
    GodMoveTransportedMassConsumesRuntimeBudget C R.frame := by
  intro M hM n
  have hsteps :
      GodMoveFrame.transportedMass R.frame M n ≤
        C.toMachineModel.searchSteps M.code (R.layerInput n) :=
    transportedMass_le_searchSteps_of_runtimeFaithful R M hM n
  have hbudget_input :
      C.toMachineModel.searchSteps M.code (R.layerInput n) ≤
        M.budget (R.layerInput n).size :=
    M.steps_le_budget (R.layerInput n)
  have hbudget_n : M.budget (R.layerInput n).size = M.budget n := by
    rw [R.layerInput_size n]
  exact Nat.le_trans hsteps (by simpa [hbudget_n] using hbudget_input)

/-! ## Closure for a runtime-faithful frame -/

/-- If a runtime-faithful frame also has super-polynomial layer mass, the
runtime-budget God-Move route closes.  The only remaining mathematical work is
now construction of such an `R` with `GodMoveFamilyMassLowerBound R.frame`. -/
theorem noCanonicalSATDecisionInP_of_runtimeFaithfulGodMoveFrame
    (C : CanonicalMachineSurface)
    (R : RuntimeFaithfulGodMoveFrame C)
    (hlower : GodMoveFamilyMassLowerBound R.frame) :
    ¬ CanonicalSATDecisionInP C :=
  noCanonicalSATDecisionInP_of_godMoveRuntimeBudget
    C R.frame hlower
    (godMoveTransportedMassConsumesRuntimeBudget_of_runtimeFaithful R)

/-- Described-surface closure for runtime-faithful God-Move frames. -/
theorem ktRoute_finalClosure_of_runtimeFaithfulGodMoveFrame
    (D : DescribedCanonicalSurface)
    (R : RuntimeFaithfulGodMoveFrame D.surface)
    (hlower : GodMoveFamilyMassLowerBound R.frame) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure_of_godMoveRuntimeBudget
    D R.frame hlower
    (godMoveTransportedMassConsumesRuntimeBudget_of_runtimeFaithful R)

/-! ## Axiom trace -/

#print axioms liveRuntimeSlotCertificate_length_le_steps
#print axioms transportedMass_le_searchSteps_of_runtimeFaithful
#print axioms godMoveTransportedMassConsumesRuntimeBudget_of_runtimeFaithful
#print axioms noCanonicalSATDecisionInP_of_runtimeFaithfulGodMoveFrame
#print axioms ktRoute_finalClosure_of_runtimeFaithfulGodMoveFrame

end SATDepthMachine
