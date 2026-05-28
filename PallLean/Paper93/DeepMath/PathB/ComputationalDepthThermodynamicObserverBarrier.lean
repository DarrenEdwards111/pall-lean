import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBoundarySchema

/-!
# Thermodynamic observer-relative bridge barrier

This file formalizes the strengthened, still-safe N-frame reading:

* a `P`-class observer is thermodynamically/resource bounded;
* an internal bridge/proof search has finite energy/time/memory/bandwidth cost;
* if every bridge that closes the boundary must either exceed that budget or
  expose the NP/frontier obstruction, then no clean in-budget bridge closes.

This is **not** an absolute unprovability theorem for `P ≠ NP`.  It is a
resource-relative theorem about a specified class of internal bridge
constructions.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Thermodynamic observer frames -/

/-- Finite thermodynamic/resource budget of an observer. -/
structure ThermodynamicBudget : Type where
  energyLimit : Nat
  timeLimit : Nat
  memoryLimit : Nat
  bandwidthLimit : Nat

/-- A P-observer frame equipped with a thermodynamic/resource budget. -/
structure ThermodynamicPObserverFrame
    (enc : SignedFormulaEncoding) extends PObserverFrame enc where
  budget : ThermodynamicBudget

/-- An internal bridge procedure with explicit thermodynamic/resource costs. -/
structure ThermodynamicInternalBridge
    (enc : SignedFormulaEncoding)
    (F : ThermodynamicPObserverFrame enc)
    extends InternalPBridgeProcedure enc F.toPObserverFrame where
  energyCost : Nat
  timeCost : Nat
  memoryCost : Nat
  bandwidthCost : Nat

/-- The bridge stays inside the observer's thermodynamic/resource budget. -/
def WithinThermodynamicBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) : Prop :=
  B.energyCost <= F.budget.energyLimit /\
  B.timeCost <= F.budget.timeLimit /\
  B.memoryCost <= F.budget.memoryLimit /\
  B.bandwidthCost <= F.budget.bandwidthLimit

/-- The bridge exceeds the observer's thermodynamic/resource budget. -/
def ExceedsThermodynamicBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) : Prop :=
  Not (WithinThermodynamicBudget B)

/-! ## Thermodynamic bridge barrier -/

/-- Thermodynamic bridge barrier.

`ExposesNPFrontier B` means the bridge already contains the witness-elimination
/ no-decider / faithful-decoder obstruction it was supposed to derive.

The load-bearing hypothesis is deliberately explicit:
if a bridge closes the boundary, then it either exceeds the observer's finite
budget or exposes that frontier obstruction.
-/
structure ThermodynamicBridgeBarrier
    (enc : SignedFormulaEncoding)
    (F : ThermodynamicPObserverFrame enc) : Type where
  ExposesNPFrontier : ThermodynamicInternalBridge enc F -> Prop
  everyClosureEitherExceedsOrExposes :
    forall B : ThermodynamicInternalBridge enc F,
      B.closesBoundary ->
        ExceedsThermodynamicBudget B \/ ExposesNPFrontier B

/-- A bridge is clean when it does not already expose/smuggle the NP frontier
obstruction. -/
def CleanThermodynamicBridge
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (K : ThermodynamicBridgeBarrier enc F)
    (B : ThermodynamicInternalBridge enc F) : Prop :=
  Not (K.ExposesNPFrontier B)

/-- Single-bridge theorem.

If closing requires either exceeding the thermodynamic budget or exposing the
NP frontier obstruction, then a clean in-budget bridge cannot close. -/
theorem noClosure_of_withinBudget_cleanThermodynamicBridge
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (K : ThermodynamicBridgeBarrier enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B)
    (hclean : CleanThermodynamicBridge K B) :
    Not B.closesBoundary := by
  intro hclose
  rcases K.everyClosureEitherExceedsOrExposes B hclose with hExceeds | hFrontier
  · exact hExceeds hbudget
  · exact hclean hFrontier

/-- Contrapositive: any in-budget bridge that closes is not clean; it exposes
the NP frontier obstruction. -/
theorem exposesNPFrontier_of_withinBudget_closes
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (K : ThermodynamicBridgeBarrier enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B)
    (hclose : B.closesBoundary) :
    K.ExposesNPFrontier B := by
  rcases K.everyClosureEitherExceedsOrExposes B hclose with hExceeds | hFrontier
  · exact False.elim (hExceeds hbudget)
  · exact hFrontier

/-- Thermodynamic observer-relative unprovability:
no clean bridge inside the finite observer budget closes the boundary. -/
def ThermodynamicObserverRelativeUnprovability
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (K : ThermodynamicBridgeBarrier enc F) : Prop :=
  forall B : ThermodynamicInternalBridge enc F,
    WithinThermodynamicBudget B ->
      CleanThermodynamicBridge K B ->
        Not B.closesBoundary

/-- Class-level theorem for a thermodynamic/P-bounded observer. -/
theorem thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (K : ThermodynamicBridgeBarrier enc F) :
    ThermodynamicObserverRelativeUnprovability F K := by
  intro B hbudget hclean
  exact noClosure_of_withinBudget_cleanThermodynamicBridge K B hbudget hclean

/-! ## Relation to the generic observer-boundary schema -/

/-- Generic schema associated to a thermodynamic bridge barrier, with the
frontier predicate restricted to in-budget exposed bridges. -/
def observerBoundarySchema_of_thermodynamicBridgeBarrier
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (K : ThermodynamicBridgeBarrier enc F) :
    ObserverBoundarySchema where
  Bridge := {B : ThermodynamicInternalBridge enc F // WithinThermodynamicBudget B}
  closesBoundary := fun B => B.val.closesBoundary
  exposesFrontier := fun B => K.ExposesNPFrontier B.val

/-- In-budget closure for the thermodynamic barrier supplies the generic
`ClosureRequiresFrontier` premise. -/
theorem closureRequiresFrontier_of_thermodynamicBridgeBarrier
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (K : ThermodynamicBridgeBarrier enc F) :
    ClosureRequiresFrontier
      (observerBoundarySchema_of_thermodynamicBridgeBarrier F K) where
  everyClosureExposes := by
    intro B hclose
    exact exposesNPFrontier_of_withinBudget_closes K B.val B.property hclose

/-- Therefore the thermodynamic barrier is an instance of the generic
observer-boundary schema: clean in-budget bridges cannot close. -/
theorem cleanCannotClose_of_thermodynamicBridgeBarrier
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (K : ThermodynamicBridgeBarrier enc F) :
    (observerBoundarySchema_of_thermodynamicBridgeBarrier F K).CleanCannotClose :=
  cleanCannotClose_of_closureRequiresFrontier
    (observerBoundarySchema_of_thermodynamicBridgeBarrier F K)
    (closureRequiresFrontier_of_thermodynamicBridgeBarrier F K)

/-! ## Kernel-only axiom trace -/

#print axioms noClosure_of_withinBudget_cleanThermodynamicBridge
#print axioms exposesNPFrontier_of_withinBudget_closes
#print axioms thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
#print axioms closureRequiresFrontier_of_thermodynamicBridgeBarrier
#print axioms cleanCannotClose_of_thermodynamicBridgeBarrier

end PallLean.Paper93.DeepMath.PathB
