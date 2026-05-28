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

/-! ## Thermodynamic cost semantics

The first version of this file used `energyCost`, `timeCost`, `memoryCost`, and
`bandwidthCost` as uninterpreted labels.  The definitions below replace those
labels with an explicit symbolic thermodynamic model:

* a computation is a finite trace of elementary steps;
* each step has irreversible bit erasures, active energy overhead, elapsed time,
  live memory cells, and transmitted bits;
* Landauer cost is represented in scaled natural units by `landauerUnit`;
* trace energy is `landauerUnit * totalErasedBits + activeEnergy`.

This is still a discrete abstract model, not a numerical physics experiment;
but the cost words now have actual semantics and a checked Landauer-style lower
bound rather than being free names.
-/

/-- Physical constants in scaled natural units.  `landauerUnit` represents
`kT ln 2` after choosing units/temperature scale. -/
structure ThermodynamicConstants : Type where
  landauerUnit : Nat

/-- One elementary computational step in the resource semantics. -/
structure ThermodynamicStep : Type where
  /-- Irreversibly erased bits in this step. -/
  erasedBits : Nat
  /-- Non-erasure active energy overhead in the same scaled units. -/
  activeEnergy : Nat
  /-- Discrete elapsed time ticks. -/
  timeTicks : Nat
  /-- Live memory cells required during this step. -/
  liveMemory : Nat
  /-- Bits transmitted across the observer boundary/channel. -/
  transmittedBits : Nat

/-- Total erased bits over a trace. -/
def traceErasedBits : List ThermodynamicStep -> Nat
  | [] => 0
  | s :: rest => s.erasedBits + traceErasedBits rest

/-- Total active/non-erasure energy over a trace. -/
def traceActiveEnergy : List ThermodynamicStep -> Nat
  | [] => 0
  | s :: rest => s.activeEnergy + traceActiveEnergy rest

/-- Total elapsed time ticks over a trace. -/
def traceTime : List ThermodynamicStep -> Nat
  | [] => 0
  | s :: rest => s.timeTicks + traceTime rest

/-- Peak live memory over a trace. -/
def tracePeakMemory : List ThermodynamicStep -> Nat
  | [] => 0
  | s :: rest => max s.liveMemory (tracePeakMemory rest)

/-- Total transmitted bits over a trace. -/
def traceBandwidth : List ThermodynamicStep -> Nat
  | [] => 0
  | s :: rest => s.transmittedBits + traceBandwidth rest

/-- Landauer lower-bound component of a trace. -/
def traceLandauerEnergy
    (c : ThermodynamicConstants)
    (steps : List ThermodynamicStep) : Nat :=
  c.landauerUnit * traceErasedBits steps

/-- Total energy semantics for a trace: Landauer erasure cost plus active
non-erasure overhead. -/
def traceEnergy
    (c : ThermodynamicConstants)
    (steps : List ThermodynamicStep) : Nat :=
  traceLandauerEnergy c steps + traceActiveEnergy steps

/-- Checked Landauer lower bound in the symbolic model. -/
theorem traceEnergy_ge_landauer
    (c : ThermodynamicConstants)
    (steps : List ThermodynamicStep) :
    traceLandauerEnergy c steps <= traceEnergy c steps :=
  Nat.le_add_right _ _

/-- Aggregated resource usage computed from the trace semantics. -/
structure TraceResourceUsage : Type where
  energy : Nat
  time : Nat
  memory : Nat
  bandwidth : Nat

/-- Compute all observer resources from a concrete trace. -/
def traceResourceUsage
    (c : ThermodynamicConstants)
    (steps : List ThermodynamicStep) : TraceResourceUsage where
  energy := traceEnergy c steps
  time := traceTime steps
  memory := tracePeakMemory steps
  bandwidth := traceBandwidth steps

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

/-- An internal bridge procedure with a concrete thermodynamic trace.

The cost fields are no longer independent labels: `costs_match_trace` states
that they are exactly the values computed from `constants` and `trace`.  This
is the key semantic upgrade over the earlier wrapper. -/
structure ThermodynamicInternalBridge
    (enc : SignedFormulaEncoding)
    (F : ThermodynamicPObserverFrame enc)
    extends InternalPBridgeProcedure enc F.toPObserverFrame where
  constants : ThermodynamicConstants
  trace : List ThermodynamicStep
  energyCost : Nat
  timeCost : Nat
  memoryCost : Nat
  bandwidthCost : Nat
  costs_match_trace :
    energyCost = (traceResourceUsage constants trace).energy /\
    timeCost = (traceResourceUsage constants trace).time /\
    memoryCost = (traceResourceUsage constants trace).memory /\
    bandwidthCost = (traceResourceUsage constants trace).bandwidth

/-- The semantic resource usage of a bridge, computed from its trace. -/
def bridgeTraceUsage
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) : TraceResourceUsage :=
  traceResourceUsage B.constants B.trace

/-- The bridge stays inside the observer's thermodynamic/resource budget,
using the trace-computed costs. -/
def WithinThermodynamicBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) : Prop :=
  (bridgeTraceUsage B).energy <= F.budget.energyLimit /\
  (bridgeTraceUsage B).time <= F.budget.timeLimit /\
  (bridgeTraceUsage B).memory <= F.budget.memoryLimit /\
  (bridgeTraceUsage B).bandwidth <= F.budget.bandwidthLimit

/-- The bridge exceeds the observer's thermodynamic/resource budget. -/
def ExceedsThermodynamicBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) : Prop :=
  Not (WithinThermodynamicBudget B)

/-- The bridge's trace-level Landauer lower bound transfers to the bridge's
semantic energy usage. -/
theorem bridge_energy_ge_landauer
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F) :
    traceLandauerEnergy B.constants B.trace <= (bridgeTraceUsage B).energy :=
  traceEnergy_ge_landauer B.constants B.trace

/-- If a bridge is within budget, then its Landauer erasure cost alone is within
the observer's energy budget.  This is the first non-vacuous thermodynamic
constraint: any in-budget bridge has only polynomial/finite erasure capacity in
this symbolic model. -/
theorem landauerCost_le_energyLimit_of_withinBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B) :
    traceLandauerEnergy B.constants B.trace <= F.budget.energyLimit :=
  Nat.le_trans (bridge_energy_ge_landauer B) hbudget.1

/-- A sufficient semantic reason for exceeding budget: the Landauer lower bound
alone is already larger than the observer's energy allowance. -/
theorem exceedsBudget_of_energyLimit_lt_landauerCost
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    (h : F.budget.energyLimit < traceLandauerEnergy B.constants B.trace) :
    ExceedsThermodynamicBudget B := by
  intro hbudget
  exact Nat.not_lt_of_ge (landauerCost_le_energyLimit_of_withinBudget B hbudget) h

/-! ## Explicit erasure/energy capacity bounds -/

/-- A bridge semantically requires at least `requiredBits` irreversible bit
erasures when its concrete trace erases at least that many bits. -/
def BridgeRequiresErasureAtLeast
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    (requiredBits : Nat) : Prop :=
  requiredBits <= traceErasedBits B.trace

/-- The Landauer energy needed for a specified erasure requirement. -/
def requiredErasureLandauerEnergy
    (c : ThermodynamicConstants)
    (requiredBits : Nat) : Nat :=
  c.landauerUnit * requiredBits

/-- If a bridge trace erases at least `requiredBits`, then the Landauer cost
for `requiredBits` is below the full trace Landauer cost. -/
theorem requiredErasureLandauerEnergy_le_traceLandauer
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    {requiredBits : Nat}
    (hreq : BridgeRequiresErasureAtLeast B requiredBits) :
    requiredErasureLandauerEnergy B.constants requiredBits <=
      traceLandauerEnergy B.constants B.trace := by
  dsimp [BridgeRequiresErasureAtLeast] at hreq
  dsimp [requiredErasureLandauerEnergy, traceLandauerEnergy]
  exact Nat.mul_le_mul_left B.constants.landauerUnit hreq

/-- In-budget bridges can only require erasures whose Landauer cost fits inside
the observer's energy limit. -/
theorem requiredErasureLandauerEnergy_le_energyLimit_of_withinBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    {requiredBits : Nat}
    (hbudget : WithinThermodynamicBudget B)
    (hreq : BridgeRequiresErasureAtLeast B requiredBits) :
    requiredErasureLandauerEnergy B.constants requiredBits <=
      F.budget.energyLimit :=
  Nat.le_trans
    (requiredErasureLandauerEnergy_le_traceLandauer B hreq)
    (landauerCost_le_energyLimit_of_withinBudget B hbudget)

/-- If a bridge must erase enough bits that the Landauer cost of just those
erasures exceeds the observer's energy limit, then the bridge is outside the
thermodynamic budget. -/
theorem exceedsBudget_of_requiredErasureEnergyLimit_lt
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    {requiredBits : Nat}
    (hreq : BridgeRequiresErasureAtLeast B requiredBits)
    (henergy :
      F.budget.energyLimit <
        requiredErasureLandauerEnergy B.constants requiredBits) :
    ExceedsThermodynamicBudget B := by
  intro hbudget
  exact Nat.not_lt_of_ge
    (requiredErasureLandauerEnergy_le_energyLimit_of_withinBudget
      B hbudget hreq)
    henergy

/-- Landauer erasure capacity induced by an observer's energy limit, in bits.
The theorem using this definition assumes `landauerUnit > 0`; if the unit is
zero, erasures carry no energy in the symbolic model. -/
def LandauerErasureCapacity
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (c : ThermodynamicConstants) : Nat :=
  F.budget.energyLimit / c.landauerUnit

/-- If the Landauer unit is positive, an in-budget bridge erases at most the
energy-limit divided by the Landauer unit.  This is the concrete finite
erasure capacity of the thermodynamic P-observer. -/
theorem traceErasedBits_le_landauerCapacity_of_withinBudget
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    (hunit : 0 < B.constants.landauerUnit)
    (hbudget : WithinThermodynamicBudget B) :
    traceErasedBits B.trace <=
      LandauerErasureCapacity F B.constants := by
  dsimp [LandauerErasureCapacity]
  rw [Nat.le_div_iff_mul_le hunit]
  have hland :
      B.constants.landauerUnit * traceErasedBits B.trace <=
        F.budget.energyLimit :=
    landauerCost_le_energyLimit_of_withinBudget B hbudget
  simpa [Nat.mul_comm, traceLandauerEnergy] using hland

/-- Equivalent strict form: if the Landauer cost of `requiredBits` is above the
energy budget, then any in-budget bridge erases strictly fewer than
`requiredBits`. -/
theorem traceErasedBits_lt_required_of_energyLimit_lt_requiredLandauer
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    {requiredBits : Nat}
    (hbudget : WithinThermodynamicBudget B)
    (henergy :
      F.budget.energyLimit <
        requiredErasureLandauerEnergy B.constants requiredBits) :
    traceErasedBits B.trace < requiredBits := by
  by_contra hnot
  have hreq : BridgeRequiresErasureAtLeast B requiredBits :=
    Nat.le_of_not_gt hnot
  exact Nat.not_lt_of_ge
    (requiredErasureLandauerEnergy_le_energyLimit_of_withinBudget
      B hbudget hreq)
    henergy

/-- A power-time envelope for an observer: total available energy is bounded by
`powerLimit * timeLimit`.  This is the standard physical way finite power and
finite time imply a finite energy budget. -/
structure PowerTimeEnergyEnvelope
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc) : Type where
  powerLimit : Nat
  energyLimit_le_powerTime :
    F.budget.energyLimit <= powerLimit * F.budget.timeLimit

/-- Power-time form of the erasure obstruction: if the Landauer cost of the
required erasures is larger than all energy available from finite power over
the observer's time budget, then the bridge exceeds the thermodynamic budget. -/
theorem exceedsBudget_of_requiredErasurePowerTime_lt
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (B : ThermodynamicInternalBridge enc F)
    (E : PowerTimeEnergyEnvelope F)
    {requiredBits : Nat}
    (hreq : BridgeRequiresErasureAtLeast B requiredBits)
    (hpower :
      E.powerLimit * F.budget.timeLimit <
        requiredErasureLandauerEnergy B.constants requiredBits) :
    ExceedsThermodynamicBudget B :=
  exceedsBudget_of_requiredErasureEnergyLimit_lt B hreq
    (lt_of_le_of_lt E.energyLimit_le_powerTime hpower)

/-! ## Complexity-side erasure lower-bound interface -/

/-- Complexity-side erasure lower bound for a bridge family.

This is the exact missing P/NP-content hook: closing the boundary must force
the concrete trace to erase at least `requiredBits B` independent bits or
counterfactual branches.  The structure does not prove that claim for SAT; it
names the theorem a concrete complexity argument would have to supply. -/
structure ComplexityErasureLowerBound
    (enc : SignedFormulaEncoding)
    (F : ThermodynamicPObserverFrame enc) : Type where
  requiredBits : ThermodynamicInternalBridge enc F -> Nat
  everyClosureRequiresErasure :
    forall B : ThermodynamicInternalBridge enc F,
      B.closesBoundary ->
        BridgeRequiresErasureAtLeast B (requiredBits B)

namespace ComplexityErasureLowerBound

/-- The standard binomial counterfactual-branch floor used throughout the
God-Move/strict-port chain.  It is the formal stand-in for the
`n^{Theta(log n)}` independent witness/counterfactual family; this file does
not prove that SAT closure forces this floor, it records the thermodynamic
consequence if a separate complexity theorem supplies that fact. -/
def independentBranchFloor (n : Nat) : Nat :=
  Nat.choose (n / 3) (Nat.log 2 n)

/-- At scale `n`, the complexity-side lower bound dominates the binomial
independent-branch floor for every closing bridge. -/
structure IndependentBranchErasureLowerBoundAtScale
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (n : Nat) : Prop where
  everyClosureRequiresBranchFloor :
    forall B : ThermodynamicInternalBridge enc F,
      B.closesBoundary ->
        independentBranchFloor n <= L.requiredBits B

/-- Closing plus a complexity-side erasure lower bound implies the required
Landauer erasure energy fits inside any in-budget observer. -/
theorem requiredEnergy_le_energyLimit_of_withinBudget_closes
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hbudget : WithinThermodynamicBudget B)
    (hclose : B.closesBoundary) :
    requiredErasureLandauerEnergy B.constants (L.requiredBits B) <=
      F.budget.energyLimit :=
  requiredErasureLandauerEnergy_le_energyLimit_of_withinBudget
    B hbudget (L.everyClosureRequiresErasure B hclose)

/-- If the complexity-side lower bound costs more Landauer energy than the
observer has, then the bridge cannot both close and stay in budget. -/
theorem not_withinBudget_of_closes_energyLimit_lt_requiredEnergy
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hclose : B.closesBoundary)
    (henergy :
      F.budget.energyLimit <
        requiredErasureLandauerEnergy B.constants (L.requiredBits B)) :
    Not (WithinThermodynamicBudget B) := by
  intro hbudget
  exact Nat.not_lt_of_ge
    (L.requiredEnergy_le_energyLimit_of_withinBudget_closes
      B hbudget hclose)
    henergy

/-- Equivalent `ExceedsThermodynamicBudget` form of the previous theorem. -/
theorem exceedsBudget_of_closes_energyLimit_lt_requiredEnergy
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (B : ThermodynamicInternalBridge enc F)
    (hclose : B.closesBoundary)
    (henergy :
      F.budget.energyLimit <
        requiredErasureLandauerEnergy B.constants (L.requiredBits B)) :
    ExceedsThermodynamicBudget B :=
  L.not_withinBudget_of_closes_energyLimit_lt_requiredEnergy B hclose henergy

/-- Power-time version: closing exceeds budget whenever the complexity-side
required erasures cost more Landauer energy than finite power over the
observer's time window can supply. -/
theorem exceedsBudget_of_closes_powerTime_lt_requiredEnergy
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (B : ThermodynamicInternalBridge enc F)
    (E : PowerTimeEnergyEnvelope F)
    (hclose : B.closesBoundary)
    (hpower :
      E.powerLimit * F.budget.timeLimit <
        requiredErasureLandauerEnergy B.constants (L.requiredBits B)) :
    ExceedsThermodynamicBudget B :=
  L.exceedsBudget_of_closes_energyLimit_lt_requiredEnergy B hclose
    (lt_of_le_of_lt E.energyLimit_le_powerTime hpower)

/-- If closing forces at least the binomial independent-branch floor, then the
Landauer cost of that floor is a lower bound on the bridge's required erasure
energy. -/
theorem branchFloorEnergy_le_requiredEnergy_of_closes
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    {L : ComplexityErasureLowerBound enc F}
    {n : Nat}
    (H : IndependentBranchErasureLowerBoundAtScale L n)
    (B : ThermodynamicInternalBridge enc F)
    (hclose : B.closesBoundary) :
    requiredErasureLandauerEnergy B.constants (independentBranchFloor n) <=
      requiredErasureLandauerEnergy B.constants (L.requiredBits B) :=
  Nat.mul_le_mul_left B.constants.landauerUnit
    (H.everyClosureRequiresBranchFloor B hclose)

/-- Binomial-branch version of the thermodynamic obstruction: if a closing
bridge must resolve the `choose(n/3, log n)` independent branch floor and that
floor alone costs more Landauer energy than the observer has, then the bridge
exceeds the budget. -/
theorem exceedsBudget_of_closes_branchFloorEnergyGap
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    {L : ComplexityErasureLowerBound enc F}
    {n : Nat}
    (H : IndependentBranchErasureLowerBoundAtScale L n)
    (B : ThermodynamicInternalBridge enc F)
    (hclose : B.closesBoundary)
    (henergy :
      F.budget.energyLimit <
        requiredErasureLandauerEnergy B.constants (independentBranchFloor n)) :
    ExceedsThermodynamicBudget B :=
  L.exceedsBudget_of_closes_energyLimit_lt_requiredEnergy B hclose
    (lt_of_lt_of_le henergy
      (branchFloorEnergy_le_requiredEnergy_of_closes H B hclose))

/-- Power-time version of the binomial-branch obstruction. -/
theorem exceedsBudget_of_closes_branchFloorPowerTimeGap
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    {L : ComplexityErasureLowerBound enc F}
    {n : Nat}
    (H : IndependentBranchErasureLowerBoundAtScale L n)
    (B : ThermodynamicInternalBridge enc F)
    (E : PowerTimeEnergyEnvelope F)
    (hclose : B.closesBoundary)
    (hpower :
      E.powerLimit * F.budget.timeLimit <
        requiredErasureLandauerEnergy B.constants (independentBranchFloor n)) :
    ExceedsThermodynamicBudget B :=
  exceedsBudget_of_closes_branchFloorEnergyGap H B hclose
    (lt_of_le_of_lt E.energyLimit_le_powerTime hpower)

end ComplexityErasureLowerBound

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

namespace ComplexityErasureLowerBound

/-- A complexity erasure lower bound and an energy gap instantiate the generic
thermodynamic bridge barrier with a trivial frontier predicate.  In this case
closure is ruled out by budget alone; no NP-frontier smuggling predicate is
needed. -/
def toThermodynamicBridgeBarrier_of_energyGap
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    (L : ComplexityErasureLowerBound enc F)
    (energyGap :
      forall B : ThermodynamicInternalBridge enc F,
        B.closesBoundary ->
          F.budget.energyLimit <
            requiredErasureLandauerEnergy B.constants (L.requiredBits B)) :
    ThermodynamicBridgeBarrier enc F where
  ExposesNPFrontier := fun _ => False
  everyClosureEitherExceedsOrExposes := by
    intro B hclose
    exact Or.inl
      (L.exceedsBudget_of_closes_energyLimit_lt_requiredEnergy
        B hclose (energyGap B hclose))

/-- Therefore, under a concrete complexity-side erasure lower bound and an
energy gap, no clean in-budget bridge closes. -/
theorem observerRelativeUnprovability_of_complexityErasureEnergyGap
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    (L : ComplexityErasureLowerBound enc F)
    (energyGap :
      forall B : ThermodynamicInternalBridge enc F,
        B.closesBoundary ->
          F.budget.energyLimit <
            requiredErasureLandauerEnergy B.constants (L.requiredBits B)) :
    ThermodynamicObserverRelativeUnprovability
      F (L.toThermodynamicBridgeBarrier_of_energyGap energyGap) :=
  thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
    F (L.toThermodynamicBridgeBarrier_of_energyGap energyGap)

end ComplexityErasureLowerBound

namespace ComplexityErasureLowerBound

/-- Binomial-branch-floor version of the generic thermodynamic bridge barrier.
This is the formal shape requested by the complexity side: once an independent
witness/counterfactual-branch lower bound is proved, finite thermodynamic
budget alone rules out clean closure whenever the floor's Landauer cost exceeds
the observer's energy budget. -/
def toThermodynamicBridgeBarrier_of_branchFloorEnergyGap
    {enc : SignedFormulaEncoding}
    {F : ThermodynamicPObserverFrame enc}
    {L : ComplexityErasureLowerBound enc F}
    {n : Nat}
    (H : IndependentBranchErasureLowerBoundAtScale L n)
    (energyGap :
      forall B : ThermodynamicInternalBridge enc F,
        B.closesBoundary ->
          F.budget.energyLimit <
            requiredErasureLandauerEnergy B.constants (independentBranchFloor n)) :
    ThermodynamicBridgeBarrier enc F where
  ExposesNPFrontier := fun _ => False
  everyClosureEitherExceedsOrExposes := by
    intro B hclose
    exact Or.inl
      (exceedsBudget_of_closes_branchFloorEnergyGap
        H B hclose (energyGap B hclose))

/-- Observer-relative unprovability from a binomial independent-branch lower
bound plus a thermodynamic energy gap. -/
theorem observerRelativeUnprovability_of_branchFloorEnergyGap
    {enc : SignedFormulaEncoding}
    (F : ThermodynamicPObserverFrame enc)
    {L : ComplexityErasureLowerBound enc F}
    {n : Nat}
    (H : IndependentBranchErasureLowerBoundAtScale L n)
    (energyGap :
      forall B : ThermodynamicInternalBridge enc F,
        B.closesBoundary ->
          F.budget.energyLimit <
            requiredErasureLandauerEnergy B.constants (independentBranchFloor n)) :
    ThermodynamicObserverRelativeUnprovability
      F (toThermodynamicBridgeBarrier_of_branchFloorEnergyGap H energyGap) :=
  thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
    F (toThermodynamicBridgeBarrier_of_branchFloorEnergyGap H energyGap)

end ComplexityErasureLowerBound

/-! ## Kernel-only axiom trace -/

#print axioms noClosure_of_withinBudget_cleanThermodynamicBridge
#print axioms exposesNPFrontier_of_withinBudget_closes
#print axioms thermodynamicObserverRelativeUnprovability_of_bridgeBarrier
#print axioms closureRequiresFrontier_of_thermodynamicBridgeBarrier
#print axioms cleanCannotClose_of_thermodynamicBridgeBarrier
#print axioms requiredErasureLandauerEnergy_le_energyLimit_of_withinBudget
#print axioms exceedsBudget_of_requiredErasureEnergyLimit_lt
#print axioms traceErasedBits_le_landauerCapacity_of_withinBudget
#print axioms traceErasedBits_lt_required_of_energyLimit_lt_requiredLandauer
#print axioms exceedsBudget_of_requiredErasurePowerTime_lt
#print axioms ComplexityErasureLowerBound.requiredEnergy_le_energyLimit_of_withinBudget_closes
#print axioms ComplexityErasureLowerBound.exceedsBudget_of_closes_energyLimit_lt_requiredEnergy
#print axioms ComplexityErasureLowerBound.exceedsBudget_of_closes_powerTime_lt_requiredEnergy
#print axioms ComplexityErasureLowerBound.observerRelativeUnprovability_of_complexityErasureEnergyGap
#print axioms ComplexityErasureLowerBound.exceedsBudget_of_closes_branchFloorEnergyGap
#print axioms ComplexityErasureLowerBound.exceedsBudget_of_closes_branchFloorPowerTimeGap
#print axioms ComplexityErasureLowerBound.observerRelativeUnprovability_of_branchFloorEnergyGap

end PallLean.Paper93.DeepMath.PathB
