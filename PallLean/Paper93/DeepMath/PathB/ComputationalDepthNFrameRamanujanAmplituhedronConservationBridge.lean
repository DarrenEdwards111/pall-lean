import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConcreteLagrangianBoundaryAudit

/-!
# N-frame conservation bridge: Ramanujan separation through amplituhedron cells

The overview in `p vs np1.pdf` proposes the chain

```text
Ramanujan--Tseitin boundary witness
  -> N-frame Lagrangian / Farkas dual certificate
  -> holographic amplituhedron projection
  -> identity-label preservation
  -> exponential positive-cell lower bound.
```

The existing geometric extraction file isolated `preservesLabels` as its hard
field.  This file proves that the proposed conservation mechanism really can
discharge that field.  It factors the argument into two independently visible
laws:

1. `conservesAction`: the amplituhedron projection preserves the on-shell
   N-frame action;
2. `ramanujanActionSeparates`: different hard residual labels have different
   raw action, as certified by the Ramanujan/identity-minor side.

If two branches land in the same positive cell, their cell actions agree;
conservation then makes their raw actions agree, and Ramanujan action
separation forces their labels to agree.  This constructs the previously
missing `SoundOnFoolingFamily` theorem and feeds the existing positive-cell
contradiction.

The final audit checks the current concrete proxy.  Its closed form depends
only on projection rank and ignores the workload family.  At a fixed gauge it
therefore assigns exactly the same action to every family, so it cannot yet
prove `ramanujanActionSeparates`.  A future successful implementation must
replace/refine that family-blind proxy with the genuine local edge-energy,
identity-minor, and log-det/Farkas action whose Ramanujan separation theorem is
the new load-bearing lemma.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge

open SATDepthMachine
open PallLean.Paper93.NFrame
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPPACAmplituhedronProjection
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction

/-! ## Lagrangian-stabilized geometric extraction -/

/-- The overview's full one-decider certificate, with label preservation
derived rather than assumed. -/
structure LagrangianStabilizedRamanujanAmplituhedronFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  rawTranscript : Type
  holographicScreen : Type
  positiveCellType : Type
  fintypePositiveCell : Fintype positiveCellType
  rawObserver : TranscriptObserver rawTranscript
  holographic : HolographicProjectionStage rawTranscript holographicScreen
  amplituhedron : AmplituhedronPositiveCellStage holographicScreen positiveCellType
  fam : FoolingResidualFamily m
  rawAction : rawTranscript -> Real
  cellAction : positiveCellType -> Real
  /-- Amplituhedron/holographic on-shell conservation law. -/
  conservesAction : forall r,
    rawAction r = cellAction (composedPositiveProjection holographic amplituhedron r)
  /-- Ramanujan--Tseitin / identity-minor action separation. -/
  ramanujanActionSeparates : forall a b : Assignment m,
    fam.label a ≠ fam.label b ->
      rawAction (rawObserver (fam.instanceOf a)) ≠
        rawAction (rawObserver (fam.instanceOf b))
  polyPositiveCells : @Fintype.card positiveCellType fintypePositiveCell <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace LagrangianStabilizedRamanujanAmplituhedronFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- Conservation plus Ramanujan action separation proves the missing positive
cell label-preservation theorem. -/
theorem preservesLabels
    (E : LagrangianStabilizedRamanujanAmplituhedronFor U D hD) :
    SoundOnFoolingFamily
      (fun x => composedPositiveProjection E.holographic E.amplituhedron
        (E.rawObserver x)) E.fam := by
  intro a b hCell
  by_contra hLabels
  have hDifferent := E.ramanujanActionSeparates a b hLabels
  have hCell' :
      composedPositiveProjection E.holographic E.amplituhedron
          (E.rawObserver (E.fam.instanceOf a)) =
        composedPositiveProjection E.holographic E.amplituhedron
          (E.rawObserver (E.fam.instanceOf b)) := by
    simpa only using hCell
  apply hDifferent
  calc
    E.rawAction (E.rawObserver (E.fam.instanceOf a))
        = E.cellAction
            (composedPositiveProjection E.holographic E.amplituhedron
              (E.rawObserver (E.fam.instanceOf a))) :=
          E.conservesAction _
    _ = E.cellAction
            (composedPositiveProjection E.holographic E.amplituhedron
              (E.rawObserver (E.fam.instanceOf b))) := by rw [hCell']
    _ = E.rawAction (E.rawObserver (E.fam.instanceOf b)) :=
          (E.conservesAction _).symm

/-- Forget the derived-certificate presentation to the existing geometric
extraction interface. -/
def toGeometricExtraction
    (E : LagrangianStabilizedRamanujanAmplituhedronFor U D hD) :
    RamanujanHolographicAmplituhedronExtractionFor U D hD where
  m := E.m
  k := E.k
  rawTranscript := E.rawTranscript
  holographicScreen := E.holographicScreen
  positiveCellType := E.positiveCellType
  fintypePositiveCell := E.fintypePositiveCell
  rawObserver := E.rawObserver
  holographic := E.holographic
  amplituhedron := E.amplituhedron
  fam := E.fam
  preservesLabels := E.preservesLabels
  polyPositiveCells := E.polyPositiveCells
  expGap := E.expGap

/-- The full conservation bridge contradicts a correct polynomial SAT
decider's polynomial positive-cell boundary. -/
theorem impossible
    (E : LagrangianStabilizedRamanujanAmplituhedronFor U D hD) : False :=
  E.toGeometricExtraction.impossible_via_positive_cells

end LagrangianStabilizedRamanujanAmplituhedronFor

/-! ## Global cash-out -/

/-- Uniform overview theorem: every alleged SAT decider receives the combined
Ramanujan/Lagrangian/amplituhedron certificate. -/
def LagrangianStabilizedRamanujanAmplituhedronForPTimeSAT
    (U : MachineModel) : Prop :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    Nonempty (LagrangianStabilizedRamanujanAmplituhedronFor U D hD)

/-- The combined conservation bridge rules out polynomial SAT decision. -/
theorem no_SATDecisionInP_of_lagrangianRamanujanAmplituhedron
    {U : MachineModel}
    (H : LagrangianStabilizedRamanujanAmplituhedronForPTimeSAT U) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨E⟩ := H D hD
  exact E.impossible

/-! ## Audit of the current concrete proxy -/

/-- The current proxy Lagrangian is workload-family blind at every fixed
gauge.  This follows from its rank-only closed form. -/
theorem current_nframeLagrangian_family_invariant
    {N : Nat}
    (family₁ family₂ : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) :
    nframeLagrangian family₁ gauge = nframeLagrangian family₂ gauge := by
  rw [nframeLagrangian_eq_proxy, nframeLagrangian_eq_proxy]

/-- A constant raw action cannot satisfy Ramanujan action separation whenever
the fooling family contains a pair with different labels. -/
theorem constant_action_cannot_separate_labels
    {m : Nat} {raw : Type}
    (obs : TranscriptObserver raw) (fam : FoolingResidualFamily m)
    (rawAction : raw -> Real) (c : Real)
    (hConstant : forall r, rawAction r = c)
    (a b : Assignment m) (hLabels : fam.label a ≠ fam.label b) :
    ¬ (forall x y : Assignment m,
      fam.label x ≠ fam.label y ->
        rawAction (obs (fam.instanceOf x)) ≠
          rawAction (obs (fam.instanceOf y))) := by
  intro hSeparate
  have hNe := hSeparate a b hLabels
  exact hNe (by simp only [hConstant])

/-- In particular, varying the encoded workload family while retaining one
fixed concrete gauge cannot generate the action separation required by the
Ramanujan conservation bridge. -/
theorem fixedGauge_proxy_cannot_distinguish_two_families
    {N : Nat}
    (family₁ family₂ : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) :
    ¬ nframeLagrangian family₁ gauge ≠ nframeLagrangian family₂ gauge := by
  intro hNe
  exact hNe
    (current_nframeLagrangian_family_invariant family₁ family₂ gauge)

end PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge.LagrangianStabilizedRamanujanAmplituhedronFor.preservesLabels
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge.LagrangianStabilizedRamanujanAmplituhedronFor.impossible
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge.no_SATDecisionInP_of_lagrangianRamanujanAmplituhedron
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanAmplituhedronConservationBridge.current_nframeLagrangian_family_invariant
