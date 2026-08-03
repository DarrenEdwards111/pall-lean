import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementLocalAccessRedundancyAudit

/-!
# Runtime-calibrated entanglement: the exact unrestricted endpoint

The restricted classes constrain representations, locality, or communication.
To reach all polynomial machines, an entanglement quantity must instead be
charged directly to runtime.  This file states that requirement on the
repository's actual polynomial-budget decision machines.

A `RuntimeCalibratedEntanglement` assigns every decision machine a natural
number profile `charge D n` with two properties:

1. the charge is pointwise bounded by the machine's certified runtime budget;
2. the charge is not polynomially bounded whenever the machine decides SAT.

The first property automatically makes every charge polynomial, because every
`DecisionMachine` already carries an `IsPolynomialBudget` certificate.  Hence
the two fields rule out a correct SAT decider.  Conversely, if there is no SAT
decider, the zero charge satisfies the hard field vacuously.  We therefore
prove the exact equivalence

```text
Nonempty (RuntimeCalibratedEntanglement U) <-> ¬ SATDecisionInP U.
```

This is the formal endpoint requested by the restricted-class audit.  A
non-vacuous construction of the hard field would be the separation theorem;
renaming runtime as entanglement does not create an intermediate lemma.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint

open SATDepthMachine

/-- An unrestricted entanglement charge calibrated to the actual certified
runtime budget of every decision machine. -/
structure RuntimeCalibratedEntanglement (U : MachineModel) where
  charge : DecisionMachine U -> Nat -> Nat
  charge_le_runtime : forall (D : DecisionMachine U) (n : Nat),
    charge D n <= D.budget n
  hard_on_correct : forall D : DecisionMachine U,
    DecidesSAT U D -> ¬ IsPolynomialBudget (charge D)

namespace RuntimeCalibratedEntanglement

/-- Runtime calibration forces every machine's charge to be polynomially
bounded, independently of SAT correctness. -/
theorem charge_isPolynomialBudget
    {U : MachineModel} (E : RuntimeCalibratedEntanglement U)
    (D : DecisionMachine U) :
    IsPolynomialBudget (E.charge D) := by
  obtain ⟨k, c, hbudget⟩ := D.polyBudget
  exact ⟨k, c, fun n => le_trans (E.charge_le_runtime D n) (hbudget n)⟩

/-- Therefore a runtime-calibrated hard entanglement charge rules out every
polynomial-budget SAT decider. -/
theorem no_SATDecisionInP
    {U : MachineModel} (E : RuntimeCalibratedEntanglement U) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  exact E.hard_on_correct D hD (E.charge_isPolynomialBudget D)

end RuntimeCalibratedEntanglement

/-- Under the already-complete SAT lower bound, the zero charge satisfies the
hardness field only because there are no correct machines to test it on. -/
def zeroRuntimeCalibratedEntanglement_of_no_SATDecisionInP
    {U : MachineModel} (hNo : ¬ SATDecisionInP U) :
    RuntimeCalibratedEntanglement U where
  charge := fun _ _ => 0
  charge_le_runtime := fun _ _ => Nat.zero_le _
  hard_on_correct := by
    intro D hD
    exact False.elim (hNo ⟨D, hD⟩)

/-- Exact calibration: the unrestricted time-sound/hard entanglement package
exists iff SAT has no polynomial-budget decider. -/
theorem runtimeCalibratedEntanglement_iff_no_SATDecisionInP
    (U : MachineModel) :
    Nonempty (RuntimeCalibratedEntanglement U) <-> ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨E⟩
    exact E.no_SATDecisionInP
  · intro hNo
    exact ⟨zeroRuntimeCalibratedEntanglement_of_no_SATDecisionInP hNo⟩

/-- The converse witness carries no construction-derived SAT information: its
charge is identically zero. -/
theorem zeroRuntimeCalibratedEntanglement_charge
    {U : MachineModel} (hNo : ¬ SATDecisionInP U)
    (D : DecisionMachine U) (n : Nat) :
    (zeroRuntimeCalibratedEntanglement_of_no_SATDecisionInP hNo).charge D n = 0 :=
  rfl

/-- Consolidated endpoint: the four restricted architectures have a genuine
class lower bound, while a runtime-calibrated global charge is exactly the
unrestricted SAT lower bound. -/
theorem restricted_vs_runtime_frontier
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    (¬ PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant.SATDecisionInClass
      (PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.FourArchitectureEntanglementClass
        U p m d lower)) /\
    (Nonempty (RuntimeCalibratedEntanglement U) <-> ¬ SATDecisionInP U) := by
  constructor
  · exact
      PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.no_SATDecisionInClass_fourArchitecture
        U p m t d lower hp2 ht1 hpt hlow hm
  · exact runtimeCalibratedEntanglement_iff_no_SATDecisionInP U

end PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint.RuntimeCalibratedEntanglement.charge_isPolynomialBudget
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint.RuntimeCalibratedEntanglement.no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint.runtimeCalibratedEntanglement_iff_no_SATDecisionInP
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuntimeCalibrationEndpoint.restricted_vs_runtime_frontier
