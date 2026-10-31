import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePolynomialResidualTraceCompatibility
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer8GeneralCircuit

/-!
# A linear-size circuit generates the complete residual label

The polynomial compatibility endpoint shows that an `m`-bit residual fits a
polynomial bit budget.  This file strengthens the countermodel from a bare
function to a concrete general-circuit implementation.

Use one projection circuit for each of the `m` continuation coordinates.
Each output circuit is a single input leaf, so the total size of the
multi-output family is exactly `m`.  Evaluating the family is definitionally
the full-label residual.  It is therefore injective, supports input-blind
factorization of the identity cell, and satisfies the radius-one four-label
law for every redundant code.

Hence neither full continuation preservation nor the separated four-label law
implies superpolynomial circuit work.  A lower-bound argument needs additional
solver-relative structure that the identity projection family does not
satisfy; injectivity alone cannot provide it.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameInputBlindResidualTraceBarrier
open PallLean.Paper93.DeepMath.PathB.NFramePolynomialResidualTraceCompatibility
open PallLean.Paper93.DeepMath.PathB.Layer8

/-! ## Multi-output residual circuit families -/

/-- Evaluate a family of `k` single-output general circuits as a `k`-bit
residual generator. -/
def evalResidualCircuitFamily
    {m k : Nat} (circuits : Fin k -> Circuit m) :
    Assignment m -> Assignment k :=
  fun a j => (circuits j).eval a

/-- The total size of a multi-output circuit family. -/
def residualCircuitFamilySize
    {m k : Nat} (circuits : Fin k -> Circuit m) : Nat :=
  ∑ j, (circuits j).size

/-! ## The coordinate-projection implementation -/

/-- One projection circuit for every continuation coordinate. -/
def coordinateResidualCircuits (m : Nat) : Fin m -> Circuit m :=
  fun i => .input i

/-- Evaluating the coordinate circuits is exactly the full-label residual. -/
theorem coordinateResidualCircuits_eval (m : Nat) :
    evalResidualCircuitFamily (coordinateResidualCircuits m) =
      fullLabelTrace m := by
  funext a i
  rfl

/-- Each coordinate projection has one gate/leaf. -/
theorem coordinateResidualCircuit_size {m : Nat} (i : Fin m) :
    (coordinateResidualCircuits m i).size = 1 := by
  rfl

/-- The complete multi-output residual generator has total circuit size
exactly `m`. -/
theorem coordinateResidualCircuits_totalSize (m : Nat) :
    residualCircuitFamilySize (coordinateResidualCircuits m) = m := by
  simp [residualCircuitFamilySize, coordinateResidualCircuits, Circuit.size]

/-! ## Semantic consequences of the linear implementation -/

/-- The circuit-generated residual is injective. -/
theorem coordinateResidualCircuits_injective (m : Nat) :
    Function.Injective
      (evalResidualCircuitFamily (coordinateResidualCircuits m)) := by
  rw [coordinateResidualCircuits_eval]
  exact fullLabelCell_injective m

/-- The identity semantic cell factors input-blindly through the
circuit-generated residual. -/
theorem coordinateResidualCircuits_inputBlind (m : Nat) :
    CellMapFactorsThroughInputBlindResidual
      (evalResidualCircuitFamily (coordinateResidualCircuits m))
      (id : Assignment m -> Assignment m) := by
  rw [coordinateResidualCircuits_eval]
  exact fullLabelCell_inputBlind_factorization m

/-- The same linear-size residual satisfies fourwise radius-one compatibility
for every redundant continuation code. -/
theorem coordinateResidualCircuits_fourwise
    {m N : Nat} (C : RedundantContinuationCode m N) :
    CellFourwiseRadiusCompatible C
      (id : Assignment m -> Assignment m) (R := 1) :=
  fullLabelCell_fourwise C

/-- Full linear-work package: size exactly `m`, injectivity, input-blind
factorization, and fourwise compatibility. -/
theorem exists_linearCircuitResidual_fourwise_package
    {m N : Nat} (C : RedundantContinuationCode m N) :
    ∃ circuits : Fin m -> Circuit m,
      residualCircuitFamilySize circuits = m ∧
      Function.Injective (evalResidualCircuitFamily circuits) ∧
      CellMapFactorsThroughInputBlindResidual
        (evalResidualCircuitFamily circuits)
        (id : Assignment m -> Assignment m) ∧
      CellFourwiseRadiusCompatible C
        (id : Assignment m -> Assignment m) (R := 1) := by
  exact ⟨coordinateResidualCircuits m,
    coordinateResidualCircuits_totalSize m,
    coordinateResidualCircuits_injective m,
    coordinateResidualCircuits_inputBlind m,
    coordinateResidualCircuits_fourwise C⟩

/-- For every positive polynomial exponent, the concrete circuit family also
fits the corresponding polynomial work budget. -/
theorem coordinateResidualCircuits_polynomialSize
    {m d : Nat} (hm : 1 <= m) (hd : 1 <= d) :
    residualCircuitFamilySize (coordinateResidualCircuits m) <= m ^ d := by
  rw [coordinateResidualCircuits_totalSize]
  exact linear_le_polynomial_budget hm hd

/-- SAT correctness is irrelevant: every alleged solver already admits the
same explicit linear-size residual package. -/
theorem correctnessForces_linearCircuitResidual_fourwise_package
    {U : MachineModel} (D : DecisionMachine U)
    {m N : Nat} (C : RedundantContinuationCode m N) :
    DecidesSAT U D ->
      ∃ circuits : Fin m -> Circuit m,
        residualCircuitFamilySize circuits = m ∧
        Function.Injective (evalResidualCircuitFamily circuits) ∧
        CellMapFactorsThroughInputBlindResidual
          (evalResidualCircuitFamily circuits)
          (id : Assignment m -> Assignment m) ∧
        CellFourwiseRadiusCompatible C
          (id : Assignment m -> Assignment m) (R := 1) := by
  intro _
  exact exists_linearCircuitResidual_fourwise_package C

end PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.coordinateResidualCircuits_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.coordinateResidualCircuits_totalSize
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.coordinateResidualCircuits_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.coordinateResidualCircuits_inputBlind
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.exists_linearCircuitResidual_fourwise_package
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.coordinateResidualCircuits_polynomialSize
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLinearCircuitResidualWitness.correctnessForces_linearCircuitResidual_fourwise_package
