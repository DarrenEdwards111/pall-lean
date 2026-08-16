import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerSuperpolyScale

/-!
# Exact decision correctness does not force Gödel-tower doubling

The remaining solver-capture socket cannot be discharged from extensional
YES/NO correctness alone.  A correct decider exposes one Boolean answer per
instance; the corresponding output-only load is constantly one, satisfies the
positive base condition, and fails the first doubling inequality.

This is a finite countermodel to any theorem whose only premise is functional
correctness and whose conclusion is `SolverCaptureDoubling`.  A valid bridge
must additionally connect load to computation-sensitive residual structure.
-/

namespace PallLean.Paper93.DeepMath.PathB.SolverCaptureCorrectnessNoGo

open PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale

/-- Extensional correctness of a Boolean decider for a truth function. -/
def Correct {Input : Type} (truth decider : Input → Bool) : Prop :=
  ∀ x, decider x = truth x

/-- The load visible from the one-bit output alone. -/
def outputOnlyLoad (_level : Nat) : Nat := 1

theorem outputOnlyLoad_base : 1 ≤ outputOnlyLoad 0 := by
  simp [outputOnlyLoad]

theorem outputOnlyLoad_not_doubling :
    ¬ SolverCaptureDoubling outputOnlyLoad := by
  intro capture
  have step0 := capture.doubling 0
  simp [outputOnlyLoad] at step0

/-- Even an exactly correct decider can have only the constant one-bit
extensional load, which does not satisfy tower doubling. -/
theorem correctness_does_not_force_solver_capture :
    ∃ (truth decider : Bool → Bool),
      Correct truth decider ∧ ¬ SolverCaptureDoubling outputOnlyLoad := by
  refine ⟨id, id, ?_, outputOnlyLoad_not_doubling⟩
  intro x
  rfl

/-- The extra property a successful route must supply: load is not merely the
output alphabet size, but a computation-faithful semantic measure.  This
structure names the obligation without asserting that arbitrary circuits have
it. -/
structure ComputationFaithfulLoad {Input : Type}
    (truth decider : Input → Bool) (load : Nat → Nat) : Prop where
  correct : Correct truth decider
  capture : SolverCaptureDoubling load
  not_output_only : load ≠ outputOnlyLoad

theorem faithful_load_breaks_polynomial_at_witness
    {Input : Type} {truth decider : Input → Bool} {load : Nat → Nat}
    (faithful : ComputationFaithfulLoad truth decider load)
    {n k C : Nat} (scale : SuperpolyScaleWitness n k C) :
    n ^ C < load k :=
  polynomial_budget_broken faithful.capture scale

end PallLean.Paper93.DeepMath.PathB.SolverCaptureCorrectnessNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.SolverCaptureCorrectnessNoGo.outputOnlyLoad_not_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.SolverCaptureCorrectnessNoGo.correctness_does_not_force_solver_capture
#print axioms PallLean.Paper93.DeepMath.PathB.SolverCaptureCorrectnessNoGo.faithful_load_breaks_polynomial_at_witness
