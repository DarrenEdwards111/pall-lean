import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLagrangianConservationEndpoint
import PallLean.Paper93.NFrame.PiStarExistence

/-!
# Concrete N-frame Lagrangian boundary audit

The preceding endpoint established that an N-frame conservation law would
force solver anti-correlation if the conserved charge had two SAT-specific
boundary conditions: positive initial debt and zero terminal debt under a
correct answer.  This file instantiates that proposal with the repository's
actual three-term `nframeLagrangian` proxy.

The literal action cannot satisfy the terminal-zero condition.  Its closed
form is

`2 * rank + 1 / (1 + rank)`,

and the existing proxy theorem proves it is at least `1` for every gauge.  At
the canonical trivial/Pi-star gauge its value is exactly `1`.  Therefore the
literal conserved action has a positive baseline at both ends of every
trajectory, independently of solver correctness.

Subtracting the baseline produces a conserved excess action, but at the
canonical minimizer that excess is identically zero, so it supplies no
positive initial SAT debt.  For any exactly conserved action, demanding a
positive initial excess and zero correct terminal excess is once again the
semantic anti-correlation boundary mismatch, not a consequence of the
Lagrangian's algebraic decomposition.

This is a useful refinement of the conservation proposal: the conserved object
cannot be the raw N-frame action.  A successful version must construct a
solver/CNF-relative defect above the Pi-star baseline and prove that correctness
would discharge it.  That construction remains the finite diagonal theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit

open SATDepthMachine
open PallLean.Paper93.NFrame
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint

/-! ## The raw concrete action has a positive baseline -/

/-- The repository's concrete N-frame proxy is at least one at every gauge. -/
theorem one_le_nframeLagrangian
    {N : Nat} (family : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) :
    1 <= nframeLagrangian family gauge := by
  rw [nframeLagrangian_eq_proxy]
  exact one_le_proxy_of_nonneg _ (Nat.cast_nonneg _)

/-- Consequently, the raw action never has value zero. -/
theorem nframeLagrangian_ne_zero
    {N : Nat} (family : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) :
    nframeLagrangian family gauge ≠ 0 := by
  have h := one_le_nframeLagrangian family gauge
  linarith

/-- At the canonical rank-zero gauge the raw action is exactly its positive
baseline `1`. -/
theorem nframeLagrangian_trivialGauge_eq_one
    {N : Nat} (family : Nat -> MvPolynomial (Fin N) Rat) :
    nframeLagrangian family (trivialGauge N) = 1 := by
  rw [nframeLagrangian_eq_proxy]
  have htriv :
      (Module.finrank Rat
        (LinearMap.range (trivialGauge N).projection) : Real) = 0 := by
    have hrange : LinearMap.range (trivialGauge N).projection = ⊥ := by
      simp [trivialGauge]
    rw [hrange]
    simp
  simp [htriv]

/-! ## Solver-indexed concrete trajectories -/

/-- A solver-indexed assignment of the actual N-frame functional.  The family
and gauge may depend on the certified solver, but are fixed along its finite
trajectory, matching literal action conservation. -/
structure ConcreteNFrameTrajectory (U : MachineModel) (N : Nat) where
  family : DecisionMachine U -> Nat -> MvPolynomial (Fin N) Rat
  gauge : DecisionMachine U -> CandidateGauge N
  horizon : DecisionMachine U -> Nat

/-- The literal raw action along a concrete trajectory. -/
noncomputable def concreteAction
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (_t : Nat) : Real :=
  nframeLagrangian (A.family M) (A.gauge M)

/-- The literal action is exactly conserved. -/
theorem concreteAction_conserved
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (t : Nat) :
    concreteAction A M (t + 1) = concreteAction A M t := by
  rfl

/-- Every literal concrete trajectory retains action at least one at every
time, including its terminal time. -/
theorem one_le_concreteAction
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (t : Nat) :
    1 <= concreteAction A M t :=
  one_le_nframeLagrangian (A.family M) (A.gauge M)

/-- The tempting literal terminal boundary condition. -/
def LiteralCorrectTerminalZero
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N) : Prop :=
  forall M : DecisionMachine U,
    CorrectOn U M.code (decodeCNFCode M.code) ->
      concreteAction A M (A.horizon M) = 0

/-- Any certified machine correct on its paired decoded formula refutes the
literal terminal-zero condition, because the barrier keeps action at least
one. -/
theorem no_literalCorrectTerminalZero_of_correctPair
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U)
    (hCorrect : CorrectOn U M.code (decodeCNFCode M.code)) :
    ¬ LiteralCorrectTerminalZero A := by
  intro hZero
  have hOne := one_le_concreteAction A M (A.horizon M)
  have h0 := hZero M hCorrect
  linarith

/-- Concrete countermodel: no choice of actual N-frame families and gauges can
make the raw action vanish on correct terminals. -/
theorem pointwiseModel_refutes_literal_concrete_boundary
    {N : Nat} (A : ConcreteNFrameTrajectory pointwiseCNFMachineModel N) :
    ¬ LiteralCorrectTerminalZero A :=
  no_literalCorrectTerminalZero_of_correctPair A
    (pointwiseCodeDecisionMachine 0)
    (pointwiseCodeDecisionMachine_correct_on_decode 0)

/-! ## Baseline subtraction -/

/-- Excess action above the universal Pi-star baseline. -/
noncomputable def excessConcreteAction
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (t : Nat) : Real :=
  concreteAction A M t - 1

/-- Baseline subtraction preserves exact conservation. -/
theorem excessConcreteAction_conserved
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (t : Nat) :
    excessConcreteAction A M (t + 1) = excessConcreteAction A M t := by
  rfl

/-- The excess action is nonnegative. -/
theorem excessConcreteAction_nonneg
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N)
    (M : DecisionMachine U) (t : Nat) :
    0 <= excessConcreteAction A M t := by
  unfold excessConcreteAction
  have h := one_le_concreteAction A M t
  linarith

/-- The canonical trivial/Pi-star trajectory has identically zero excess
action, so normalization removes the positive baseline but creates no SAT
debt. -/
theorem trivialGauge_excessAction_eq_zero
    {U : MachineModel} {N : Nat}
    (family : DecisionMachine U -> Nat -> MvPolynomial (Fin N) Rat)
    (horizon : DecisionMachine U -> Nat)
    (M : DecisionMachine U) (t : Nat) :
    let A : ConcreteNFrameTrajectory U N :=
      { family := family, gauge := fun _ => trivialGauge N,
        horizon := horizon }
    excessConcreteAction A M t = 0 := by
  dsimp [excessConcreteAction, concreteAction]
  rw [nframeLagrangian_trivialGauge_eq_one]
  ring

/-! ## Exact surviving semantic endpoint -/

/-- A normalized boundary mismatch: positive initial excess, but correctness
would force zero terminal excess. -/
structure ExcessSATBoundaryLaw
    {U : MachineModel} {N : Nat} (A : ConcreteNFrameTrajectory U N) : Prop where
  initial_positive : forall M, 0 < excessConcreteAction A M 0
  correct_terminal_zero : forall M,
    CorrectOn U M.code (decodeCNFCode M.code) ->
      excessConcreteAction A M (A.horizon M) = 0

/-- Exact conservation turns any normalized boundary mismatch into decoded
solver anti-correlation. -/
theorem decodedAntiCorrelation_of_excessSATBoundaryLaw
    {U : MachineModel} {N : Nat} {A : ConcreteNFrameTrajectory U N}
    (hLaw : ExcessSATBoundaryLaw A) :
    DecodedSolverAntiCorrelation U := by
  intro M hCorrect
  have hPos := hLaw.initial_positive M
  have hZero := hLaw.correct_terminal_zero M hCorrect
  have hConserved :
      excessConcreteAction A M (A.horizon M) =
        excessConcreteAction A M 0 := by
    rfl
  linarith

/-- Therefore a successful concrete normalized Lagrangian boundary theorem
would prove the SAT lower bound. -/
theorem no_SATDecisionInP_of_excessSATBoundaryLaw
    {U : MachineModel} {N : Nat} {A : ConcreteNFrameTrajectory U N}
    (hLaw : ExcessSATBoundaryLaw A) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_decodedSolverAntiCorrelation
    (decodedAntiCorrelation_of_excessSATBoundaryLaw hLaw)

end PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit.one_le_nframeLagrangian
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit.pointwiseModel_refutes_literal_concrete_boundary
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit.trivialGauge_excessAction_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteLagrangianBoundaryAudit.no_SATDecisionInP_of_excessSATBoundaryLaw
