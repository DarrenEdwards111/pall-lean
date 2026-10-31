import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTowerFixedProgramFactorizationEndpoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt
import PallLean.Paper93.NFrame.LagrangianFunctional

/-!
# N-Frame Lagrangian conservation endpoint

The N-frame Lagrangian is a natural candidate for the conservation law behind
the remaining solver-code anti-correlation theorem.  This file tests that
proposal without weakening it to a compiler or coverage property.

There are two distinct statements:

* a Lagrangian charge is conserved along a finite solver trajectory;
* the conserved charge has SAT-specific boundary conditions: it starts with a
  positive unresolved debt, while correctness would force zero terminal debt.

The first statement is harmless and unconditionally inhabited (even the
concrete static N-frame functional gives a constant conserved trajectory).
The second statement, combined with conservation, rules out correctness on the
decoded formula.  Uniformly over certified solver codes it is exactly the
missing decoded anti-correlation law, hence yields the effective finite
diagonalizer and `SAT ∉ P`.

The observer-time form reaches the same endpoint.  The already-proved theorem
`bounded_action_fails` transports initial debt through the integrated
Lagrangian action.  To obtain a solver error one still needs the SAT-specific
gap saying that the available action is smaller than the initial debt and that
correctness clears the terminal debt.  Existence of that gap package is again
equivalent to decoded anti-correlation.

Thus the conservation-law idea is structurally sound: the N-frame Lagrangian
is the right carrier.  The remaining hard theorem is not conservation itself,
but deriving its SAT boundary mismatch from each finite solver/formula pair.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint

open SATDepthMachine
open PallLean.Paper93.NFrame
open PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverDiagonalizationFrontier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerProgramSliceCoverageBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerSolverResponsiveCoverageBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameTowerFixedProgramFactorizationEndpoint

/-! ## Exact conservation alone -/

/-- A finite solver-indexed N-frame charge with exact time conservation. -/
structure ConservedNFrameLagrangian (U : MachineModel) where
  charge : DecisionMachine U -> Nat -> Nat
  horizon : DecisionMachine U -> Nat
  conserved : forall M t, charge M (t + 1) = charge M t

/-- Exact conservation transports the initial charge to every time. -/
theorem conserved_charge_eq_initial
    {U : MachineModel} (C : ConservedNFrameLagrangian U)
    (M : DecisionMachine U) (T : Nat) :
    C.charge M T = C.charge M 0 := by
  induction T with
  | zero => rfl
  | succ t ih =>
      rw [C.conserved M t, ih]

/-- In particular, the initial and terminal Lagrangian charges agree. -/
theorem conserved_initial_eq_terminal
    {U : MachineModel} (C : ConservedNFrameLagrangian U)
    (M : DecisionMachine U) :
    C.charge M 0 = C.charge M (C.horizon M) := by
  symm
  exact conserved_charge_eq_initial C M (C.horizon M)

/-- Conservation by itself is unconditionally inhabited by the zero charge. -/
def zeroConservedNFrameLagrangian (U : MachineModel) :
    ConservedNFrameLagrangian U where
  charge := fun _ _ => 0
  horizon := fun _ => 0
  conserved := by intros; rfl

/-- Regard the concrete N-frame functional at a fixed gauge as a trajectory. -/
noncomputable def staticNFrameAction
    {N : Nat} (family : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) (_t : Nat) : Real :=
  nframeLagrangian family gauge

/-- The concrete static N-frame action is exactly conserved.  This witnesses
directly that mere time invariance supplies no SAT semantics. -/
theorem static_nframeLagrangian_is_conserved
    {N : Nat} (family : Nat -> MvPolynomial (Fin N) Rat)
    (gauge : CandidateGauge N) (t : Nat) :
    staticNFrameAction family gauge (t + 1) =
      staticNFrameAction family gauge t := by
  rfl

/-! ## The load-bearing SAT boundary law -/

/-- SAT-specific boundary conditions for a conserved Lagrangian: every paired
solver starts with positive unresolved charge, while correctness on its decoded
formula would clear that charge at the terminal time. -/
structure LagrangianSATBoundaryLaw
    (U : MachineModel) (C : ConservedNFrameLagrangian U) : Prop where
  initial_positive : forall M, 0 < C.charge M 0
  correct_terminal_zero : forall M,
    CorrectOn U M.code (decodeCNFCode M.code) ->
      C.charge M (C.horizon M) = 0

/-- Conservation plus the SAT boundary mismatch forces decoded
anti-correlation. -/
theorem decodedAntiCorrelation_of_conservedBoundaryLaw
    {U : MachineModel} {C : ConservedNFrameLagrangian U}
    (hLaw : LagrangianSATBoundaryLaw U C) :
    DecodedSolverAntiCorrelation U := by
  intro M hCorrect
  have hEq := conserved_initial_eq_terminal C M
  have hPos := hLaw.initial_positive M
  have hZero := hLaw.correct_terminal_zero M hCorrect
  omega

/-- A unit conserved charge.  Under anti-correlation its terminal-zero
condition is vacuous, exposing the exact logical calibration. -/
def unitConservedNFrameLagrangian (U : MachineModel) :
    ConservedNFrameLagrangian U where
  charge := fun _ _ => 1
  horizon := fun _ => 0
  conserved := by intros; rfl

theorem conservedBoundaryLaw_of_decodedAntiCorrelation
    {U : MachineModel} (hAnti : DecodedSolverAntiCorrelation U) :
    LagrangianSATBoundaryLaw U (unitConservedNFrameLagrangian U) where
  initial_positive := by
    intro M
    change 0 < 1
    omega
  correct_terminal_zero := by
    intro M hCorrect
    exact (hAnti M hCorrect).elim

/-- Exact endpoint: some conserved N-frame charge with the required SAT
boundary mismatch exists iff the decoded finite diagonal law already holds. -/
theorem conservedLagrangianBoundaryLaw_iff_decodedAntiCorrelation
    (U : MachineModel) :
    (exists C : ConservedNFrameLagrangian U,
      LagrangianSATBoundaryLaw U C) <->
      DecodedSolverAntiCorrelation U := by
  constructor
  · rintro ⟨C, hLaw⟩
    exact decodedAntiCorrelation_of_conservedBoundaryLaw hLaw
  · intro hAnti
    exact ⟨unitConservedNFrameLagrangian U,
      conservedBoundaryLaw_of_decodedAntiCorrelation hAnti⟩

/-! ## Observer-time action form -/

/-- Solver-indexed debt and servicing rate to which the proved observer-time
Lagrangian conservation theorem applies. -/
structure ObserverTimeLagrangianFamily (U : MachineModel) where
  debt : DecisionMachine U -> Nat -> Nat
  rate : DecisionMachine U -> Nat -> Nat
  horizon : DecisionMachine U -> Nat
  service : forall M t, debt M t <= debt M (t + 1) + rate M t

/-- The SAT-specific gap needed in addition to observer-time conservation. -/
structure ObserverTimeSATGap
    (U : MachineModel) (C : ObserverTimeLagrangianFamily U) : Prop where
  action_lt_initial : forall M,
    observerTimeAction (C.rate M) (C.horizon M) < C.debt M 0
  correct_clears : forall M,
    CorrectOn U M.code (decodeCNFCode M.code) ->
      C.debt M (C.horizon M) = 0

/-- The existing integrated-action conservation theorem turns the SAT gap into
the decoded solver error. -/
theorem decodedAntiCorrelation_of_observerTimeSATGap
    {U : MachineModel} {C : ObserverTimeLagrangianFamily U}
    (hGap : ObserverTimeSATGap U C) :
    DecodedSolverAntiCorrelation U := by
  intro M hCorrect
  have hNotCleared := bounded_action_fails
    (C.debt M) (C.rate M) (C.service M) (C.horizon M)
    (hGap.action_lt_initial M)
  exact hNotCleared (hGap.correct_clears M hCorrect)

/-- A one-unit initial debt with zero time horizon.  It satisfies the
conservation inequality independently of SAT. -/
def unitObserverTimeLagrangianFamily (U : MachineModel) :
    ObserverTimeLagrangianFamily U where
  debt := fun _ _ => 1
  rate := fun _ _ => 0
  horizon := fun _ => 0
  service := by intros; simp

theorem observerTimeSATGap_of_decodedAntiCorrelation
    {U : MachineModel} (hAnti : DecodedSolverAntiCorrelation U) :
    ObserverTimeSATGap U (unitObserverTimeLagrangianFamily U) where
  action_lt_initial := by
    intro M
    simp [observerTimeAction, unitObserverTimeLagrangianFamily]
  correct_clears := by
    intro M hCorrect
    exact (hAnti M hCorrect).elim

/-- The integrated observer-time version has exactly the same endpoint. -/
theorem observerTimeLagrangianGap_iff_decodedAntiCorrelation
    (U : MachineModel) :
    (exists C : ObserverTimeLagrangianFamily U, ObserverTimeSATGap U C) <->
      DecodedSolverAntiCorrelation U := by
  constructor
  · rintro ⟨C, hGap⟩
    exact decodedAntiCorrelation_of_observerTimeSATGap hGap
  · intro hAnti
    exact ⟨unitObserverTimeLagrangianFamily U,
      observerTimeSATGap_of_decodedAntiCorrelation hAnti⟩

/-! ## Concrete countermodel and separation consequence -/

/-- Conservation exists in the pointwise countermodel while the SAT boundary
law does not.  Thus no theorem from conservation alone can supply the missing
anti-correlation. -/
theorem conservation_without_SAT_boundary_law :
    Nonempty (ConservedNFrameLagrangian pointwiseCNFMachineModel) /\
    ¬ (exists C : ConservedNFrameLagrangian pointwiseCNFMachineModel,
      LagrangianSATBoundaryLaw pointwiseCNFMachineModel C) := by
  refine ⟨⟨zeroConservedNFrameLagrangian pointwiseCNFMachineModel⟩, ?_⟩
  intro h
  have hAnti :=
    (conservedLagrangianBoundaryLaw_iff_decodedAntiCorrelation
      pointwiseCNFMachineModel).1 h
  exact operational_complete_but_semantic_field_false.2.2 hAnti

/-- A genuine conserved SAT boundary law would prove the SAT lower bound. -/
theorem no_SATDecisionInP_of_conservedLagrangianBoundaryLaw
    {U : MachineModel} {C : ConservedNFrameLagrangian U}
    (hLaw : LagrangianSATBoundaryLaw U C) :
    ¬ SATDecisionInP U :=
  no_SATDecisionInP_of_decodedSolverAntiCorrelation
    (decodedAntiCorrelation_of_conservedBoundaryLaw hLaw)

end PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint.conserved_initial_eq_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint.conservedLagrangianBoundaryLaw_iff_decodedAntiCorrelation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint.observerTimeLagrangianGap_iff_decodedAntiCorrelation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLagrangianConservationEndpoint.conservation_without_SAT_boundary_law
