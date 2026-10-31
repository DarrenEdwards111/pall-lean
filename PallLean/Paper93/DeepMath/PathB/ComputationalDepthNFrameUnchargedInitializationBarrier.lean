import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameExecutionTraceProvenanceCalibration
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# Uncharged initialization trivializes the clocked machine model

The repository already contains a deterministic transition-level model:
`PvsNPSeparatingInvariant.ClockedMachine`.  Its configuration may contain the
whole input, its transition function is iterated for a charged clock, and its
final configuration is observed for the answer.

However, `init : List Bool -> Config` is an arbitrary Lean function and its
evaluation is not charged to `runtime`.  Therefore initialization may compute
the entire target language before the clock starts.  Taking `Config = Bool`,
`init = L`, identity transition, identity output, and zero runtime decides any
language `L` in the model's polynomial-time class.

This file proves that collapse explicitly.  In particular, the model's
internal `PeqNP` statement is inhabited, and no resource can satisfy both its
`PUpper` and `SATLower` obligations for any language.  A faithful
transition-level endpoint must charge input decoding/initialization or replace
the arbitrary initializer with a concrete local loading procedure.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant

/-! ## A zero-step decider for every language -/

/-- Store the already-computed language answer in the initial configuration;
the charged transition phase does no work. -/
def zeroStepDecisionMachine (L : List Bool -> Bool) : ClockedMachine where
  Config := Bool
  init := L
  next := id
  output := id
  runtime := fun _ => 0

/-- The machine's clock is identically zero. -/
theorem zeroStepDecisionMachine_runtime
    (L : List Bool -> Bool) (x : List Bool) :
    (zeroStepDecisionMachine L).runtime x = 0 := rfl

/-- The uncharged initializer has already computed the complete answer. -/
theorem zeroStepDecisionMachine_decide
    (L : List Bool -> Bool) (x : List Bool) :
    (zeroStepDecisionMachine L).decide x = L x := by
  rfl

/-- Zero runtime is polynomially bounded. -/
theorem zeroStepDecisionMachine_polyTime (L : List Bool -> Bool) :
    IsPolyTime (zeroStepDecisionMachine L) := by
  refine ⟨0, 0, ?_⟩
  intro x
  simp [zeroStepDecisionMachine]

/-- The zero-step machine decides its arbitrary target language. -/
theorem zeroStepDecisionMachine_decides (L : List Bool -> Bool) :
    Decides (zeroStepDecisionMachine L) L := by
  intro x
  exact zeroStepDecisionMachine_decide L x

/-! ## Collapse of the advertised complexity classes -/

/-- Every Boolean language belongs to the model's `InP`, including
noncomputable functions represented in Lean. -/
theorem every_language_inP (L : List Bool -> Bool) : InP L :=
  ⟨zeroStepDecisionMachine L,
    zeroStepDecisionMachine_polyTime L,
    zeroStepDecisionMachine_decides L⟩

/-- Consequently the model's internal `P = NP` proposition is provable. -/
theorem clockedModel_PeqNP : PeqNP := by
  intro L _hNP
  exact every_language_inP L

/-- Therefore the model cannot establish its own `P ≠ NP` statement. -/
theorem clockedModel_not_PneqNP : ¬ ¬ PeqNP := by
  intro hne
  exact hne clockedModel_PeqNP

/-! ## The separating-invariant socket is uninhabitable -/

/-- For every resource and every language, `PUpper` and `SATLower` cannot both
hold: the zero-step machine is simultaneously a polynomial-time machine and a
decider for the language. -/
theorem no_PUpper_and_SATLower
    (R : ClockedMachine -> Nat -> Nat)
    (L : List Bool -> Bool) :
    ¬ (PUpper R ∧ SATLower R L) := by
  rintro ⟨hupper, hlower⟩
  exact (no_InP_of_invariant R L hupper hlower) (every_language_inP L)

/-- The obstruction can also be seen directly on the zero-step witness: the
upper obligation makes its resource polynomial, while the lower obligation
forbids exactly that. -/
theorem zeroStepMachine_resource_contradiction
    (R : ClockedMachine -> Nat -> Nat)
    (L : List Bool -> Bool)
    (hupper : PUpper R)
    (hlower : SATLower R L) : False := by
  exact hlower (zeroStepDecisionMachine L)
    (zeroStepDecisionMachine_decides L)
    (hupper (zeroStepDecisionMachine L)
      (zeroStepDecisionMachine_polyTime L))

end PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.zeroStepDecisionMachine_decide
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.zeroStepDecisionMachine_polyTime
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.every_language_inP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.clockedModel_PeqNP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.clockedModel_not_PneqNP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.no_PUpper_and_SATLower
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameUnchargedInitializationBarrier.zeroStepMachine_resource_contradiction
