import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameUnchargedInitializationBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Repairing the clocked model with forced initialization and local transitions

The uncharged-initialization barrier shows that an arbitrary
`init : Input -> Config` trivializes a step-counted machine model.  The
repository already contains the appropriate local alternative:
`ComposableMachine.Machine` has finite control, a forced start state, the
input placed unchanged on a tape, and a transition table that can inspect only
the symbol under the head.

This file proves the basic non-vacuity property missing from the old
`ClockedMachine`.  At zero charged steps the output is independent of the
input, so a zero-clock local machine can decide only a constant language.
More generally, if a machine distinguishes two inputs of the same length,
their shared clock must be positive.  In particular the one-bit head language
cannot be decided at zero cost.

This repairs the specific initialization loophole; it is not a SAT lower
bound.  The remaining hard work is a superpolynomial lower bound in this
finite-control local-transition model, not another abstract trace predicate.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-! ## Zero-step behavior is input-independent -/

/-- Before any local transition, the decision reads only the fixed start
state, not the input tape. -/
theorem decideOut_zero (M : Machine) (x : List Bool) :
    decideOut M x 0 = M.accept M.start := by
  rfl

/-- Any language decided with an identically zero clock is constant. -/
theorem zeroClock_decides_constant
    (M : Machine) (L : List Bool -> Bool)
    (hdec : Decides M L (fun _ => 0)) :
    ∀ x y, L x = L y := by
  intro x y
  have hx := (hdec x).2
  have hy := (hdec y).2
  calc
    L x = decideOut M x 0 := hx.symm
    _ = M.accept M.start := decideOut_zero M x
    _ = decideOut M y 0 := (decideOut_zero M y).symm
    _ = L y := hy

/-! ## Distinguishing equal-length inputs costs a transition -/

/-- If a local machine distinguishes two inputs governed by the same
length-based clock, that clock cannot be zero. -/
theorem sameLength_distinction_requires_positive_clock
    (M : Machine) (L : List Bool -> Bool) (T : Nat -> Nat)
    (hdec : Decides M L T)
    {x y : List Bool} (hlen : x.length = y.length)
    (hdiff : L x ≠ L y) :
    0 < T x.length := by
  by_contra hnot
  have hzeroX : T x.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hzeroY : T y.length = 0 := by
    rw [← hlen]
    exact hzeroX
  have hx := (hdec x).2
  have hy := (hdec y).2
  apply hdiff
  calc
    L x = decideOut M x (T x.length) := hx.symm
    _ = decideOut M x 0 := by rw [hzeroX]
    _ = M.accept M.start := decideOut_zero M x
    _ = decideOut M y 0 := (decideOut_zero M y).symm
    _ = decideOut M y (T y.length) := by rw [hzeroY]
    _ = L y := hy

/-! ## A concrete nonconstant language -/

/-- Return the first input bit, or `false` on the empty input. -/
def firstBitLanguage : List Bool -> Bool
  | [] => false
  | b :: _ => b

/-- No local finite-control machine decides the first-bit language with zero
charged transitions. -/
theorem no_zeroClock_firstBit_decider :
    ¬ ∃ M : Machine, Decides M firstBitLanguage (fun _ => 0) := by
  rintro ⟨M, hdec⟩
  have hconstant := zeroClock_decides_constant M firstBitLanguage hdec
  have hbad := hconstant [false] [true]
  simp [firstBitLanguage] at hbad

/-- Every local machine deciding the first-bit language needs a positive
clock already at input length one. -/
theorem firstBit_decider_requires_positive_clock
    (M : Machine) (T : Nat -> Nat)
    (hdec : Decides M firstBitLanguage T) :
    0 < T 1 := by
  have h := sameLength_distinction_requires_positive_clock
    M firstBitLanguage T hdec
    (x := [false]) (y := [true]) (by simp) (by simp [firstBitLanguage])
  simpa using h

/-- Hence the zero-step universal-language construction from the uncharged
model has no analogue in the repaired local model. -/
theorem no_universal_zeroClock_local_deciders :
    ¬ ∀ L : List Bool -> Bool,
      ∃ M : Machine, Decides M L (fun _ => 0) := by
  intro hall
  exact no_zeroClock_firstBit_decider (hall firstBitLanguage)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.decideOut_zero
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.zeroClock_decides_constant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.sameLength_distinction_requires_positive_clock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.no_zeroClock_firstBit_decider
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.firstBit_decider_requires_positive_clock
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair.no_universal_zeroClock_local_deciders
