import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameDynamicMERAHolonomy

/-!
# Run-indexed, causally faithful `TΦ`

This file rebuilds the paper's proposed extraction at the level that follows from an
actual deterministic run.  The extractor at time `t` is not an independently appended
clause sheet: it is the Boolean decision obtained by running the *actual state at time
`t`* through the remaining suffix of the same computation.

This gives a genuine no-dead-padding theorem: two inputs with different final decisions
cannot be merged by the extracted causal quotient at any intermediate time.  It also
exposes the exact limitation.  The quotient has only one Boolean coordinate, so causal
faithfulness to a decision bit alone cannot yield an exponential identity minor.  An
ignored auxiliary label is formally invisible to the extractor.

Thus a superpolynomial SPDP/holonomy lower bound still needs a new theorem showing that
the SAT decision itself forces a richer *operational* quotient than the canonical
one-bit causal quotient constructed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi

open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy

variable {Input State Base Label : Type*}

/-- A deterministic decision computation, with its real input encoding, transition
trajectory, clock, and final Boolean observation. -/
structure ActualDecisionRun (Input State : Type*) where
  encode : Input → State
  step : Nat → State → State
  steps : Nat
  observe : State → Bool

namespace ActualDecisionRun

/-- The actual state reached after `time` transitions. -/
def stateAt (R : ActualDecisionRun Input State) (time : Nat) (x : Input) : State :=
  runFrom R.step 0 time (R.encode x)

/-- The decision produced by the complete run. -/
def finalAnswer (R : ActualDecisionRun Input State) (x : Input) : Bool :=
  R.observe (R.stateAt R.steps x)

/-- **Run-indexed `TΦ`.**  Continue the actual state at time `time` through the
remaining suffix and observe the decision.  No independent sheet or auxiliary payload
is inserted. -/
def causalTPhi (R : ActualDecisionRun Input State) (time : Nat) (x : Input) : Bool :=
  R.observe (runFrom R.step time (R.steps - time) (R.stateAt time x))

/-- The run-indexed extraction is exactly the real final decision. -/
theorem causalTPhi_eq_finalAnswer (R : ActualDecisionRun Input State)
    (time : Nat) (htime : time ≤ R.steps) (x : Input) :
    R.causalTPhi time x = R.finalAnswer x := by
  have hs : R.steps = time + (R.steps - time) := by omega
  rw [finalAnswer, stateAt, hs, runFrom_add]
  simp [causalTPhi, stateAt]

/-- **Causal no-merging.**  If two inputs have different decisions, their run-indexed
causal extractions differ at every time before the output. -/
theorem causalTPhi_ne_of_finalAnswer_ne (R : ActualDecisionRun Input State)
    (time : Nat) (htime : time ≤ R.steps) {x y : Input}
    (hxy : R.finalAnswer x ≠ R.finalAnswer y) :
    R.causalTPhi time x ≠ R.causalTPhi time y := by
  simpa [R.causalTPhi_eq_finalAnswer time htime] using hxy

/-- Equality of the causal extractions is exactly equality of the decisions. -/
theorem causalTPhi_eq_iff (R : ActualDecisionRun Input State)
    (time : Nat) (htime : time ≤ R.steps) (x y : Input) :
    R.causalTPhi time x = R.causalTPhi time y ↔
      R.finalAnswer x = R.finalAnswer y := by
  simp only [R.causalTPhi_eq_finalAnswer time htime]

/-- The exact audit boundary: on `n ≥ 2` input bits, a causally faithful Boolean
decision quotient cannot be injective.  Hence actual-run causality by itself cannot
manufacture the `2^n` independent lanes required by the proposed identity minor. -/
theorem causalTPhi_not_injective_on_bitstrings
    (R : ActualDecisionRun (Fin n → Bool) State)
    (time : Nat) (_htime : time ≤ R.steps) (hn : 2 ≤ n) :
    ¬ Function.Injective (R.causalTPhi time) := by
  intro hinj
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective (R.causalTPhi time) hinj
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  have hfour : 4 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
  omega

end ActualDecisionRun

/-! ## Formal no-dead-sheet audit -/

/-- Lift a real run with an auxiliary label that does not affect its dynamics or output.
This is precisely the independently appended-sheet construction criticized in the paper
audit. -/
def labelIgnoredRun (R : ActualDecisionRun Base State) (Label : Type*) :
    ActualDecisionRun (Base × Label) State where
  encode := fun x => R.encode x.1
  step := R.step
  steps := R.steps
  observe := R.observe

/-- Appended labels are invisible to the complete decision. -/
theorem labelIgnoredRun_finalAnswer
    (R : ActualDecisionRun Base State) (Label : Type*) (x : Base) (a : Label) :
    (labelIgnoredRun R Label).finalAnswer (x, a) = R.finalAnswer x := by
  rfl

/-- Appended labels are invisible at every run-indexed causal extraction time.  Thus a
`TΦ` that extracts such labels is extracting syntactic padding, not information forced
by the solver's output trajectory. -/
theorem labelIgnoredRun_causalTPhi
    (R : ActualDecisionRun Base State) (Label : Type*)
    (time : Nat) (x : Base) (a b : Label) :
    (labelIgnoredRun R Label).causalTPhi time (x, a) =
      (labelIgnoredRun R Label).causalTPhi time (x, b) := by
  rfl

/-- If the attached label has two distinct values, the run-indexed extraction cannot
recover it injectively. -/
theorem labelIgnoredRun_causalTPhi_not_injective
    (R : ActualDecisionRun Base State) {Label : Type*}
    (time : Nat) (x : Base) {a b : Label} (hab : a ≠ b) :
    ¬ Function.Injective ((labelIgnoredRun R Label).causalTPhi time) := by
  intro hinj
  have hp : (x, a) = (x, b) :=
    hinj (labelIgnoredRun_causalTPhi R Label time x a b)
  exact hab (congrArg Prod.snd hp)

/-!
## Honest endpoint

The causal extraction requested by the paper can be built from the actual run, and its
no-merging theorem is unconditional.  But its solver-forced content is exactly the one
decision bit.  The appended-sheet route fails formally because ignored labels disappear
from this quotient.

The remaining new mathematics must prove that, for a concrete single NP-complete SAT
family, a polynomial-time solver's *operational* causal quotient has a mandatory
superpolynomial SPDP/holonomy rank.  That statement does not follow from Boolean SAT
correctness alone.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun.causalTPhi_eq_finalAnswer
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun.causalTPhi_ne_of_finalAnswer_ne
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi.ActualDecisionRun.causalTPhi_not_injective_on_bitstrings
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi.labelIgnoredRun_causalTPhi_not_injective
