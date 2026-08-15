import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Exact time-unrolled local-factor representation of finite computations

Every deterministic finite trajectory has a canonical path-shaped tensor/factor
network: one state variable per time slice, one initial factor, and one local
transition factor between consecutive slices.  The construction is universal
and exact, but its depth is the runtime `T`; it does not provide logarithmic-depth
MERA compression or a complexity lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork

/-- The deterministic state at time `t`. -/
def run {State : Type*} (step : State → State) (start : State) (t : Nat) : State :=
  (step^[t]) start

/-- A Boolean local tensor/factor enforcing one transition edge. -/
def transitionFactor {State : Type*} [DecidableEq State]
    (step : State → State) (before after : State) : Bool :=
  decide (after = step before)

/-- A path-shaped, time-unrolled local-factor network for `T` transitions.
It has `T+1` state slices and only nearest-time-neighbour constraints. -/
structure Network (State : Type*) (step : State → State) (start : State) (T : Nat) where
  stateAt : Fin (T + 1) → State
  initial_exact : stateAt ⟨0, Nat.zero_lt_succ T⟩ = start
  transition_exact : ∀ t : Fin T,
    stateAt (Fin.succ t) = step (stateAt (Fin.castSucc t))

/-- The canonical time-unrolling of any deterministic computation. -/
def canonical {State : Type*} (step : State → State) (start : State) (T : Nat) :
    Network State step start T where
  stateAt t := run step start t.val
  initial_exact := by simp [run]
  transition_exact := by
    intro t
    simp only [run, Fin.succ, Fin.castSucc]
    exact Function.iterate_succ_apply' step t.val start

/-- The final open leg of the canonical network is exactly the `T`-step state. -/
theorem canonical_terminal {State : Type*} (step : State → State) (start : State) (T : Nat) :
    (canonical step start T).stateAt (Fin.last T) = run step start T := by
  rfl

/-- Every local transition factor of the canonical network evaluates to true. -/
theorem canonical_transitionFactor_true {State : Type*} [DecidableEq State]
    (step : State → State) (start : State) (T : Nat) (t : Fin T) :
    transitionFactor step
      ((canonical step start T).stateAt (Fin.castSucc t))
      ((canonical step start T).stateAt (Fin.succ t)) = true := by
  simp [transitionFactor, (canonical step start T).transition_exact t]

/-- The representation uses exactly one state slice per clock value. -/
def sliceCount (T : Nat) : Nat := T + 1

theorem canonical_sliceCount (T : Nat) : sliceCount T = T + 1 := rfl

/-- The path network depth is the original runtime.  This equality records the
precise limitation of time unrolling: universality supplies no depth collapse. -/
def networkDepth (T : Nat) : Nat := T

theorem canonical_depth_eq_runtime (T : Nat) : networkDepth T = T := rfl

/-! ## Concrete machine-run instantiation -/

/-- Compile a clocked run of the repository's composition-friendly machine
model into its exact time-unrolled local-factor network. -/
def ofComposableMachine
    (M : ComposableMachine.Machine) (x : List Bool) (T : Nat) :
    Network (ComposableMachine.Cfg M) (ComposableMachine.step M)
      (ComposableMachine.init M x) T :=
  canonical (ComposableMachine.step M) (ComposableMachine.init M x) T

/-- The final open leg of the compiled network is the machine's actual
configuration after `T` steps. -/
theorem ofComposableMachine_terminal
    (M : ComposableMachine.Machine) (x : List Bool) (T : Nat) :
    (ofComposableMachine M x T).stateAt (Fin.last T) =
      ComposableMachine.run M T (ComposableMachine.init M x) := by
  rfl

/-- Reading the accepting control bit at the final open leg gives exactly the
machine model's clocked decision output. -/
theorem ofComposableMachine_decision_exact
    (M : ComposableMachine.Machine) (x : List Bool) (T : Nat) :
    M.accept ((ofComposableMachine M x T).stateAt (Fin.last T)).st =
      ComposableMachine.decideOut M x T := by
  rfl

end PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork

#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_transitionFactor_true
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_depth_eq_runtime
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.ofComposableMachine_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.ofComposableMachine_decision_exact
