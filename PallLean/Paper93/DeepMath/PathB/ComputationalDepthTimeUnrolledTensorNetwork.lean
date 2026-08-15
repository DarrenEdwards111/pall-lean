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

/-! ## Balanced transition-monoid compression -/

/-- A binary contraction tree whose leaves are transition summaries.  At a
node, the left time segment runs first and the right segment runs second. -/
inductive CompositionTree (State : Type*) where
  | leaf (transition : State → State)
  | node (left right : CompositionTree State)

namespace CompositionTree

/-- Exact endomorphism represented by a composition tree. -/
def eval {State : Type*} : CompositionTree State → (State → State)
  | .leaf transition => transition
  | .node left right => eval right ∘ eval left

/-- Parallel contraction depth. -/
def height {State : Type*} : CompositionTree State → Nat
  | .leaf _ => 0
  | .node left right => max (height left) (height right) + 1

/-- Number of sequential transition leaves represented by the tree. -/
def leafCount {State : Type*} : CompositionTree State → Nat
  | .leaf _ => 1
  | .node left right => leafCount left + leafCount right

/-- The perfectly balanced summary tree for `2^d` repetitions of one local
transition. -/
def balancedPower {State : Type*} (step : State → State) : Nat → CompositionTree State
  | 0 => .leaf step
  | d + 1 =>
      let half := balancedPower step d
      .node half half

theorem balancedPower_height {State : Type*} (step : State → State) (d : Nat) :
    (balancedPower step d).height = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [balancedPower, height, ih]

theorem balancedPower_leafCount {State : Type*} (step : State → State) (d : Nat) :
    (balancedPower step d).leafCount = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [balancedPower, leafCount, ih, pow_succ]
      omega

/-- Balanced contraction is semantically exact: depth `d` represents precisely
`2^d` sequential transition steps. -/
theorem balancedPower_eval {State : Type*} (step : State → State) (d : Nat) :
    (balancedPower step d).eval = step^[2 ^ d] := by
  induction d with
  | zero => rfl
  | succ d ih =>
      funext x
      simp only [balancedPower, eval, Function.comp_apply, ih, pow_succ]
      rw [show 2 ^ d * 2 = 2 ^ d + 2 ^ d by omega]
      exact (Function.iterate_add_apply step (2 ^ d) (2 ^ d) x).symm

/-- Exact terminal-state form of balanced transition composition. -/
theorem balancedPower_terminal {State : Type*}
    (step : State → State) (start : State) (d : Nat) :
    (balancedPower step d).eval start = run step start (2 ^ d) := by
  rw [balancedPower_eval]
  rfl

end CompositionTree

/-- For a finite configuration carrier, every internal wire of the balanced
composition tree ranges over exactly the finite state space. -/
def bondDimension (State : Type*) [Fintype State] : Nat := Fintype.card State

theorem bondDimension_eq_card (State : Type*) [Fintype State] :
    bondDimension State = Fintype.card State := rfl

/-- Concrete machine instantiation: a power-of-two clocked run has an exact
balanced transition tree of logarithmic depth `d`. -/
theorem composableMachine_balanced_terminal
    (M : ComposableMachine.Machine) (x : List Bool) (d : Nat) :
    (CompositionTree.balancedPower (ComposableMachine.step M) d).eval
        (ComposableMachine.init M x) =
      ComposableMachine.run M (2 ^ d) (ComposableMachine.init M x) := by
  exact CompositionTree.balancedPower_terminal
    (ComposableMachine.step M) (ComposableMachine.init M x) d

end PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork

#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_transitionFactor_true
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.canonical_depth_eq_runtime
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.ofComposableMachine_terminal
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.ofComposableMachine_decision_exact
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.CompositionTree.balancedPower_height
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.CompositionTree.balancedPower_leafCount
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.CompositionTree.balancedPower_eval
#print axioms PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork.composableMachine_balanced_terminal
