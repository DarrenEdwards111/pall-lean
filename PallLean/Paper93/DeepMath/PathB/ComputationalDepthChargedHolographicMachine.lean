import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# A charged finite-description machine for holographic dynamic SPDP

`ComputationalDepthHolographicDynamicSPDPInitNoGo` proves that the earlier `ClockedMachine` collapses: its
arbitrary, uncharged `init` can decide any language.  This file repairs that modelling layer with a concrete
deterministic single-tape machine:

* finitely many states `Fin Q` and a finite transition table `δ`;
* a fixed start state;
* initial configuration exactly `(start, head 0, tape = input)`;
* one local transition per charged step;
* a clock depending only on input length.

There is no field in which an arbitrary language can be evaluated for free.  On top of this machine the file
rebuilds causal fixed-observer projection and proves projected innovation is bounded by the charged clock.

This is infrastructure, not a separation.  The remaining work is to define an intrinsic/minimal observer over
reachable configurations, establish simulation invariance, and prove the SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead writeAt)

/-- A deterministic finite-state binary-tape machine with a length clock. -/
structure ChargedMachine where
  Q : Nat
  start : Fin Q
  delta : Fin Q → Bool → Fin Q × Bool × Move
  accept : Fin Q → Bool
  clock : Nat → Nat

/-- Concrete configurations: finite control, head position, and binary tape. -/
structure Config (M : ChargedMachine) where
  state : Fin M.Q
  head : Nat
  tape : List Bool

/-- The only initialiser: copy the input literally, use the fixed start state and head position zero. -/
def init (M : ChargedMachine) (x : List Bool) : Config M :=
  ⟨M.start, 0, x⟩

/-- One charged local transition. -/
def step (M : ChargedMachine) (c : Config M) : Config M :=
  let tr := M.delta c.state (c.tape.getD c.head false)
  ⟨tr.1, moveHead c.head tr.2.2, writeAt c.tape c.head tr.2.1⟩

/-- Run exactly `t` charged transitions. -/
def run (M : ChargedMachine) (t : Nat) (c : Config M) : Config M :=
  (step M)^[t] c

/-- Decision after the machine's length-dependent charged clock. -/
def decide (M : ChargedMachine) (x : List Bool) : Bool :=
  M.accept (run M (M.clock x.length) (init M x)).state

def Decides (M : ChargedMachine) (L : List Bool → Bool) : Prop :=
  ∀ x, decide M x = L x

def IsPolyTime (M : ChargedMachine) : Prop :=
  PolyBounded M.clock

def InP (L : List Bool → Bool) : Prop :=
  ∃ M : ChargedMachine, IsPolyTime M ∧ Decides M L

@[simp] theorem init_state (M : ChargedMachine) (x : List Bool) : (init M x).state = M.start := rfl
@[simp] theorem init_head (M : ChargedMachine) (x : List Bool) : (init M x).head = 0 := rfl
@[simp] theorem init_tape (M : ChargedMachine) (x : List Bool) : (init M x).tape = x := rfl

/-- A finite causal observer of the real charged machine configuration. -/
structure CausalObserver (M : ChargedMachine) where
  Observer : Type
  observerFintype : Fintype Observer
  observerDecEq : DecidableEq Observer
  observe : Config M → Observer
  observedNext : Observer → Observer
  observedOutput : Observer → Bool
  step_commutes : ∀ c, observe (step M c) = observedNext (observe c)
  output_factors : ∀ c, observedOutput (observe c) = M.accept c.state

attribute [instance] CausalObserver.observerFintype CausalObserver.observerDecEq

theorem observe_run {M : ChargedMachine} (O : CausalObserver M) (c : Config M) (t : Nat) :
    O.observe (run M t c) = O.observedNext^[t] (O.observe c) := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      calc
        O.observe (run M (t + 1) c) = O.observe (step M (run M t c)) := by
          simp [run, Function.iterate_succ_apply']
        _ = O.observedNext (O.observe (run M t c)) := O.step_commutes _
        _ = O.observedNext (O.observedNext^[t] (O.observe c)) := congrArg O.observedNext ih
        _ = O.observedNext^[t + 1] (O.observe c) := by
          rw [Function.iterate_succ_apply']

theorem projected_output_correct {M : ChargedMachine} (O : CausalObserver M) (x : List Bool) :
    O.observedOutput (O.observedNext^[M.clock x.length] (O.observe (init M x))) = decide M x := by
  rw [← observe_run O]
  exact O.output_factors _

/-- Cumulative observed boundary changes along the genuinely charged trace. -/
def projectedInnovation {M : ChargedMachine} (O : CausalObserver M) (x : List Bool) : Nat :=
  ((Finset.range (M.clock x.length)).filter (fun t =>
    O.observe (run M (t + 1) (init M x)) ≠ O.observe (run M t (init M x)))).card

theorem projectedInnovation_le_clock {M : ChargedMachine} (O : CausalObserver M) (x : List Bool) :
    projectedInnovation O x ≤ M.clock x.length := by
  unfold projectedInnovation
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Worst-case projected innovation at input length `n`. -/
def RprojectedFor {M : ChargedMachine} (O : CausalObserver M) (n : Nat) : Nat :=
  (Finset.univ : Finset (Fin n → Bool)).sup
    (fun a => projectedInnovation O (List.ofFn a))

/-- The repaired all-P upper theorem, for any supplied causal observer of a charged machine. -/
theorem RprojectedFor_polyBounded {M : ChargedMachine} (O : CausalObserver M)
    (hM : IsPolyTime M) : PolyBounded (RprojectedFor O) := by
  obtain ⟨c, k, hclock⟩ := hM
  refine ⟨c, k, fun n => ?_⟩
  apply Finset.sup_le
  intro a _
  calc
    projectedInnovation O (List.ofFn a) ≤ M.clock (List.ofFn a).length :=
      projectedInnovation_le_clock _ _
    _ = M.clock n := by rw [List.length_ofFn]
    _ ≤ c * (n + 1) ^ k := hclock n

/-- Languages decided in polynomial time by a charged machine carrying a finite causal observer.  Keeping the
observer witness explicit avoids silently assuming that every infinite-tape transition system has a finite
quotient. -/
def ObserverEquippedInP (L : List Bool → Bool) : Prop :=
  ∃ (M : ChargedMachine) (_O : CausalObserver M), IsPolyTime M ∧ Decides M L

/-- A super-polynomial projected-innovation lower bound against every observer-equipped charged decider
excludes the language from `ObserverEquippedInP`.  Connecting this class to all of real `P` requires a finite
causal-observer construction and is intentionally left as the next explicit obligation. -/
theorem not_ObserverEquippedInP_of_projected_lower (L : List Bool → Bool)
    (hLower : ∀ (M : ChargedMachine) (O : CausalObserver M),
      Decides M L → ¬ PolyBounded (RprojectedFor O)) : ¬ ObserverEquippedInP L := by
  rintro ⟨M, O, hpoly, hdec⟩
  exact hLower M O hdec (RprojectedFor_polyBounded O hpoly)

end PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine.observe_run
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine.projected_output_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine.RprojectedFor_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine.not_ObserverEquippedInP_of_projected_lower
