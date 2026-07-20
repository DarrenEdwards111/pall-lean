import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinWrite

/-!
# Faithful-machine circuit simulation: bounded snapshots

This is the first concrete brick for discharging
`SATCircuitSeparationBridge.ComposablePSubsetPpoly`.  A time-`T` run of the
faithful `ComposableMachine` on an `n`-bit input only visits tape positions below
`n + T + 1`; therefore every row of the run has a finite Boolean snapshot.

The transition equations below are exact consequences of the real machine semantics:

* the next state/head are `stepStateHead` of the current state, head, and scanned bit;
* the old head cell becomes `writtenBit`;
* every other bounded cell is copied.

These equations are the semantic specification for the Boolean step circuit.  They
include halted configurations and all four moves, including reset-to-zero; no alternate
machine model is substituted.
-/

namespace PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite

/-- Number of tape positions sufficient for every row through time `T` on an input of
length `n`. -/
def spaceBound (n T : ℕ) : ℕ := n + T + 1

/-- The real run's head lies in the finite snapshot through time `T`. -/
theorem run_head_lt_spaceBound (M : Machine) (x : List Bool) {t T : ℕ} (ht : t ≤ T) :
    (run M t (init M x)).hd < spaceBound x.length T := by
  have h := (run_bounds M x t).1
  unfold spaceBound
  omega

/-- The real run's materialized tape also fits in the finite snapshot. -/
theorem run_tape_length_le_spaceBound (M : Machine) (x : List Bool) {t T : ℕ} (ht : t ≤ T) :
    (run M t (init M x)).tp.length ≤ spaceBound x.length T := by
  have h := (run_bounds M x t).2
  unfold spaceBound
  omega

/-- Tape bit `p` in row `t` of the bounded real-run snapshot. -/
def cellBit (M : Machine) (x : List Bool) (t T : ℕ)
    (p : Fin (spaceBound x.length T)) : Bool :=
  (run M t (init M x)).tp.getD p.val false

/-- One-hot head bit `p` in row `t`. -/
def headBit (M : Machine) (x : List Bool) (t T : ℕ)
    (p : Fin (spaceBound x.length T)) : Bool :=
  decide ((run M t (init M x)).hd = p.val)

/-- One-hot finite-control bit `q` in row `t`. -/
noncomputable def controlBit (M : Machine) (x : List Bool) (t : ℕ)
    (q : Fin (Fintype.card M.State)) : Bool :=
  decide (Fintype.equivFin M.State (run M t (init M x)).st = q)

/-- The head encoding is genuinely one-hot: the in-range real head bit is true. -/
theorem headBit_real_head (M : Machine) (x : List Bool) {t T : ℕ} (ht : t ≤ T) :
    headBit M x t T ⟨(run M t (init M x)).hd, run_head_lt_spaceBound M x ht⟩ = true := by
  simp [headBit]

/-- The control encoding is genuinely one-hot at the real state. -/
theorem controlBit_real_state (M : Machine) (x : List Bool) (t : ℕ) :
    controlBit M x t (Fintype.equivFin M.State (run M t (init M x)).st) = true := by
  simp [controlBit]

/-- Exact bounded-tape transition.  The old head cell receives `writtenBit`; every
other cell is copied. -/
theorem cellBit_succ (M : Machine) (x : List Bool) (t T : ℕ)
    (p : Fin (spaceBound x.length T)) :
    cellBit M x (t + 1) T p =
      if p.val = (run M t (init M x)).hd then
        writtenBit M (run M t (init M x)).st
          ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)
      else cellBit M x t T p := by
  rw [cellBit, run_succ]
  by_cases hp : p.val = (run M t (init M x)).hd
  · rw [if_pos hp, hp, step_tape_getD_head]
  · rw [if_neg hp]
    exact step_tape_getD_ne_all M (run M t (init M x)) p.val hp

/-- Exact next-head bit, including reset and halted self-loops. -/
theorem headBit_succ (M : Machine) (x : List Bool) (t T : ℕ)
    (p : Fin (spaceBound x.length T)) :
    headBit M x (t + 1) T p = decide
      ((stepStateHead M (run M t (init M x)).st (run M t (init M x)).hd
        ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)).2 = p.val) := by
  unfold headBit
  rw [run_succ, (step_via_stepStateHead M (run M t (init M x))).2]

/-- Exact next-control bit. -/
theorem controlBit_succ (M : Machine) (x : List Bool) (t : ℕ)
    (q : Fin (Fintype.card M.State)) :
    controlBit M x (t + 1) q = decide
      (Fintype.equivFin M.State
        (stepStateHead M (run M t (init M x)).st (run M t (init M x)).hd
          ((run M t (init M x)).tp.getD (run M t (init M x)).hd false)).1 = q) := by
  unfold controlBit
  rw [run_succ, (step_via_stepStateHead M (run M t (init M x))).1]

end PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot

#print axioms PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot.run_head_lt_spaceBound
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot.cellBit_succ
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot.headBit_succ
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableCircuitSnapshot.controlBit_succ
