import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTwoPowMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterIncr

/-!
# MCSP verifier: finalize the `2^n` accumulator as a standard unary counter

`MCSPTwoPowMachine` finishes with `2^n - 1` doubled `11` units followed by its
old `00` separator.  This tiny finite-control pass turns that separator into
the missing `11` unit and writes a fresh `01` boundary immediately after it.
Consequently the tape begins with the repository's standard
`unaryD (2^n)` counter, ready for the table-count comparison phase.

The pass is local and uniform: scan the true accumulator cells, then perform
four fixed writes `00uv ↦ 1101`.  Its exact run, output, halting, and linear
clock are proved below.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTwoPowFinalizeMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.MCSPTwoPowMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.UnaryDupMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

inductive FinalState
  | scan
  | secondOne
  | markerLow
  | markerHigh
  | done
  deriving DecidableEq, Fintype

/-- Convert the leading `11* 00` accumulator into `unaryD`. -/
def finalizeMachine : Machine where
  State := FinalState
  fin := inferInstance
  dec := inferInstance
  start := .scan
  halt
    | .done => true
    | _ => false
  δ q b :=
    match q with
    | .scan =>
        if b then (.scan, none, 1)
        else (.secondOne, some true, 1)
    | .secondOne => (.markerLow, some true, 1)
    | .markerLow => (.markerHigh, some false, 1)
    | .markerHigh => (.done, some true, 2)
    | .done => (.done, none, 2)
  accept
    | .done => true
    | _ => false

theorem step_scan_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step finalizeMachine ⟨.scan, p, T⟩ =
      ⟨.scan, p + 1, T⟩ := by
  unfold step
  rw [show finalizeMachine.halt .scan = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show finalizeMachine.δ .scan (T.getD p false) =
      if T.getD p false then (.scan, none, 1)
      else (.secondOne, some true, 1) from rfl, h]
  rfl

theorem step_scan_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step finalizeMachine ⟨.scan, p, T⟩ =
      ⟨.secondOne, p + 1, writeAt T p true⟩ := by
  unfold step
  rw [show finalizeMachine.halt .scan = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show finalizeMachine.δ .scan (T.getD p false) =
      if T.getD p false then (.scan, none, 1)
      else (.secondOne, some true, 1) from rfl, h]
  rfl

theorem step_secondOne {p : ℕ} {T : List Bool} :
    step finalizeMachine ⟨.secondOne, p, T⟩ =
      ⟨.markerLow, p + 1, writeAt T p true⟩ := by
  rfl

theorem step_markerLow {p : ℕ} {T : List Bool} :
    step finalizeMachine ⟨.markerLow, p, T⟩ =
      ⟨.markerHigh, p + 1, writeAt T p false⟩ := by
  rfl

theorem step_markerHigh {p : ℕ} {T : List Bool} :
    step finalizeMachine ⟨.markerHigh, p, T⟩ =
      ⟨.done, p, writeAt T p true⟩ := by
  rfl

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem scan_true_cells (P R : List Bool) (k : ℕ) :
    run finalizeMachine k
      ⟨.scan, P.length, P ++ List.replicate k true ++ R⟩ =
      ⟨.scan, P.length + k, P ++ List.replicate k true ++ R⟩ := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ]
      rw [show k + 1 = 1 + k by omega, run_add]
      change run finalizeMachine k
        (step finalizeMachine
          ⟨.scan, P.length,
            P ++ true :: List.replicate k true ++ R⟩) = _
      have hread :
          (P ++ true :: List.replicate k true ++ R).getD
            P.length false = true := by
        rw [show P ++ true :: List.replicate k true ++ R =
          P ++ true :: (List.replicate k true ++ R) by
            simp [List.append_assoc]]
        exact getD_boundary P true (List.replicate k true ++ R)
      rw [step_scan_true hread]
      have H := ih (P ++ [true])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

/-- Four writes implement `00uv ↦ 1101`, independent of the overwritten
scratch bits `u,v`. -/
theorem write_counter_tail (P R : List Bool) (u v : Bool) :
    run finalizeMachine 4
      ⟨.scan, P.length, P ++ false :: false :: u :: v :: R⟩ =
      ⟨.done, P.length + 3, P ++ true :: true :: false :: true :: R⟩ := by
  change step finalizeMachine
      (step finalizeMachine
        (step finalizeMachine
          (step finalizeMachine
            ⟨.scan, P.length, P ++ false :: false :: u :: v :: R⟩))) = _
  rw [step_scan_false (getD_boundary P false (false :: u :: v :: R))]
  rw [PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  rw [step_secondOne]
  rw [show P ++ true :: false :: u :: v :: R =
      (P ++ [true]) ++ false :: u :: v :: R by simp,
    show P.length + 1 = (P ++ [true]).length by simp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  rw [step_markerLow]
  rw [show P ++ [true] ++ true :: u :: v :: R =
      (P ++ [true, true]) ++ u :: v :: R by simp,
    show (P ++ [true]).length + 1 =
      (P ++ [true, true]).length by simp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  rw [step_markerHigh]
  rw [show P ++ [true, true] ++ false :: v :: R =
      (P ++ [true, true, false]) ++ v :: R by simp,
    show (P ++ [true, true]).length + 1 =
      (P ++ [true, true, false]).length by simp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  simp

/-- Exact conversion of a generic `a`-unit accumulator. -/
theorem finalize_run (a : ℕ) (u v : Bool) (rest : List Bool) :
    run finalizeMachine (2 * a + 4)
      (init finalizeMachine
        (List.replicate (2 * a) true ++ false :: false :: u :: v :: rest)) =
      ⟨.done, 2 * a + 3, unaryD (a + 1) ++ rest⟩ := by
  rw [run_add]
  change run finalizeMachine 4
    (run finalizeMachine (2 * a)
      ⟨.scan, 0,
        List.replicate (2 * a) true ++ false :: false :: u :: v :: rest⟩) = _
  have hs := scan_true_cells []
    (false :: false :: u :: v :: rest) (2 * a)
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hs
  rw [hs]
  have hw := write_counter_tail
    (List.replicate (2 * a) true) rest u v
  rw [List.length_replicate] at hw
  rw [hw]
  rw [unaryD_eq, show 2 * (a + 1) = 2 * a + 2 by omega,
    List.replicate_add]
  simp

/-- Scratch left between the finalized counter and the payload. -/
def finalGarbage : ℕ → List Bool → List Bool
  | 0, rest => rest
  | n + 1, rest =>
      List.replicate (2 * n) false ++ true :: false :: rest

/-- Applied to the exact terminal tape of `twoPow_run`, the pass exposes a
standard `unaryD (2^n)` counter at the tape front. -/
theorem finalize_twoPow_tape (n : ℕ) (rest : List Bool) :
    run finalizeMachine (2 * (2 ^ n - 1) + 4)
      (init finalizeMachine
        (powTape (2 ^ n - 1) n 0 rest)) =
      ⟨.done, 2 * (2 ^ n - 1) + 3,
        unaryD (2 ^ n) ++ finalGarbage n rest⟩ := by
  cases n with
  | zero =>
      simpa [powTape, workspace_zero, finalGarbage,
        PallLean.Paper93.DeepMath.PathB.DIndexMachine.flat2] using
        finalize_run 0 true false rest
  | succ n =>
      have h := finalize_run (2 ^ (n + 1) - 1) false false
        (List.replicate (2 * n) false ++ true :: false :: rest)
      have hpow : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have hsucc : 2 * (n + 1) = 2 + 2 * n := by omega
      simpa [powTape, workspace_zero, finalGarbage,
        flat2_replicate_true, hsucc, List.replicate_add,
        Nat.sub_add_cancel hpow] using h

def finalizeClock (N : ℕ) : ℕ := N + 4

theorem finalizeClock_poly : PolyBounded finalizeClock :=
  ⟨5, 1, fun N => by simp [finalizeClock]; omega⟩

end PallLean.Paper93.DeepMath.PathB.MCSPTwoPowFinalizeMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowFinalizeMachine.finalize_run
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowFinalizeMachine.finalize_twoPow_tape
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTwoPowFinalizeMachine.finalizeClock_poly
