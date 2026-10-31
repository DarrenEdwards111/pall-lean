import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyRun
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# MCSP verifier: prefix lifting for local counter copying

The reset macro makes the verified unary copy controller local-home aware.
The other transitions still need to be transported from a counter at tape
cell `0` to a counter following an arbitrary live prefix and its `00` home
delimiter.

This file proves that transport once, generically.  Reads, in-range writes,
and every non-reset head move commute with the prefix offset.  Consequently a
non-reset step of the original copy machine is simulated exactly by one step
of `localCopyMachine`, with the arbitrary prefix and delimiter preserved.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open LocalCopyState

def homePrefix (pre : List Bool) : List Bool := pre ++ [false, false]

def localTape (pre T : List Bool) : List Bool := homePrefix pre ++ T

def localOffset (pre : List Bool) : ℕ := pre.length + 2

theorem homePrefix_length (pre : List Bool) :
    (homePrefix pre).length = localOffset pre := by
  simp [homePrefix, localOffset]

theorem localTape_getD (pre T : List Bool) (p : ℕ) :
    (localTape pre T).getD (localOffset pre + p) false =
      T.getD p false := by
  unfold localTape
  exact getD_append_left_length' (homePrefix pre) T
    (homePrefix_length pre) p false

theorem localTape_writeAt (pre T : List Bool) (p : ℕ) (w : Bool)
    (hp : p < T.length) :
    writeAt (localTape pre T) (localOffset pre + p) w =
      localTape pre (writeAt T p w) := by
  unfold localTape
  exact writeAt_append_right (homePrefix pre) T
    (localOffset pre) p w (homePrefix_length pre) hp

/-- Any non-reset move commutes with adding the local-counter offset.  A left
move additionally needs the original head to be positive, exactly as in the
copy machine's proved passes. -/
theorem moveHead_localOffset (pre : List Bool) (p : ℕ) (m : Move)
    (hreset : m ≠ 3) (hleft : m = 0 → 0 < p) :
    moveHead (localOffset pre + p) m =
      localOffset pre + moveHead p m := by
  fin_cases m <;> simp [moveHead] at hreset hleft ⊢ <;> omega

def liftCopyCfg (pre : List Bool) (c : Cfg copyMachine) :
    Cfg localCopyMachine :=
  ⟨.copy c.st, localOffset pre + c.hd, localTape pre c.tp⟩

/-- Generic one-step prefix lift.  The hypotheses say precisely that this is
a non-reset transition, a possible left move does not underflow in the
unshifted run, and an optional write stays in the live suffix. -/
theorem step_localCopy_lift (pre : List Bool) (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hreset : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd)
    (hwrite : ∀ w, (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.1 = some w → c.hd < c.tp.length) :
    step localCopyMachine (liftCopyCfg pre c) =
      liftCopyCfg pre (step copyMachine c) := by
  let tr := copyMachine.δ c.st (c.tp.getD c.hd false)
  have hread : (localTape pre c.tp).getD
      (localOffset pre + c.hd) false = c.tp.getD c.hd false :=
    localTape_getD pre c.tp c.hd
  have hmove : moveHead (localOffset pre + c.hd) tr.2.2 =
      localOffset pre + moveHead c.hd tr.2.2 :=
    moveHead_localOffset pre c.hd tr.2.2 hreset hleft
  unfold liftCopyCfg
  simp only [step, localCopyMachine, hhalt, Bool.false_eq_true,
    if_false, hread]
  rw [if_neg hreset]
  change
    (⟨.copy tr.1, moveHead (localOffset pre + c.hd) tr.2.2,
      match tr.2.1 with
      | none => localTape pre c.tp
      | some w => writeAt (localTape pre c.tp)
          (localOffset pre + c.hd) w⟩ : Cfg localCopyMachine) =
    (⟨.copy tr.1, localOffset pre + moveHead c.hd tr.2.2,
      localTape pre
        (match tr.2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w)⟩ : Cfg localCopyMachine)
  rw [hmove]
  cases hw : tr.2.1 with
  | none => rfl
  | some w =>
      simpa using localTape_writeAt pre c.tp c.hd w
        (hwrite w (by simpa [tr] using hw))

/-- A whole reset-free copy pass lifts through the arbitrary live prefix.
The hypotheses are pointwise versions of the one-step safety conditions and
are exactly what the existing find/seek/restore run invariants provide. -/
theorem run_localCopy_lift_nonreset (pre : List Bool)
    (c : Cfg copyMachine) (t : ℕ)
    (hhalt : ∀ i, i < t →
      copyMachine.halt (run copyMachine i c).st = false)
    (hreset : ∀ i, i < t →
      (copyMachine.δ (run copyMachine i c).st
        ((run copyMachine i c).tp.getD
          (run copyMachine i c).hd false)).2.2 ≠ 3)
    (hleft : ∀ i, i < t →
      (copyMachine.δ (run copyMachine i c).st
        ((run copyMachine i c).tp.getD
          (run copyMachine i c).hd false)).2.2 = 0 →
        0 < (run copyMachine i c).hd)
    (hwrite : ∀ i, i < t → ∀ w,
      (copyMachine.δ (run copyMachine i c).st
        ((run copyMachine i c).tp.getD
          (run copyMachine i c).hd false)).2.1 = some w →
        (run copyMachine i c).hd <
          (run copyMachine i c).tp.length) :
    run localCopyMachine t (liftCopyCfg pre c) =
      liftCopyCfg pre (run copyMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ,
        ih
          (fun i hi => hhalt i (by omega))
          (fun i hi => hreset i (by omega))
          (fun i hi => hleft i (by omega))
          (fun i hi => hwrite i (by omega)),
        step_localCopy_lift pre (run copyMachine t c)
          (hhalt t (by omega))
          (hreset t (by omega))
          (hleft t (by omega))
          (hwrite t (by omega)),
        ← run_succ]

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift.step_localCopy_lift
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift.run_localCopy_lift_nonreset
