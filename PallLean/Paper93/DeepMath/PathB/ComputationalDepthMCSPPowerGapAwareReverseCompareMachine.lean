import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCompareHomeMachine

/-!
# MCSP verifier: tagged reverse comparator over the retained physical gap

The reverse comparison starts at tape cell zero, so the ordinary comparator's
absolute resets are already correct.  Its only physical mismatch is the `00`
between the first counter's `01` boundary and the first power counter.  This
file defines a fixed finite-control wrapper which agrees exactly with every
ordinary comparator transition except that one tagged boundary transition,
where it validates and crosses both gap cells before resuming state `4`.

The resulting transition lift and exact three-step crossing are the control
interface needed to transport the existing round proof onto the live tape.
Both possible destructive endgame descriptors are also connected directly to
the verified local-home adapter.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine

inductive ReverseCompareState
  | cmp (q : Fin 8) (stored : Bool)
  | gapLo
  | gapHi
  | malformed
  deriving DecidableEq, Fintype

open ReverseCompareState

def liftCompareTransition
    (tr : compareMachine.State × Option Bool × Move) :
    ReverseCompareState × Option Bool × Move :=
  (.cmp tr.1.1 tr.1.2, tr.2.1, tr.2.2)

/-- The reverse wrapper is the ordinary comparator everywhere except the
unique `state 3 / stored false / read true` boundary transition. -/
def reverseCompareMachine : Machine where
  State := ReverseCompareState
  fin := inferInstance
  dec := inferInstance
  start := .cmp 0 false
  halt
    | .cmp q _ => decide (q = 6) || decide (q = 7)
    | .malformed => true
    | _ => false
  δ
    | .cmp q s, b =>
        if q = 3 ∧ s = false ∧ b = true then
          (.gapLo, none, 1)
        else
          liftCompareTransition (compareMachine.δ (q, s) b)
    | .gapLo, false => (.gapHi, none, 1)
    | .gapLo, true => (.malformed, none, 2)
    | .gapHi, false => (.cmp 4 false, none, 1)
    | .gapHi, true => (.malformed, none, 2)
    | .malformed, _ => (.malformed, none, 2)
  accept
    | .cmp q _ => decide (q = 6)
    | _ => false

def liftCompareCfg (c : Cfg compareMachine) : Cfg reverseCompareMachine :=
  ⟨.cmp c.st.1 c.st.2, c.hd, c.tp⟩

theorem init_reverseCompare (T : List Bool) :
    init reverseCompareMachine T = liftCompareCfg (init compareMachine T) := rfl

/-- Every ordinary nonhalting transition other than the unique boundary
crossing is simulated literally: same optional write, same head motion,
same tape.  This includes the comparator's absolute reset after marking `B`. -/
theorem step_reverseCompare_lift (c : Cfg compareMachine)
    (hhalt : compareMachine.halt c.st = false)
    (hspecial : ¬(c.st.1 = 3 ∧ c.st.2 = false ∧
      c.tp.getD c.hd false = true)) :
    step reverseCompareMachine (liftCompareCfg c) =
      liftCompareCfg (step compareMachine c) := by
  rcases c with ⟨⟨q, s⟩, p, T⟩
  simp only [liftCompareCfg]
  unfold step
  rw [hhalt]
  have hrhalt : reverseCompareMachine.halt (.cmp q s) = false := by
    simpa [reverseCompareMachine, compareMachine] using hhalt
  rw [hrhalt]
  simp only [reverseCompareMachine, hspecial, ↓reduceIte,
    liftCompareTransition]
  rfl

/-! ## Explicit inherited comparator transitions -/

theorem step_reverse_c0 {s : Bool} {p : ℕ} {T : List Bool} :
    step reverseCompareMachine ⟨.cmp 0 s, p, T⟩ =
      ⟨.cmp 1 (T.getD p false), p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(0, s), p, T⟩ : Cfg compareMachine)) (by rfl) (by simp)
  rw [step_c0] at h
  exact h

theorem step_reverse_c1_mark {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) :
    step reverseCompareMachine ⟨.cmp 1 true, p, T⟩ =
      ⟨.cmp 2 true, p + 1, writeAt T p false⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(1, true), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c1_mark hread] at h
  exact h

theorem step_reverse_c1_skip {p : ℕ} {T : List Bool}
    (hread : T.getD p false = false) :
    step reverseCompareMachine ⟨.cmp 1 true, p, T⟩ =
      ⟨.cmp 0 true, p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(1, true), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c1_skip hread] at h
  exact h

theorem step_reverse_c1_accept {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) :
    step reverseCompareMachine ⟨.cmp 1 false, p, T⟩ =
      ⟨.cmp 6 false, p, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(1, false), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c1_acc hread] at h
  exact h

theorem step_reverse_c2 {s : Bool} {p : ℕ} {T : List Bool} :
    step reverseCompareMachine ⟨.cmp 2 s, p, T⟩ =
      ⟨.cmp 3 (T.getD p false), p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(2, s), p, T⟩ : Cfg compareMachine)) (by rfl) (by simp)
  rw [step_c2] at h
  exact h

theorem step_reverse_c3_data {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) :
    step reverseCompareMachine ⟨.cmp 3 true, p, T⟩ =
      ⟨.cmp 2 true, p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(3, true), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c3_data hread] at h
  exact h

theorem step_reverse_c4 {s : Bool} {p : ℕ} {T : List Bool} :
    step reverseCompareMachine ⟨.cmp 4 s, p, T⟩ =
      ⟨.cmp 5 (T.getD p false), p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(4, s), p, T⟩ : Cfg compareMachine)) (by rfl) (by simp)
  rw [step_c4] at h
  exact h

theorem step_reverse_c5_mark {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) :
    step reverseCompareMachine ⟨.cmp 5 true, p, T⟩ =
      ⟨.cmp 0 true, 0, writeAt T p false⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(5, true), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c5_mark hread] at h
  exact h

theorem step_reverse_c5_skip {p : ℕ} {T : List Bool}
    (hread : T.getD p false = false) :
    step reverseCompareMachine ⟨.cmp 5 true, p, T⟩ =
      ⟨.cmp 4 true, p + 1, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(5, true), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c5_skip hread] at h
  exact h

theorem step_reverse_c5_reject {p : ℕ} {T : List Bool}
    (hread : T.getD p false = true) :
    step reverseCompareMachine ⟨.cmp 5 false, p, T⟩ =
      ⟨.cmp 7 false, p, T⟩ := by
  have h := step_reverseCompare_lift
    (c := (⟨(5, false), p, T⟩ : Cfg compareMachine))
    (by rfl) (by simp)
  rw [step_c5_rej hread] at h
  exact h

/-! ## The unique physical gap crossing -/

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem step_reverse_enterGap (P R : List Bool) :
    step reverseCompareMachine
      ⟨.cmp 3 false, P.length, P ++ true :: R⟩ =
      ⟨.gapLo, P.length + 1, P ++ true :: R⟩ := by
  unfold step
  rw [show reverseCompareMachine.halt (.cmp 3 false) = false from rfl,
    getD_boundary]
  rfl

theorem step_reverse_gapLo (P R : List Bool) :
    step reverseCompareMachine
      ⟨.gapLo, P.length, P ++ false :: R⟩ =
      ⟨.gapHi, P.length + 1, P ++ false :: R⟩ := by
  unfold step
  rw [show reverseCompareMachine.halt .gapLo = false from rfl,
    getD_boundary]
  rfl

theorem step_reverse_gapHi (P R : List Bool) :
    step reverseCompareMachine
      ⟨.gapHi, P.length, P ++ false :: R⟩ =
      ⟨.cmp 4 false, P.length + 1, P ++ false :: R⟩ := by
  unfold step
  rw [show reverseCompareMachine.halt .gapHi = false from rfl,
    getD_boundary]
  rfl

/-- The old one-step boundary transition becomes exactly three physical
steps: enter the tagged gap, validate `00`, resume on `B`. -/
theorem run_reverse_crossGap (P R : List Bool) :
    run reverseCompareMachine 3
      ⟨.cmp 3 false, P.length,
        P ++ true :: false :: false :: R⟩ =
      ⟨.cmp 4 false, P.length + 3,
        P ++ true :: false :: false :: R⟩ := by
  rw [show 3 = 1 + (1 + 1) by omega, run_add]
  change run reverseCompareMachine (1 + 1)
    (step reverseCompareMachine
      ⟨.cmp 3 false, P.length,
        P ++ true :: false :: false :: R⟩) = _
  rw [step_reverse_enterGap P (false :: false :: R)]
  rw [show P ++ true :: false :: false :: R =
      (P ++ [true]) ++ false :: false :: R by simp]
  rw [run_add]
  simp only [run, Function.iterate_one]
  have hlo := step_reverse_gapLo (P ++ [true]) (false :: R)
  have hlo' : step reverseCompareMachine
      ⟨.gapLo, P.length + 1,
        (P ++ [true]) ++ false :: false :: R⟩ =
      ⟨.gapHi, P.length + 2,
        (P ++ [true]) ++ false :: false :: R⟩ := by
    simpa using hlo
  rw [hlo']
  rw [show (P ++ [true]) ++ false :: false :: R =
      (P ++ [true, false]) ++ false :: R by simp]
  simpa using step_reverse_gapHi (P ++ [true, false]) R

theorem step_reverse_badGapLo (P R : List Bool) :
    step reverseCompareMachine
      ⟨.gapLo, P.length, P ++ true :: R⟩ =
      ⟨.malformed, P.length, P ++ true :: R⟩ := by
  unfold step
  rw [show reverseCompareMachine.halt .gapLo = false from rfl,
    getD_boundary]
  rfl

theorem step_reverse_badGapHi (P R : List Bool) :
    step reverseCompareMachine
      ⟨.gapHi, P.length, P ++ true :: R⟩ =
      ⟨.malformed, P.length, P ++ true :: R⟩ := by
  unfold step
  rw [show reverseCompareMachine.halt .gapHi = false from rfl,
    getD_boundary]
  rfl

/-! ## Exact live-tape descriptors and adapter handoff -/

def reversePhysicalTape (a b jA jB : ℕ) (rest : List Bool) : List Bool :=
  compareHomeTape a b jA jB rest

theorem reversePhysicalTape_zero (a b : ℕ) (rest : List Bool) :
    reversePhysicalTape a b 0 0 rest =
      unaryD a ++ [false, false] ++ unaryD b ++ rest := by
  simp [reversePhysicalTape, compareHomeTape, workD_zero,
    List.append_assoc]

theorem reversePhysicalTape_gappedComparatorLayout (n a : ℕ)
    (payload : List Bool) :
    reversePhysicalTape a (2 ^ n) 0 0
        (unaryD (2 ^ n) ++ unaryD a ++ payload) =
      gappedComparatorLayout n a payload := by
  simp [reversePhysicalTape_zero, gappedComparatorLayout, powBridge,
    List.append_assoc]

/-- The accepting destructive reverse shape feeds the already verified
arbitrary-head local-home adapter without any tape conversion. -/
theorem reverse_accept_handoff (a b p : ℕ) (hab : a ≤ b)
    (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      ⟨.reset, p, reversePhysicalTape a b a a rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        reversePhysicalTape a b a a rest⟩ :=
  machine_run_after_reverse_accept a b p hab rest

/-- The rejecting destructive reverse shape feeds the same adapter. -/
theorem reverse_reject_handoff (a b p : ℕ) (hab : b < a)
    (rest : List Bool) :
    run compareHomeMachine (compareHomeClock a b)
      ⟨.reset, p, reversePhysicalTape a b (b + 1) b rest⟩ =
      ⟨.accept, 2 * a + 2 * b + 6,
        reversePhysicalTape a b (b + 1) b rest⟩ :=
  machine_run_after_reverse_reject a b p hab rest

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.step_reverseCompare_lift
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.run_reverse_crossGap
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.step_reverse_badGapLo
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.step_reverse_badGapHi
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.reverse_accept_handoff
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine.reverse_reject_handoff
