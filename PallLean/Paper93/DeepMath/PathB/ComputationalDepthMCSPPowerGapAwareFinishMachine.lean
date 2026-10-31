import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyRestore

/-!
# MCSP verifier: physical finish handoff across the retained power gap

The restored copy phase stops on the low cell of the internal `00`.  Old copy
state `8` would mistake that gap for final scratch.  This file defines one
fixed finite-control finisher which first validates and crosses exactly those
two cells, then traverses both power counters and the copied table, and writes
the final copied `01` terminator.  The gap remains physical in the output.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound
open PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopySeek
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyRestore
open GapCopyState

inductive GapFinishState
  | gapLo
  | gapHi
  | scanLo
  | scanHi (lo : Bool)
  | done
  | reject
  deriving DecidableEq, Fintype

open GapFinishState

/-- Fixed controller: validate/cross one `00`, scan every later pair whose
high cell is true, then turn the genuine final `00` into `01`. -/
def gapFinishMachine : Machine where
  State := GapFinishState
  fin := inferInstance
  dec := inferInstance
  start := gapLo
  halt
    | done | reject => true
    | _ => false
  δ
    | gapLo, b =>
        if b then (reject, none, 2) else (gapHi, none, 1)
    | gapHi, b =>
        if b then (reject, none, 2) else (scanLo, none, 1)
    | scanLo, b => (scanHi b, none, 1)
    | scanHi lo, b =>
        if b then (scanLo, none, 1)
        else if lo then (reject, none, 2)
        else (done, some true, 2)
    | done, _ => (done, none, 2)
    | reject, _ => (reject, none, 2)
  accept
    | done => true
    | _ => false

theorem run_two_finishGap {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false) :
    run gapFinishMachine 2 ⟨gapLo, p, T⟩ =
      ⟨scanLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapFinishMachine, moveHead, hlo, hhi]

theorem run_two_finishHigh {p : ℕ} {T : List Bool}
    (hhi : T.getD (p + 1) false = true) :
    run gapFinishMachine 2 ⟨scanLo, p, T⟩ =
      ⟨scanLo, p + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapFinishMachine, moveHead, hhi]

theorem run_finishHighs (T : List Bool) (q k : ℕ)
    (h : ∀ i, i < k → T.getD (q + 2 * i + 1) false = true) :
    run gapFinishMachine (2 * k) ⟨scanLo, q, T⟩ =
      ⟨scanLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        run_add, ih (fun i hi => h i (by omega))]
      simpa [Nat.mul_succ, Nat.add_assoc] using
        run_two_finishHigh (p := q + 2 * k) (T := T) (h k (by omega))

theorem run_two_finishBlank {p : ℕ} {T : List Bool}
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false) :
    run gapFinishMachine 2 ⟨scanLo, p, T⟩ =
      ⟨done, p + 1, writeAt T (p + 1) true⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  rw [run_succ, run_succ, run_zero]
  simp [step, gapFinishMachine, moveHead, hlo, hhi]

/-- Exact post-finish physical layout. -/
def gappedComparatorLayout (n a : ℕ) (payload : List Bool) : List Bool :=
  unaryD a ++ [false, false] ++ powBridge n ++ unaryD a ++ payload

/-- The retained gap is the sole difference from the already verified
comparator input.  This is a logical equation only; no physical deletion is
claimed. -/
theorem erasePowerHome_gappedComparatorLayout (n : ℕ)
    (table payload : List Bool) :
    erasePowerHome table.length
        (gappedComparatorLayout n table.length payload) =
      comparatorLayout n table payload := by
  simp [erasePowerHome, gappedComparatorLayout, comparatorLayout,
    powBridge, List.append_assoc]

theorem gappedComparatorLayout_length (n : ℕ)
    (table payload : List Bool) :
    (gappedComparatorLayout n table.length payload).length =
      (comparatorLayout n table payload).length + 2 := by
  simp [gappedComparatorLayout, comparatorLayout, powBridge,
    unaryD_length]
  omega

theorem gappedBridgeResS_all_eq (n a : ℕ) (suffix : List Bool) :
    gappedBridgeResS n a a suffix =
      unaryD a ++ [false, false] ++ powBridge n ++
        List.replicate (2 * a) true ++ [false, false] ++ suffix := by
  unfold gappedBridgeResS
  rw [Nat.sub_self]
  change List.replicate (2 * a) true ++
      ([] ++ ([false, true] ++ ([false, false] ++
        (powBridge n ++
          (List.replicate (2 * a) true ++ ([false, false] ++ suffix)))))) = _
  simp [unaryD_eq, List.append_assoc]

theorem gappedBridgeResS_finish (n a : ℕ) (suffix : List Bool) :
    let p := 4 * a + 4 * (2 ^ n) + 9
    writeAt (gappedBridgeResS n a a suffix) p true =
      gappedComparatorLayout n a suffix := by
  intro p
  let A := unaryD a ++ [false, false] ++ powBridge n ++
    List.replicate (2 * a) true ++ [false]
  have hp : A.length = p := by
    simp [A, p, unaryD_length, powBridge_length]
    omega
  rw [gappedBridgeResS_all_eq]
  have hshape : unaryD a ++ [false, false] ++ powBridge n ++
      List.replicate (2 * a) true ++ [false, false] ++ suffix =
      A ++ false :: suffix := by
    simp [A, List.append_assoc]
  rw [hshape, ← hp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  simp [gappedComparatorLayout, A, unaryD_eq, List.append_assoc]

theorem gappedBridgeResS_finish_high (n a i : ℕ)
    (suffix : List Bool) (hi : i < bridgePairs n + a) :
    (gappedBridgeResS n a a suffix).getD
      (2 * a + 4 + 2 * i + 1) false = true := by
  rw [gappedBridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * i + 1 =
      (unaryD a).length + (2 + (2 * i + 1)) by
        rw [unaryD_length]; omega,
    getD_append_left_length' _ _ rfl,
    show 2 + (2 * i + 1) =
      ([false, false] : List Bool).length + (2 * i + 1) by simp,
    getD_append_left_length' _ _ rfl]
  by_cases hb : i < bridgePairs n
  · rw [List.getD_append (h := by
      rw [powBridge_length_eq_pairs]
      omega)]
    exact powBridge_getD_high n i hb
  · rw [List.getD_append_right (h := by
      rw [powBridge_length_eq_pairs]
      omega), powBridge_length_eq_pairs]
    rw [List.getD_append (h := by rw [List.length_replicate]; omega)]
    exact List.getD_replicate _ (by omega)

theorem gappedBridgeResS_finish_blank_lo (n a : ℕ)
    (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD
      (2 * a + 4 + 2 * (bridgePairs n + a)) false = false := by
  rw [gappedBridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * (bridgePairs n + a) =
      (unaryD a).length +
        (2 + ((powBridge n).length + 2 * a)) by
        rw [unaryD_length, powBridge_length_eq_pairs]; ring,
    getD_append_left_length' _ _ rfl,
    show 2 + ((powBridge n).length + 2 * a) =
      ([false, false] : List Bool).length +
        ((powBridge n).length + 2 * a) by simp,
    getD_append_left_length' _ _ rfl,
    getD_append_left_length' _ _ rfl,
    getD_append_length' _ _ List.length_replicate]
  rfl

theorem gappedBridgeResS_finish_blank_hi (n a : ℕ)
    (suffix : List Bool) :
    (gappedBridgeResS n a a suffix).getD
      (2 * a + 4 + 2 * (bridgePairs n + a) + 1) false = false := by
  rw [gappedBridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * (bridgePairs n + a) + 1 =
      (unaryD a).length +
        (2 + ((powBridge n).length + (2 * a + 1))) by
        rw [unaryD_length, powBridge_length_eq_pairs]; ring,
    getD_append_left_length' _ _ rfl,
    show 2 + ((powBridge n).length + (2 * a + 1)) =
      ([false, false] : List Bool).length +
        ((powBridge n).length + (2 * a + 1)) by simp,
    getD_append_left_length' _ _ rfl,
    getD_append_left_length' _ _ rfl,
    List.getD_append_right (h := by rw [List.length_replicate]; omega),
    List.length_replicate]
  rw [show 2 * a + 1 - 2 * a = 1 by omega]
  rfl

def gapFinishClock (n a : ℕ) : ℕ :=
  2 + 2 * (bridgePairs n + a) + 2

theorem gapFinishClock_eq (n a : ℕ) :
    gapFinishClock n a = 2 * bridgePairs n + 2 * a + 4 := by
  unfold gapFinishClock
  ring

/-- Validate/cross the retained gap, traverse the bridge and copied table,
then write the copied marker. -/
theorem run_gapFinish_gappedLayout (pre : List Bool)
    (n a : ℕ) (payload : List Bool) :
    let q := pre.length + 2 * a + 2
    run gapFinishMachine (gapFinishClock n a)
      ⟨gapLo, q, pre ++ gappedBridgeResS n a a payload⟩ =
      ⟨done, pre.length + 4 * a + 4 * (2 ^ n) + 9,
        pre ++ gappedComparatorLayout n a payload⟩ := by
  intro q
  let T := pre ++ gappedBridgeResS n a a payload
  have hgap : run gapFinishMachine 2 ⟨gapLo, q, T⟩ =
      ⟨scanLo, q + 2, T⟩ := by
    apply run_two_finishGap
    · rw [show q = pre.length + (2 * a + 2) by rfl,
        show T = pre ++ gappedBridgeResS n a a payload by rfl,
        getD_append_left_length' _ _ rfl]
      exact gappedBridgeResS_gap_lo n a payload
    · rw [show q + 1 = pre.length + (2 * a + 3) by simp [q]; omega,
        show T = pre ++ gappedBridgeResS n a a payload by rfl,
        getD_append_left_length' _ _ rfl]
      exact gappedBridgeResS_gap_hi n a payload
  have hhigh := run_finishHighs T (q + 2) (bridgePairs n + a)
    (fun i hi => by
      rw [show q + 2 + 2 * i + 1 =
        pre.length + (2 * a + 4 + 2 * i + 1) by simp [q]; omega,
        show T = pre ++ gappedBridgeResS n a a payload by rfl,
        getD_append_left_length' _ _ rfl]
      exact gappedBridgeResS_finish_high n a i payload hi)
  have hblank := run_two_finishBlank
    (p := q + 2 + 2 * (bridgePairs n + a)) (T := T)
    (by
      rw [show q + 2 + 2 * (bridgePairs n + a) =
        pre.length + (2 * a + 4 + 2 * (bridgePairs n + a)) by
          simp [q]; omega,
        show T = pre ++ gappedBridgeResS n a a payload by rfl,
        getD_append_left_length' _ _ rfl]
      exact gappedBridgeResS_finish_blank_lo n a payload)
    (by
      rw [show q + 2 + 2 * (bridgePairs n + a) + 1 =
        pre.length +
          (2 * a + 4 + 2 * (bridgePairs n + a) + 1) by
          simp [q]; omega,
        show T = pre ++ gappedBridgeResS n a a payload by rfl,
        getD_append_left_length' _ _ rfl]
      exact gappedBridgeResS_finish_blank_hi n a payload)
  rw [gapFinishClock,
    show 2 + 2 * (bridgePairs n + a) + 2 =
      2 + (2 * (bridgePairs n + a) + 2) by omega,
    run_add, hgap, run_add, hhigh, hblank]
  have hpos : q + 2 + 2 * (bridgePairs n + a) + 1 =
      pre.length + 4 * a + 4 * (2 ^ n) + 9 := by
    simp [q, bridgePairs]
    ring
  rw [hpos]
  have hwrite : writeAt T
      (pre.length + (4 * a + 4 * (2 ^ n) + 9)) true =
      pre ++ gappedComparatorLayout n a payload := by
    rw [show T = pre ++ gappedBridgeResS n a a payload by rfl,
      writeAt_append_right pre (gappedBridgeResS n a a payload)
      pre.length (4 * a + 4 * (2 ^ n) + 9) true rfl (by
        rw [gappedBridgeResS_length n a a payload (le_refl a)]
        omega), gappedBridgeResS_finish]
  simpa [Nat.add_assoc] using hwrite

theorem gapFinish_gappedLayout_halts (pre : List Bool)
    (n a : ℕ) (payload : List Bool) :
    let q := pre.length + 2 * a + 2
    gapFinishMachine.halt
      (run gapFinishMachine (gapFinishClock n a)
        ⟨gapLo, q, pre ++ gappedBridgeResS n a a payload⟩).st = true := by
  intro q
  rw [run_gapFinish_gappedLayout]
  rfl

/-- Consume the exact tape/head produced by the full physical gapped copy and
restore phase. -/
theorem run_gapFinish_after_copy (pre : List Bool)
    (n a : ℕ) (payload : List Bool) (s : Bool) :
    let handoff := run gapCopyMachine (gappedCopyToHandoffClock n a)
      ⟨.copy (0, s) false, localOffset pre,
        localTape pre (gappedBridgeCpyS n a 0 0 payload)⟩
    run gapFinishMachine (gapFinishClock n a)
      ⟨gapLo, handoff.hd, handoff.tp⟩ =
      ⟨done,
        (homePrefix pre).length + 4 * a + 4 * (2 ^ n) + 9,
        homePrefix pre ++ gappedComparatorLayout n a payload⟩ := by
  intro handoff
  rw [show handoff =
      ⟨.copy (8, false) false, localOffset pre + 2 * a + 2,
        localTape pre (gappedBridgeResS n a a payload)⟩ by
      exact run_gapped_copy_to_handoff pre payload n a s]
  simpa [localTape, localOffset, homePrefix, List.append_assoc] using
    run_gapFinish_gappedLayout (homePrefix pre) n a payload

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine.run_gapFinish_gappedLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine.gapFinish_gappedLayout_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine.run_gapFinish_after_copy
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine.gapFinishClock_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareFinishMachine.erasePowerHome_gappedComparatorLayout
