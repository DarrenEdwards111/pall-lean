import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorBridgeCopyRounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# MCSP verifier: bridge-aware copied-counter finish machine

The ordinary unary-copy finish states skip only `11` pairs.  That is correct
for adjacent scratch, but not for the comparator bridge: each intervening
power counter ends in an `01` marker.  This file supplies the required fixed
finite-control scanner.  It skips every pair whose high cell is true (`11`
or `01`), rejects malformed `10`, and writes the copied `01` terminator only
when it reaches the reserved `00` pair.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyRound

inductive BridgeFinishState
  | scanLo
  | scanHi (lo : Bool)
  | done
  | reject
  deriving DecidableEq, Fintype

open BridgeFinishState

/-- Fixed bridge-aware end scanner. -/
def bridgeFinishMachine : Machine where
  State := BridgeFinishState
  fin := inferInstance
  dec := inferInstance
  start := scanLo
  halt
    | done | reject => true
    | _ => false
  δ
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

theorem step_scanLo {p : ℕ} {T : List Bool} :
    step bridgeFinishMachine ⟨scanLo, p, T⟩ =
      ⟨scanHi (T.getD p false), p + 1, T⟩ := by
  simp [step, bridgeFinishMachine, moveHead]

theorem step_scanHi_true {lo : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step bridgeFinishMachine ⟨scanHi lo, p, T⟩ =
      ⟨scanLo, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, bridgeFinishMachine, moveHead, h]

theorem step_scanHi_blank {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step bridgeFinishMachine ⟨scanHi false, p, T⟩ =
      ⟨done, p, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, bridgeFinishMachine, moveHead, h]

theorem step_scanHi_malformed {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step bridgeFinishMachine ⟨scanHi true, p, T⟩ =
      ⟨reject, p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, bridgeFinishMachine, moveHead, h]

/-- A pair with true high cell is skipped regardless of its low cell. -/
theorem run_two_high (p : ℕ) (T : List Bool)
    (hhi : T.getD (p + 1) false = true) :
    run bridgeFinishMachine 2 ⟨scanLo, p, T⟩ =
      ⟨scanLo, p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_scanLo,
    step_scanHi_true hhi]

/-- Skip `k` consecutive doubled pairs whose high cells are true. -/
theorem run_high_pairs (T : List Bool) (q k : ℕ)
    (h : ∀ i, i < k → T.getD (q + 2 * i + 1) false = true) :
    run bridgeFinishMachine (2 * k) ⟨scanLo, q, T⟩ =
      ⟨scanLo, q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        run_add, ih (fun i hi => h i (by omega))]
      simpa [Nat.mul_succ, Nat.add_assoc] using
        run_two_high (q + 2 * k) T (h k (by omega))

/-- On `00`, write the marker high cell and accept. -/
theorem run_two_blank (p : ℕ) (T : List Bool)
    (hlo : T.getD p false = false)
    (hhi : T.getD (p + 1) false = false) :
    run bridgeFinishMachine 2 ⟨scanLo, p, T⟩ =
      ⟨done, p + 1, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_scanLo, hlo,
    step_scanHi_blank hhi]

/-- A malformed `10` pair enters the rejecting halt state without a write. -/
theorem run_two_malformed (p : ℕ) (T : List Bool)
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = false) :
    run bridgeFinishMachine 2 ⟨scanLo, p, T⟩ =
      ⟨reject, p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_scanLo, hlo,
    step_scanHi_malformed hhi]

/-- Fully restored bridge tape in explicit block form. -/
theorem bridgeResS_all_eq (n a : ℕ) (suffix : List Bool) :
    bridgeResS n a a suffix =
      unaryD a ++ powBridge n ++
        List.replicate (2 * a) true ++ [false, false] ++ suffix := by
  unfold bridgeResS
  rw [Nat.sub_self]
  change List.replicate (2 * a) true ++
      ([] ++ ([false, true] ++
        (powBridge n ++
          (List.replicate (2 * a) true ++ ([false, false] ++ suffix))))) = _
  simp [unaryD_eq, List.append_assoc]

theorem bridgeResS_all_getD_high (n a i : ℕ) (suffix : List Bool)
    (hi : i < bridgePairs n + a) :
    (bridgeResS n a a suffix).getD
        (2 * a + 2 + 2 * i + 1) false = true := by
  rw [bridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [
    show 2 * a + 2 + 2 * i + 1 =
      (unaryD a).length + (2 * i + 1) by rw [unaryD_length]; omega,
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

theorem bridgeResS_all_getD_blank_lo (n a : ℕ) (suffix : List Bool) :
    (bridgeResS n a a suffix).getD
        (2 * a + 2 + 2 * (bridgePairs n + a)) false = false := by
  rw [bridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [
    show 2 * a + 2 + 2 * (bridgePairs n + a) =
      (unaryD a).length +
        ((powBridge n).length + (2 * a)) by
      rw [unaryD_length, powBridge_length_eq_pairs]
      ring,
    getD_append_left_length' _ _ rfl,
    getD_append_left_length' _ _ rfl,
    getD_append_length' _ _ List.length_replicate]
  rfl

theorem bridgeResS_all_getD_blank_hi (n a : ℕ) (suffix : List Bool) :
    (bridgeResS n a a suffix).getD
        (2 * a + 2 + 2 * (bridgePairs n + a) + 1) false = false := by
  rw [bridgeResS_all_eq]
  simp only [List.append_assoc]
  rw [
    show 2 * a + 2 + 2 * (bridgePairs n + a) + 1 =
      (unaryD a).length +
        ((powBridge n).length + (2 * a + 1)) by
      rw [unaryD_length, powBridge_length_eq_pairs]
      ring,
    getD_append_left_length' _ _ rfl,
    getD_append_left_length' _ _ rfl,
    List.getD_append_right (h := by rw [List.length_replicate]; omega),
    List.length_replicate]
  rw [show 2 * a + 1 - 2 * a = 1 by omega]
  rfl

/-- Exact bridge-aware finish clock. -/
def bridgeFinishClock (n a : ℕ) : ℕ :=
  2 * (bridgePairs n + a) + 2

/-- Traverse both power counters and the copied table, then create the final
table-counter marker.  The resulting tape is exactly the comparator layout. -/
theorem run_bridgeFinish_comparatorLayout (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    let a := table.length
    let q := pre.length + 2 * a + 2
    run bridgeFinishMachine (bridgeFinishClock n a)
      ⟨scanLo, q, pre ++ bridgeResS n a a payload⟩ =
      ⟨done,
        pre.length + 4 * a + 4 * (2 ^ n) + 7,
        pre ++ comparatorLayout n table payload⟩ := by
  intro a q
  have hhigh := run_high_pairs (pre ++ bridgeResS n a a payload)
    q (bridgePairs n + a) (fun i hi => by
      rw [show q + 2 * i + 1 = pre.length +
          (2 * a + 2 + 2 * i + 1) by simp [q]; omega,
        getD_append_left_length' _ _ rfl]
      exact bridgeResS_all_getD_high n a i payload hi)
  have hlo : (pre ++ bridgeResS n a a payload).getD
      (q + 2 * (bridgePairs n + a)) false = false := by
    rw [show q + 2 * (bridgePairs n + a) = pre.length +
        (2 * a + 2 + 2 * (bridgePairs n + a)) by simp [q]; omega,
      getD_append_left_length' _ _ rfl]
    exact bridgeResS_all_getD_blank_lo n a payload
  have hhi : (pre ++ bridgeResS n a a payload).getD
      (q + 2 * (bridgePairs n + a) + 1) false = false := by
    rw [show q + 2 * (bridgePairs n + a) + 1 = pre.length +
        (2 * a + 2 + 2 * (bridgePairs n + a) + 1) by simp [q]; omega,
      getD_append_left_length' _ _ rfl]
    exact bridgeResS_all_getD_blank_hi n a payload
  have hblank := run_two_blank
    (q + 2 * (bridgePairs n + a))
    (pre ++ bridgeResS n a a payload) hlo hhi
  rw [bridgeFinishClock, show 2 * (bridgePairs n + a) + 2 =
      2 * (bridgePairs n + a) + 2 by rfl,
    run_add, hhigh, hblank]
  have hpos : q + 2 * (bridgePairs n + a) + 1 =
      pre.length + 4 * a + 4 * (2 ^ n) + 7 := by
    simp [q, bridgePairs]
    ring
  rw [hpos]
  have hwrite : writeAt (pre ++ bridgeResS n a a payload)
      (pre.length + (4 * a + 4 * (2 ^ n) + 7)) true =
      pre ++ comparatorLayout n table payload := by
    rw [writeAt_append_right pre (bridgeResS n a a payload)
      pre.length (4 * a + 4 * (2 ^ n) + 7) true rfl (by
        rw [bridgeResS_length n a a payload (le_refl a)]
        omega), bridgeResS_finish_comparatorLayout]
  simpa [Nat.add_assoc] using hwrite

theorem bridgeFinish_comparatorLayout_halts (pre : List Bool)
    (n : ℕ) (table payload : List Bool) :
    let a := table.length
    let q := pre.length + 2 * a + 2
    bridgeFinishMachine.halt
      (run bridgeFinishMachine (bridgeFinishClock n a)
        ⟨scanLo, q, pre ++ bridgeResS n a a payload⟩).st = true := by
  intro a q
  rw [run_bridgeFinish_comparatorLayout]
  rfl

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine.run_high_pairs
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine.run_two_malformed
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine.run_bridgeFinish_comparatorLayout
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeFinishMachine.bridgeFinish_comparatorLayout_halts
