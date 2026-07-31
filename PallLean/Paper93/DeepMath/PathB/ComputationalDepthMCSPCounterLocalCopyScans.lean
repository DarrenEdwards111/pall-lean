import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyLift

/-!
# MCSP verifier: prefix-lifted copy scan passes

This file instantiates the generic prefix transport theorem on the two
reset-free scans repeated in every unary-copy round:

* the find pass skips processed `10` pairs from local home;
* the rightward seek crosses pairs whose high cell is true.

Both are executions of the real `localCopyMachine`, preserve the arbitrary
live prefix and `00` delimiter, retain the existing exact clocks, and end at
the same relative copy states and positions as the original verified scans.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterCopyScratchMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyLift

theorem step_c0_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} :
    step localCopyMachine
      (liftCopyCfg pre ⟨(0, s), p, T⟩) =
      liftCopyCfg pre ⟨(1, T.getD p false), p + 1, T⟩ := by
  have h := step_localCopy_lift pre
    (⟨(0, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
  rw [h, step_c0]

theorem step_c1_skip_local (pre : List Bool) {p : ℕ}
    {T : List Bool} (hread : T.getD p false = false) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(1, true), p, T⟩) =
      liftCopyCfg pre ⟨(0, true), p + 1, T⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(1, true), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
  rw [h, step_c1_skip hread]

theorem step_c2_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} :
    step localCopyMachine
      (liftCopyCfg pre ⟨(2, s), p, T⟩) =
      liftCopyCfg pre ⟨(3, T.getD p false), p + 1, T⟩ := by
  have h := step_localCopy_lift pre
    (⟨(2, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
    (by simp [copyMachine])
  rw [h, step_c2]

theorem step_c3_skip_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} (hread : T.getD p false = true) :
    step localCopyMachine
      (liftCopyCfg pre ⟨(3, s), p, T⟩) =
      liftCopyCfg pre ⟨(2, true), p + 1, T⟩ := by
  have hread' := hread
  rw [List.getD_eq_getElem?_getD] at hread'
  have h := step_localCopy_lift pre
    (⟨(3, s), p, T⟩ : Cfg copyMachine)
    (by simp [copyMachine])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
    (by simp [copyMachine, hread'])
  rw [h, step_c3_skip hread]

/-- One processed `10` pair is skipped under the arbitrary prefix. -/
theorem run_two_skipF_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool}
    (hlo : T.getD p false = true)
    (hhi : T.getD (p + 1) false = false) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(0, s), p, T⟩) =
      liftCopyCfg pre ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0_local, hlo,
    step_c1_skip_local pre hhi]

/-- One pair with true high cell is crossed under the arbitrary prefix. -/
theorem run_two_seekE_local (pre : List Bool) {s : Bool} {p : ℕ}
    {T : List Bool} (hhi : T.getD (p + 1) false = true) :
    run localCopyMachine 2
      (liftCopyCfg pre ⟨(2, s), p, T⟩) =
      liftCopyCfg pre ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c2_local,
    step_c3_skip_local pre hhi]

/-- Prefix-lifted find invariant: skip `k` processed pairs. -/
theorem run_findSkip_local (pre T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i) false = true ∧
        T.getD (q + 2 * i + 1) false = false) :
    run localCopyMachine (2 * k)
      (liftCopyCfg pre ⟨(0, s), q, T⟩) =
      liftCopyCfg pre
        ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        run_add,
        ih (fun i hi => h i (by omega))]
      simpa [Nat.succ_ne_zero, Nat.mul_succ, Nat.add_assoc] using
        run_two_skipF_local (pre := pre)
          (s := if k = 0 then s else true)
          (p := q + 2 * k) hk.1 hk.2

/-- Prefix-lifted rightward seek invariant. -/
theorem run_seekE_local (pre T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k →
      T.getD (q + 2 * i + 1) false = true) :
    run localCopyMachine (2 * k)
      (liftCopyCfg pre ⟨(2, s), q, T⟩) =
      liftCopyCfg pre
        ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        run_add,
        ih (fun i hi => h i (by omega))]
      simpa [Nat.succ_ne_zero, Nat.mul_succ, Nat.add_assoc] using
        run_two_seekE_local (pre := pre)
          (s := if k = 0 then s else true)
          (p := q + 2 * k) (h k (by omega))

/-! ## Instantiation on the evolving scratch-copy tapes -/

/-- The actual per-round find pass under an arbitrary local prefix. -/
theorem run_findSkip_cpyS_local (pre suffix : List Bool)
    (n j : ℕ) (hj : j ≤ n) (s : Bool) :
    run localCopyMachine (2 * j)
      (liftCopyCfg pre ⟨(0, s), 0, cpyS n j j suffix⟩) =
      liftCopyCfg pre
        ⟨(0, if j = 0 then s else true), 2 * j,
          cpyS n j j suffix⟩ := by
  simpa using run_findSkip_local pre (cpyS n j j suffix) 0 j s
    (fun i hi =>
      ⟨(by simpa using
          (cpyS_getD_Amark_lo n j j i suffix hj hj hi)),
       (by simpa using
          (cpyS_getD_Amark_hi n j j i suffix hj hj hi))⟩)

/-- The actual per-round seek from the newly marked source pair to the blank
target end, still under the arbitrary local prefix. -/
theorem run_seekE_cpyS_local (pre suffix : List Bool)
    (n j : ℕ) (hj : j < n) :
    run localCopyMachine (2 * n)
      (liftCopyCfg pre
        ⟨(2, true), 2 * j + 2, cpyS n (j + 1) j suffix⟩) =
      liftCopyCfg pre
        ⟨(2, true), 2 * n + 2 * j + 2,
          cpyS n (j + 1) j suffix⟩ := by
  have h := run_seekE_local pre (cpyS n (j + 1) j suffix)
    (2 * j + 2) n true (fun i hi => by
      rcases Nat.lt_trichotomy i (n - j - 1) with h | h | h
      · exact cpyS_getD_Adata n (j + 1) j
          (2 * j + 2 + 2 * i + 1) suffix (by omega) (by omega)
          (by omega) (by omega)
      · rw [show 2 * j + 2 + 2 * i + 1 = 2 * n + 1 by omega]
        exact cpyS_getD_marker_hi n (j + 1) j suffix
          (by omega) (by omega)
      · exact cpyS_getD_C n (j + 1) j
          (2 * j + 2 + 2 * i + 1) suffix (by omega) (by omega)
          (by omega) (by omega))
  have hn : n ≠ 0 := by omega
  simp [hn] at h
  rw [show 2 * j + 2 + 2 * n = 2 * n + 2 * j + 2 by ring] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans.run_findSkip_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans.run_seekE_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyScans.run_seekE_cpyS_local
