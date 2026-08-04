import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupSuffixRun

/-!
# Charged local lookup: INIT left-boundary safety

This file begins the concrete proof of `MasterLiteralLeftSafe` at the actual
phase level.  It proves the complete variable-length INIT segment is safe:
before the scan reaches `SEP`, every transition moves right or stays; at the
single INIT seam that moves left, the head is exactly the positive `SEP` high
position.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryInit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun

/-- The active INIT scanner cannot request a left move. -/
theorem masterM_INIT_active_not_left (sp : Fin 9) (c0 c1 b : Bool)
    (hsp : sp ≠ 2) :
    (masterM.δ (0, sp, c0, c1) b).2.2 ≠ 0 := by
  simp only [masterM]
  rw [if_neg hsp]
  simp only [inGroup, scanRightStep]
  by_cases h0 : sp = 0
  · simp [h0]
  · by_cases h1 : sp = 1
    · simp [h1]
      split <;> simp
    · fin_cases sp <;> simp_all

/-- The whole INIT phase is left-boundary safe, including its final left seam
from `SEP` high to `SEP` low. -/
theorem initPhase_leftSafe (T : List Bool) (v D : Nat)
    (h : RoundInv T v D) :
    ∀ i, i < 2 * (v + 1) + 2 + 1 →
      masterM.halt
        (run masterM i ⟨(0, 0, false, false), 0, T⟩).st = false →
      (masterM.δ
        (run masterM i ⟨(0, 0, false, false), 0, T⟩).st
        ((run masterM i ⟨(0, 0, false, false), 0, T⟩).tp.getD
          (run masterM i ⟨(0, 0, false, false), 0, T⟩).hd false)).2.2 = 0 →
      0 < (run masterM i ⟨(0, 0, false, false), 0, T⟩).hd := by
  have hns : ∀ k, k < v + 1 →
      (!(T.getD (2 * k) false) && T.getD (2 * k + 1) false) = false := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [show 2 * 0 + 1 = 1 from by norm_num, h.lsent]
      simp
    · rw [(h.ctr k (by omega) (by omega)).1,
        (h.ctr k (by omega) (by omega)).2]
      simp
  have hsep : (!(T.getD (2 * (v + 1)) false) &&
      T.getD (2 * (v + 1) + 1) false) = true := by
    rw [show 2 * (v + 1) = 2 * v + 2 by omega,
      show 2 * v + 2 + 1 = 2 * v + 3 by omega, h.seplo, h.sephi]
    decide
  intro i hi _ hmove
  by_cases hearly : i < 2 * (v + 1) + 2
  · have hmin : ∀ j < i,
        (run scanRightSep j ⟨(0, false), 0, T⟩).st.1 ≠ 2 := by
      intro j hj
      exact scanRightSep_no_early_halt
        (P := 0) (tape := T) (m := v + 1) (st := false)
        (by simpa using hns) j (by omega)
    have hsim := sim_run_INIT i ⟨(0, false), 0, T⟩ hmin
    have hphase := scanRightSep_no_early_halt
      (P := 0) (tape := T) (m := v + 1) (st := false)
      (by simpa using hns) i hearly
    have hphase' : Fin.castLE (by omega)
        (run scanRightSep i ⟨(0, false), 0, T⟩).st.1 ≠ (2 : Fin 9) := by
      intro heq
      apply hphase
      apply Fin.ext
      exact congrArg (fun z : Fin 9 => z.val) heq
    rw [show (⟨(0, 0, false, false), 0, T⟩ : Cfg masterM) =
        embedScanR 0 ⟨(0, false), 0, T⟩ from rfl, hsim] at hmove ⊢
    exact absurd hmove
      (masterM_INIT_active_not_left _ _ _ _ hphase')
  · have hi : i = 2 * (v + 1) + 2 := by omega
    subst i
    have hmin : ∀ j < 2 * (v + 1) + 2,
        (run scanRightSep j ⟨(0, false), 0, T⟩).st.1 ≠ 2 :=
      scanRightSep_no_early_halt
        (P := 0) (tape := T) (m := v + 1) (st := false)
        (by simpa using hns)
    rw [show (⟨(0, 0, false, false), 0, T⟩ : Cfg masterM) =
        embedScanR 0 ⟨(0, false), 0, T⟩ from rfl,
      sim_run_INIT (2 * (v + 1) + 2) ⟨(0, false), 0, T⟩ hmin,
      run_scan_right_halt T 0 false (v + 1)
        (by simpa using hns) (by simpa using hsep)]
    simp only [embedScanR, Nat.zero_add]
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryInit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryInit.masterM_INIT_active_not_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryInit.initPhase_leftSafe
