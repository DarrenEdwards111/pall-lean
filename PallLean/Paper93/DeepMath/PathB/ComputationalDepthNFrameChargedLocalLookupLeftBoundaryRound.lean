import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryRoundPhases

/-!
# Charged local lookup: one complete live round is left-boundary safe

The four variable-length phase theorems are composed with every fixed seam
and repositioning step.  The result has the same raw tape interface and exact
clock as `round_full`, so the round invariant can consume it directly.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinScanLeftSep
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundBody
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRoundPhases

theorem repa_leftSafe {c0 c1 : Bool} {p : Nat} {T : List Bool} :
    LeftSafeRun masterM ⟨(2, 0, c0, c1), p, T⟩ 2 := by
  apply leftSafeRun_add (a := 1) (b := 1)
    (leftSafeRun_one_of_not_left (by simp [masterM]))
  have e : run masterM 1 ⟨(2, 0, c0, c1), p, T⟩ =
      ⟨(2, 1, c0, c1), p + 1, T⟩ := by
    rw [run_one]
    simp [step, masterM, seam, moveHead]
  rw [e]
  apply leftSafeRun_one_of_not_left
  simp [masterM, seam]

theorem round_open_leftSafe {s K : Nat} {T : List Bool} (hs : 1 ≤ s)
    (hcnt : T.getD (s - 1) false = true)
    (hnr : ∀ i < K,
      (T.getD (s + 2 + 2 * i + 2) false && !(T.getD (s + 2 + 2 * i + 3) false)) = false)
    (hrend : (T.getD (s + 2 + 2 * K + 2) false &&
      !(T.getD (s + 2 + 2 * K + 3) false)) = true) :
    LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩
      (2 + 1 + 2 + (8 * K + 8) + 1) := by
  have hmin : ∀ i < 2,
      (run loopCtrl i ⟨(0, false), s, T⟩).st.1 ≠ 2 := by
    intro i hi
    interval_cases i
    · simp
    · rw [show (1 : Nat) = 0 + 1 from rfl, run_succ, run_zero,
        loopCtrl_step_left]
      simp
  have e2 : run masterM 2 ⟨(1, 0, false, false), s, T⟩ =
      ⟨(1, 2, true, false), s - 1, T⟩ := by
    rw [show (⟨(1, 0, false, false), s, T⟩ : Cfg masterM) =
        embedLoop 1 ⟨(0, false), s, T⟩ from rfl,
      sim_run_LOOPCHK 2 ⟨(0, false), s, T⟩ hmin, run_loopCtrl, hcnt]
    rfl
  have e3 : run masterM (2 + 1) ⟨(1, 0, false, false), s, T⟩ =
      ⟨(2, 0, false, false), s, T⟩ := by
    rw [run_add, e2, run_one, seam_LOOPCHK_true, Nat.sub_add_cancel hs]
  have e5 : run masterM (2 + 1 + 2) ⟨(1, 0, false, false), s, T⟩ =
      ⟨(3, 0, false, false), s + 2, T⟩ := by
    rw [run_add, e3, repa_run]
  have eSHA : run masterM (8 * K + 8) ⟨(3, 0, false, false), s + 2, T⟩ =
      ⟨(3, 8, T.getD (s + 2 + 2 * K + 2) false,
          T.getD (s + 2 + 2 * K + 3) false),
        s + 2 + 2 * K + 1, rsTape T (s + 2) (K + 1)⟩ := by
    rw [show (⟨(3, 0, false, false), s + 2, T⟩ : Cfg masterM) =
        embedRend 3 ⟨(0, false, false), s + 2, T⟩ from rfl,
      sim_run_SHA (8 * K + 8) ⟨(0, false, false), s + 2, T⟩
        (rendShift_no_early_halt hnr),
      run_shift_halt T (s + 2) false false K hnr hrend]
    rfl
  have h2 := loopCheck_empty_leftSafe (T := T) hs
  have h3 : LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩ (2 + 1) := by
    apply leftSafeRun_add h2
    rw [e2]
    exact leftSafeRun_one_of_not_left (by simp [masterM, seam])
  have h5 : LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩ (2 + 1 + 2) := by
    apply leftSafeRun_add h3
    rw [e3]
    exact repa_leftSafe
  have hS : LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩
      (2 + 1 + 2 + (8 * K + 8)) := by
    apply leftSafeRun_add h5
    rw [e5]
    exact masterSHA_leftSafe (by omega) hnr
  apply leftSafeRun_add hS
  rw [run_add, e5, eSHA]
  exact leftSafeRun_one_of_not_left (by simp [masterM, seam])

theorem round_close_leftSafe {s P1 m1 KB P2 : Nat} {TA TB : List Bool}
    (hs4 : 4 ≤ s)
    (hP1 : P1 = s + 2 * m1 + 1)
    (hns1 : ∀ i < m1,
      (!(TA.getD (P1 - 2 * i - 1) false) && TA.getD (P1 - 2 * i) false) = false)
    (hsep1 : (!(TA.getD (P1 - 2 * m1 - 1) false) &&
      TA.getD (P1 - 2 * m1) false) = true)
    (hnrB : ∀ i < KB,
      (TA.getD (s - 2 + 2 * i + 2) false && !(TA.getD (s - 2 + 2 * i + 3) false)) = false)
    (hrendB : (TA.getD (s - 2 + 2 * KB + 2) false &&
      !(TA.getD (s - 2 + 2 * KB + 3) false)) = true)
    (hTB : TB = rsTape TA (s - 2) (KB + 1))
    (hP2 : P2 = s - 2 + 2 * KB + 1)
    (hns2 : ∀ i < KB,
      (!(TB.getD (P2 - 2 * i - 1) false) && TB.getD (P2 - 2 * i) false) = false)
    (hsep2 : (!(TB.getD (P2 - 2 * KB - 1) false) &&
      TB.getD (P2 - 2 * KB) false) = true) :
    LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩
      ((2 * m1 + 2) + 1 + 1 + (8 * KB + 8) + 1 + (2 * KB + 2) + 1) := by
  have hh1 : P1 - 2 * m1 - 1 = s := by omega
  have hh1b : P1 - 2 * m1 = s + 1 := by omega
  have hh2 : P2 - 2 * KB - 1 = s - 2 := by omega
  have hh2b : P2 - 2 * KB = s - 1 := by omega
  have eR1 : run masterM (2 * m1 + 2) ⟨(4, 0, false, false), P1, TA⟩ =
      ⟨(4, 2, TA.getD (s + 1) false, false), s, TA⟩ := by
    rw [show (⟨(4, 0, false, false), P1, TA⟩ : Cfg masterM) =
        embedScanL 4 ⟨(0, false), P1, TA⟩ from rfl,
      sim_run_RANCH1 (2 * m1 + 2) ⟨(0, false), P1, TA⟩
        (scanLeftSep_no_early_halt hns1),
      CookLevinScanLeftSep.run_scan_left_halt TA P1 false m1 hns1 hsep1,
      hh1, hh1b]
    rfl
  have e1 : run masterM (2 * m1 + 2 + 1) ⟨(4, 0, false, false), P1, TA⟩ =
      ⟨(5, 0, false, false), s - 1, TA⟩ := by
    rw [run_add, eR1, run_one, seam_RANCH1]
  have e2 : run masterM (2 * m1 + 2 + 1 + 1) ⟨(4, 0, false, false), P1, TA⟩ =
      ⟨(6, 0, false, false), s - 2, TA⟩ := by
    rw [run_add, e1, run_one, repb_step, Nat.sub_sub]
  have eSHB : run masterM (8 * KB + 8) ⟨(6, 0, false, false), s - 2, TA⟩ =
      ⟨(6, 8, TA.getD (s - 2 + 2 * KB + 2) false,
          TA.getD (s - 2 + 2 * KB + 3) false),
        s - 2 + 2 * KB + 1, TB⟩ := by
    rw [show (⟨(6, 0, false, false), s - 2, TA⟩ : Cfg masterM) =
        embedRend 6 ⟨(0, false, false), s - 2, TA⟩ from rfl,
      sim_run_SHB (8 * KB + 8) ⟨(0, false, false), s - 2, TA⟩
        (rendShift_no_early_halt hnrB),
      run_shift_halt TA (s - 2) false false KB hnrB hrendB, ← hTB]
    rfl
  have e3 : run masterM (2 * m1 + 2 + 1 + 1 + (8 * KB + 8))
      ⟨(4, 0, false, false), P1, TA⟩ =
      ⟨(6, 8, TA.getD (s - 2 + 2 * KB + 2) false,
          TA.getD (s - 2 + 2 * KB + 3) false),
        s - 2 + 2 * KB + 1, TB⟩ := by
    rw [run_add, e2, eSHB]
  have e4 : run masterM (2 * m1 + 2 + 1 + 1 + (8 * KB + 8) + 1)
      ⟨(4, 0, false, false), P1, TA⟩ =
      ⟨(7, 0, false, false), P2, TB⟩ := by
    rw [run_add, e3, run_one, seam_SHB, hP2]
  have eR2 : run masterM (2 * KB + 2) ⟨(7, 0, false, false), P2, TB⟩ =
      ⟨(7, 2, TB.getD (s - 1) false, false), s - 2, TB⟩ := by
    rw [show (⟨(7, 0, false, false), P2, TB⟩ : Cfg masterM) =
        embedScanL 7 ⟨(0, false), P2, TB⟩ from rfl,
      sim_run_RANCH2 (2 * KB + 2) ⟨(0, false), P2, TB⟩
        (scanLeftSep_no_early_halt hns2),
      CookLevinScanLeftSep.run_scan_left_halt TB P2 false KB hns2 hsep2,
      hh2, hh2b]
    rfl
  have hR1 := masterRANCH1_leftSafe (T := TA) (st := false)
    (show 2 * m1 + 2 ≤ P1 by rw [hP1]; omega) hns1
  have h1 : LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩ (2 * m1 + 2 + 1) := by
    apply leftSafeRun_add hR1
    rw [eR1]
    exact leftSafeRun_one_of_positive (show 0 < s by omega)
  have h2 : LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩ (2 * m1 + 2 + 1 + 1) := by
    apply leftSafeRun_add h1
    rw [e1]
    exact leftSafeRun_one_of_positive (show 0 < s - 1 by omega)
  have hS : LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩
      (2 * m1 + 2 + 1 + 1 + (8 * KB + 8)) := by
    apply leftSafeRun_add h2
    rw [e2]
    exact masterSHB_leftSafe (by omega) hnrB
  have h4 : LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩
      (2 * m1 + 2 + 1 + 1 + (8 * KB + 8) + 1) := by
    apply leftSafeRun_add hS
    rw [e3]
    exact leftSafeRun_one_of_not_left (by simp [masterM, seam])
  have hR : LeftSafeRun masterM ⟨(4, 0, false, false), P1, TA⟩
      (2 * m1 + 2 + 1 + 1 + (8 * KB + 8) + 1 + (2 * KB + 2)) := by
    apply leftSafeRun_add h4
    rw [e4]
    exact masterRANCH2_leftSafe (show 2 * KB + 2 ≤ P2 by omega) hns2
  apply leftSafeRun_add hR
  rw [run_add, e4, eR2]
  exact leftSafeRun_one_of_not_left (by simp [masterM, seam])

theorem round_full_leftSafe {s K KB P2 : Nat} {T TA TB : List Bool}
    (hs4 : 4 ≤ s)
    (hcnt : T.getD (s - 1) false = true)
    (hnr : ∀ i < K,
      (T.getD (s + 2 + 2 * i + 2) false && !(T.getD (s + 2 + 2 * i + 3) false)) = false)
    (hrend : (T.getD (s + 2 + 2 * K + 2) false && !(T.getD (s + 2 + 2 * K + 3) false)) = true)
    (hTA : TA = rsTape T (s + 2) (K + 1))
    (hns1 : ∀ i < K + 1,
      (!(TA.getD (s + 2 + 2 * K + 1 - 2 * i - 1) false) &&
        TA.getD (s + 2 + 2 * K + 1 - 2 * i) false) = false)
    (hsep1 : (!(TA.getD (s + 2 + 2 * K + 1 - 2 * (K + 1) - 1) false) &&
      TA.getD (s + 2 + 2 * K + 1 - 2 * (K + 1)) false) = true)
    (hnrB : ∀ i < KB,
      (TA.getD (s - 2 + 2 * i + 2) false && !(TA.getD (s - 2 + 2 * i + 3) false)) = false)
    (hrendB : (TA.getD (s - 2 + 2 * KB + 2) false && !(TA.getD (s - 2 + 2 * KB + 3) false)) = true)
    (hTB : TB = rsTape TA (s - 2) (KB + 1))
    (hP2 : P2 = s - 2 + 2 * KB + 1)
    (hns2 : ∀ i < KB,
      (!(TB.getD (P2 - 2 * i - 1) false) && TB.getD (P2 - 2 * i) false) = false)
    (hsep2 : (!(TB.getD (P2 - 2 * KB - 1) false) && TB.getD (P2 - 2 * KB) false) = true) :
    LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩
      ((2 + 1 + 2 + (8 * K + 8) + 1) +
        ((2 * (K + 1) + 2) + 1 + 1 + (8 * KB + 8) + 1 + (2 * KB + 2) + 1)) := by
  apply leftSafeRun_add (round_open_leftSafe (by omega) hcnt hnr hrend)
  rw [round_open (by omega) hcnt hnr hrend, ← hTA]
  exact round_close_leftSafe hs4 (by omega) hns1 hsep1 hnrB hrendB hTB hP2 hns2 hsep2

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound.round_open_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound.round_close_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryRound.round_full_leftSafe
