import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupLeftBoundaryInit

/-!
# Charged local lookup: terminal left-boundary safety

The fixed seven-step empty-counter branch is proved safe compositionally from
its verified phase transitions.  This file also introduces the reusable
`LeftSafeRun` concatenation calculus needed for the repeated round body.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinLoopEnds

/-- No live left-moving transition among the first `n` steps crosses relative
head zero. -/
def LeftSafeRun (M : Machine) (c : Cfg M) (n : Nat) : Prop :=
  ∀ i, i < n → M.halt (run M i c).st = false →
    (M.δ (run M i c).st
      ((run M i c).tp.getD (run M i c).hd false)).2.2 = 0 →
    0 < (run M i c).hd

theorem leftSafeRun_add {M : Machine} {c : Cfg M} {a b : Nat}
    (ha : LeftSafeRun M c a)
    (hb : LeftSafeRun M (run M a c) b) :
    LeftSafeRun M c (a + b) := by
  intro i hi hhalt hmove
  by_cases hia : i < a
  · exact ha i hia hhalt hmove
  · have hirun : run M i c = run M (i - a) (run M a c) := by
      rw [← run_add]
      congr 2
      omega
    rw [hirun] at hhalt hmove ⊢
    exact hb (i - a) (by omega) hhalt hmove

theorem leftSafeRun_one_of_positive {M : Machine} {c : Cfg M}
    (hpos : 0 < c.hd) : LeftSafeRun M c 1 := by
  intro i hi _ _
  have : i = 0 := by omega
  subst i
  simpa only [run_zero] using hpos

theorem leftSafeRun_one_of_not_left {M : Machine} {c : Cfg M}
    (hnl : (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 0) :
    LeftSafeRun M c 1 := by
  intro i hi _ hmove
  have : i = 0 := by omega
  subst i
  simp only [run_zero] at hmove
  exact absurd hmove hnl

/-! ## Exact terminal blocks -/

theorem loopCheck_empty_leftSafe {s : Nat} {T : List Bool}
    (hs : 1 ≤ s) :
    LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩ 2 := by
  apply leftSafeRun_add (a := 1) (b := 1)
    (leftSafeRun_one_of_positive (by simpa using hs))
  have hstep : run masterM 1 ⟨(1, 0, false, false), s, T⟩ =
      ⟨(1, 1, false, false), s - 1, T⟩ := by
    rw [run_one]
    simp [step, masterM, loopStep, inGroup, moveHead]
  rw [hstep]
  apply leftSafeRun_one_of_not_left
  simp [masterM, loopStep, inGroup]

theorem loopToResult_empty_leftSafe {s : Nat} {T : List Bool}
    : LeftSafeRun masterM ⟨(1, 2, false, false), s - 1, T⟩ 1 := by
  apply leftSafeRun_one_of_not_left
  simp [masterM, seam]

theorem resultRead_leftSafe {s : Nat} {T : List Bool} :
    LeftSafeRun masterM ⟨(8, 0, false, false), s, T⟩ 3 := by
  have e1 : run masterM 1 ⟨(8, 0, false, false), s, T⟩ =
      ⟨(8, 1, false, false), s + 1, T⟩ := by
    rw [run_one]
    simp [step, masterM, readResStep, inGroup, moveHead]
  have e2 : run masterM 2 ⟨(8, 0, false, false), s, T⟩ =
      ⟨(8, 2, false, false), s + 2, T⟩ := by
    rw [show 2 = 1 + 1 from rfl, run_add, e1, run_one]
    simp [step, masterM, readResStep, inGroup, moveHead]
  apply leftSafeRun_add (a := 1) (b := 2)
    (leftSafeRun_one_of_not_left (by simp [masterM, readResStep, inGroup]))
  rw [e1]
  apply leftSafeRun_add (a := 1) (b := 1)
    (leftSafeRun_one_of_not_left (by simp [masterM, readResStep, inGroup]))
  rw [show run masterM 1 ⟨(8, 1, false, false), s + 1, T⟩ =
      ⟨(8, 2, false, false), s + 2, T⟩ by
        rw [run_one]
        simp [step, masterM, readResStep, inGroup, moveHead]]
  apply leftSafeRun_one_of_not_left
  simp [masterM, readResStep, inGroup]

theorem resultToHalt_leftSafe {s : Nat} {T : List Bool} {b : Bool} :
    LeftSafeRun masterM ⟨(8, 3, b, false), s, T⟩ 1 := by
  apply leftSafeRun_one_of_not_left
  simp [masterM]

/-- The entire seven-step terminal read is boundary-safe. -/
theorem tailRead_leftSafe {s : Nat} {T : List Bool} (hs : 1 ≤ s)
    (hdone : T.getD (s - 1) false = false) :
    LeftSafeRun masterM ⟨(1, 0, false, false), s, T⟩ 7 := by
  have e1 : run masterM 2 ⟨(1, 0, false, false), s, T⟩ =
      ⟨(1, 2, false, false), s - 1, T⟩ := by
    have hmin : ∀ i < 2,
        (run loopCtrl i ⟨(0, false), s, T⟩).st.1 ≠ 2 := by
      intro i hi
      interval_cases i
      · simp
      · rw [show (1 : Nat) = 0 + 1 from rfl, run_succ, run_zero,
          loopCtrl_step_left]
        simp
    rw [show (⟨(1, 0, false, false), s, T⟩ : Cfg masterM) =
        embedLoop 1 ⟨(0, false), s, T⟩ from rfl,
      sim_run_LOOPCHK 2 ⟨(0, false), s, T⟩ hmin, run_loopCtrl, hdone]
    rfl
  have e2 : run masterM 1 ⟨(1, 2, false, false), s - 1, T⟩ =
      ⟨(8, 0, false, false), s, T⟩ := by
    rw [run_one, seam_LOOPCHK_false]
    rw [Nat.sub_add_cancel hs]
  have e3 : run masterM 3 ⟨(8, 0, false, false), s, T⟩ =
      ⟨(8, 3, T.getD (s + 2) false, false), s + 2, T⟩ := by
    have hmin : ∀ i < 3,
        (run readRes i ⟨(0, false), s, T⟩).st.1 ≠ 3 := by
      intro i hi
      interval_cases i
      · simp
      · rw [show (1 : Nat) = 0 + 1 from rfl, run_succ, run_zero,
          readRes_step0]
        simp
      · rw [show (2 : Nat) = 1 + 1 from rfl, run_succ,
          show (1 : Nat) = 0 + 1 from rfl, run_succ, run_zero,
          readRes_step0, readRes_step1]
        simp
    rw [show (⟨(8, 0, false, false), s, T⟩ : Cfg masterM) =
        embedRes 8 ⟨(0, false), s, T⟩ from rfl,
      sim_run_RRES 3 ⟨(0, false), s, T⟩ hmin, run_readRes]
    rfl
  apply leftSafeRun_add (a := 2) (b := 5) (loopCheck_empty_leftSafe hs)
  rw [e1]
  apply leftSafeRun_add (a := 1) (b := 4)
    loopToResult_empty_leftSafe
  rw [e2]
  apply leftSafeRun_add (a := 3) (b := 1) resultRead_leftSafe
  rw [e3]
  exact resultToHalt_leftSafe

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal.leftSafeRun_add
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal.loopCheck_empty_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal.resultRead_leftSafe
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal.tailRead_leftSafe
