import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareCopyMachine

/-!
# MCSP verifier: generic run lifts into the gap-aware copy controller

Only two transitions of `gapCopyMachine` are new: crossing the staged `00`
while seeking right and crossing it while returning left after growth.  This
file proves that every other reset-free copy step and every ordinary local-home
step is simulated exactly.  Whole safe runs lift by induction, so the existing
find, mark, seek, grow, restore, and home invariants can be transported without
re-proving their unchanged finite-control behavior.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine
open LocalHomeState
open GapCopyState

def liftGapCopyCfg (crossed : Bool) (c : Cfg copyMachine) :
    Cfg gapCopyMachine :=
  ⟨.copy c.st crossed, c.hd, c.tp⟩

def liftGapHomeCfg (resume : copyMachine.State) (skipGap : Bool)
    (c : Cfg localHomeMachine) : Cfg gapCopyMachine :=
  ⟨.home resume skipGap c.st, c.hd, c.tp⟩

/-- Any running, non-reset copy step outside the unique uncrossed `00` case
is simulated exactly, including its optional write and head motion. -/
theorem step_gapCopy_lift (crossed : Bool) (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hspecial : ¬ (c.st.1 = 3 ∧ c.st.2 = false ∧
      c.tp.getD c.hd false = false ∧ crossed = false))
    (hreset : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 ≠ 3) :
    step gapCopyMachine (liftGapCopyCfg crossed c) =
      liftGapCopyCfg crossed (step copyMachine c) := by
  unfold liftGapCopyCfg
  simp only [step, gapCopyMachine, hhalt, Bool.false_eq_true, if_false]
  rw [if_neg hspecial, if_neg hreset]

/-- A whole reset-free, non-special copy pass transports unchanged. -/
theorem run_gapCopy_lift (crossed : Bool) (c : Cfg copyMachine) (t : ℕ)
    (hhalt : ∀ i, i < t →
      copyMachine.halt (run copyMachine i c).st = false)
    (hspecial : ∀ i, i < t → ¬
      ((run copyMachine i c).st.1 = 3 ∧
       (run copyMachine i c).st.2 = false ∧
       (run copyMachine i c).tp.getD
          (run copyMachine i c).hd false = false ∧
       crossed = false))
    (hreset : ∀ i, i < t →
      (copyMachine.δ (run copyMachine i c).st
        ((run copyMachine i c).tp.getD
          (run copyMachine i c).hd false)).2.2 ≠ 3) :
    run gapCopyMachine t (liftGapCopyCfg crossed c) =
      liftGapCopyCfg crossed (run copyMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ,
        ih
          (fun i hi => hhalt i (by omega))
          (fun i hi => hspecial i (by omega))
          (fun i hi => hreset i (by omega)),
        step_gapCopy_lift crossed (run copyMachine t c)
          (hhalt t (by omega))
          (hspecial t (by omega))
          (hreset t (by omega)),
        ← run_succ]

/-- Original reset transitions keep their write and head position, remember
the original resume state, and enable internal-gap skipping exactly for the
post-growth resume state `0`. -/
theorem step_gapCopy_reset (crossed : Bool) (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hspecial : ¬ (c.st.1 = 3 ∧ c.st.2 = false ∧
      c.tp.getD c.hd false = false ∧ crossed = false))
    (hreset : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 3) :
    step gapCopyMachine (liftGapCopyCfg crossed c) =
      ⟨.home
          (copyMachine.δ c.st (c.tp.getD c.hd false)).1
          (decide ((copyMachine.δ c.st
            (c.tp.getD c.hd false)).1.1 = 0)) scanHi,
        c.hd,
        match (copyMachine.δ c.st
          (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w⟩ := by
  unfold liftGapCopyCfg
  simp only [step, gapCopyMachine, hhalt, Bool.false_eq_true, if_false]
  rw [if_neg hspecial, if_pos hreset]
  simp [moveHead]
  rfl

theorem step_gapCopy_reset_to_growth (crossed : Bool)
    (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hspecial : ¬ (c.st.1 = 3 ∧ c.st.2 = false ∧
      c.tp.getD c.hd false = false ∧ crossed = false))
    (hreset : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 3)
    (hresume : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).1.1 = 0) :
    step gapCopyMachine (liftGapCopyCfg crossed c) =
      ⟨.home
          (copyMachine.δ c.st (c.tp.getD c.hd false)).1 true scanHi,
        c.hd,
        match (copyMachine.δ c.st
          (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w⟩ := by
  rw [step_gapCopy_reset crossed c hhalt hspecial hreset]
  have hd : decide ((copyMachine.δ c.st
      (c.tp.getD c.hd false)).1.1 = 0) = true := by
    rw [decide_eq_true_eq]
    exact hresume
  rw [hd]

theorem step_gapCopy_reset_to_restore (crossed : Bool)
    (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hspecial : ¬ (c.st.1 = 3 ∧ c.st.2 = false ∧
      c.tp.getD c.hd false = false ∧ crossed = false))
    (hreset : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 3)
    (hresume : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).1.1 ≠ 0) :
    step gapCopyMachine (liftGapCopyCfg crossed c) =
      ⟨.home
          (copyMachine.δ c.st (c.tp.getD c.hd false)).1 false scanHi,
        c.hd,
        match (copyMachine.δ c.st
          (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w⟩ := by
  rw [step_gapCopy_reset crossed c hhalt hspecial hreset]
  have hd : decide ((copyMachine.δ c.st
      (c.tp.getD c.hd false)).1.1 = 0) = false := by
    rw [decide_eq_false_iff_not]
    exact hresume
  rw [hd]

/-- Any ordinary local-home step transports exactly when it is neither the
special internal-gap low cell nor the completed-home control state. -/
theorem step_gapHome_lift (resume : copyMachine.State) (skipGap : Bool)
    (c : Cfg localHomeMachine)
    (hspecial : ¬ (c.st = probeLo ∧
      c.tp.getD c.hd false = false ∧ skipGap = true))
    (hdone : c.st ≠ done) :
    step gapCopyMachine (liftGapHomeCfg resume skipGap c) =
      liftGapHomeCfg resume skipGap (step localHomeMachine c) := by
  rcases c with ⟨s, p, T⟩
  unfold liftGapHomeCfg
  simp only [step, gapCopyMachine, localHomeMachine]
  rw [if_neg hspecial, if_neg hdone]
  rfl

/-- Whole ordinary local-home segments lift while preserving the skip flag. -/
theorem run_gapHome_lift (resume : copyMachine.State) (skipGap : Bool)
    (c : Cfg localHomeMachine) (t : ℕ)
    (hspecial : ∀ i, i < t → ¬
      ((run localHomeMachine i c).st = probeLo ∧
       (run localHomeMachine i c).tp.getD
          (run localHomeMachine i c).hd false = false ∧
       skipGap = true))
    (hdone : ∀ i, i < t →
      (run localHomeMachine i c).st ≠ done) :
    run gapCopyMachine t (liftGapHomeCfg resume skipGap c) =
      liftGapHomeCfg resume skipGap (run localHomeMachine t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ,
        ih
          (fun i hi => hspecial i (by omega))
          (fun i hi => hdone i (by omega)),
        step_gapHome_lift resume skipGap (run localHomeMachine t c)
          (hspecial t (by omega)) (hdone t (by omega)),
        ← run_succ]

/-- Completed true-home control resumes copying, clears both one-round flags,
and leaves the head and tape unchanged. -/
theorem step_gapHome_resume (resume : copyMachine.State)
    (skipGap : Bool) (p : ℕ) (T : List Bool) :
    step gapCopyMachine ⟨.home resume skipGap done, p, T⟩ =
      ⟨.copy resume false, p, T⟩ := by
  simp [step, gapCopyMachine, moveHead]

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift.step_gapCopy_lift
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift.run_gapCopy_lift
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift.step_gapCopy_reset
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift.run_gapHome_lift
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyLift.step_gapHome_resume
