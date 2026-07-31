import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerBridgeStageMachine

/-!
# MCSP verifier: gap-aware local bridge-copy controller

Physical duplication of the power counter leaves one doubled `00` local-home
pair between the table source and the power bridge.  An ordinary copy seek
would mistake that pair for its target scratch, and an ordinary local reset
from the copied target would mistake it for the table counter's home.

This file defines the fixed finite-control correction.  During a rightward
copy seek it skips the first `00` pair exactly once; later `00` is still the
real target.  During the post-growth leftward reset it skips the internal gap
exactly once; the next `00` remains the real table home.  Restore resets do not
skip a gap because they begin to its left.  The operational two-step crossing
macros are proved on arbitrary live tapes and then specialized to the exact
power-stage output.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerBridgeStageMachine
open LocalHomeState

/-- The extra Boolean on copy control records whether the unique internal gap
has been crossed during the current rightward seek.  Home control separately
records whether its leftward scan must still skip that gap. -/
inductive GapCopyState
  | copy (s : copyMachine.State) (crossedGap : Bool)
  | home (resume : copyMachine.State) (skipGap : Bool) (s : LocalHomeState)
  deriving DecidableEq, Fintype

open GapCopyState

/-- Fixed gap-aware version of the unary copy controller.  Away from the one
special `00` seek and home cases it uses the existing verified transition
tables verbatim. -/
def gapCopyMachine : Machine where
  State := GapCopyState
  fin := inferInstance
  dec := inferInstance
  start := .copy copyMachine.start false
  halt
    | .copy s _ => copyMachine.halt s
    | .home _ _ _ => false
  δ
    | .copy s crossed, b =>
        if s.1 = 3 ∧ s.2 = false ∧ b = false ∧ crossed = false then
          (.copy (2, true) true, none, 1)
        else
          let tr := copyMachine.δ s b
          if tr.2.2 = 3 then
            (.home tr.1 (decide (tr.1.1 = 0)) scanHi, tr.2.1, 2)
          else
            (.copy tr.1 crossed, tr.2.1, tr.2.2)
    | .home resume skip s, b =>
        if s = probeLo ∧ b = false ∧ skip = true then
          (.home resume false scanHi, none, 0)
        else if s = done then
          (.copy resume false, none, 2)
        else
          let tr := localHomeMachine.δ s b
          (.home resume skip tr.1, tr.2.1, tr.2.2)
  accept
    | .copy s _ => copyMachine.accept s
    | .home _ _ _ => false

theorem step_gapSeek_low {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step gapCopyMachine ⟨.copy (2, true) false, p, T⟩ =
      ⟨.copy (3, false) false, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, gapCopyMachine, copyMachine, moveHead, h]

theorem step_gapSeek_high {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step gapCopyMachine ⟨.copy (3, false) false, p, T⟩ =
      ⟨.copy (2, true) true, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, gapCopyMachine, copyMachine, moveHead, h]

/-- Once the gap has been crossed, a later `00` retains the original target
meaning and enters the real grow state. -/
theorem step_target_high_after_gap {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step gapCopyMachine ⟨.copy (3, false) true, p, T⟩ =
      ⟨.copy (4, false) true, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, gapCopyMachine, copyMachine, moveHead, h]

/-- Cross the internal `00` from its low cell to the next pair's low cell. -/
theorem run_gapSeek_two {q : ℕ} {T : List Bool}
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false) :
    run gapCopyMachine 2 ⟨.copy (2, true) false, q, T⟩ =
      ⟨.copy (2, true) true, q + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_gapSeek_low hlo,
    step_gapSeek_high hhi]

theorem step_gapHome_high {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) (resume : copyMachine.State) :
    step gapCopyMachine ⟨.home resume true scanHi, p, T⟩ =
      ⟨.home resume true probeLo, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, gapCopyMachine, localHomeMachine, moveHead, h]

theorem step_gapHome_low {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) (resume : copyMachine.State) :
    step gapCopyMachine ⟨.home resume true probeLo, p, T⟩ =
      ⟨.home resume false scanHi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, gapCopyMachine, moveHead, h]

/-- Cross the same internal `00` right-to-left.  Control records that the gap
has now been skipped, so the next `00` is handled as the true local home. -/
theorem run_gapHome_two {q : ℕ} {T : List Bool} (hq : 0 < q)
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (resume : copyMachine.State) :
    run gapCopyMachine 2 ⟨.home resume true scanHi, q + 1, T⟩ =
      ⟨.home resume false scanHi, q - 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_gapHome_high hhi,
    show q + 1 - 1 = q by omega,
    step_gapHome_low hlo]

/-- With gap skipping disabled, a `00` delimiter has the original local-home
meaning and resumes the remembered copy state at the following cell. -/
theorem run_trueHome_four {q : ℕ} {T : List Bool}
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (resume : copyMachine.State) :
    run gapCopyMachine 4 ⟨.home resume false scanHi, q + 1, T⟩ =
      ⟨.copy resume false, q + 2, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  simp [step, gapCopyMachine, localHomeMachine, moveHead, hlo, hhi]

def stagedGapOffset (pre : List Bool) (a : ℕ) : ℕ :=
  pre.length + (unaryD a).length

theorem powerStageOutput_gap_lo (pre : List Bool) (n a : ℕ)
    (payload : List Bool) :
    (powerStageOutput pre n a payload).getD
      (stagedGapOffset pre a) false = false := by
  rw [powerStageOutput, stagedGapOffset,
    getD_append_left_length' pre (gappedBridgeCore n a payload) rfl]
  exact gappedBridgeCore_getD_home_lo n a payload

theorem powerStageOutput_gap_hi (pre : List Bool) (n a : ℕ)
    (payload : List Bool) :
    (powerStageOutput pre n a payload).getD
      (stagedGapOffset pre a + 1) false = false := by
  rw [powerStageOutput, stagedGapOffset,
    show pre.length + (unaryD a).length + 1 =
      pre.length + ((unaryD a).length + 1) by omega,
    getD_append_left_length' pre (gappedBridgeCore n a payload) rfl]
  exact gappedBridgeCore_getD_home_hi n a payload

theorem run_powerStage_gapSeek (pre : List Bool) (n a : ℕ)
    (payload : List Bool) :
    let q := stagedGapOffset pre a
    run gapCopyMachine 2
      ⟨.copy (2, true) false, q, powerStageOutput pre n a payload⟩ =
      ⟨.copy (2, true) true, q + 2, powerStageOutput pre n a payload⟩ := by
  intro q
  exact run_gapSeek_two
    (powerStageOutput_gap_lo pre n a payload)
    (powerStageOutput_gap_hi pre n a payload)

theorem run_powerStage_gapHome (pre : List Bool) (n a : ℕ)
    (payload : List Bool) (resume : copyMachine.State) :
    let q := stagedGapOffset pre a
    run gapCopyMachine 2
      ⟨.home resume true scanHi, q + 1,
        powerStageOutput pre n a payload⟩ =
      ⟨.home resume false scanHi, q - 1,
        powerStageOutput pre n a payload⟩ := by
  intro q
  apply run_gapHome_two
  · simp [q, stagedGapOffset, unaryD_length]
  · exact powerStageOutput_gap_lo pre n a payload
  · exact powerStageOutput_gap_hi pre n a payload

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine.run_gapSeek_two
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine.run_gapHome_two
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine.run_trueHome_four
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine.run_powerStage_gapSeek
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCopyMachine.run_powerStage_gapHome
