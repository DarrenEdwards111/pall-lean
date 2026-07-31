import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalHomeMachine

/-!
# MCSP verifier: run-level local-reset macro for counter copying

`localCopyMachine` replaces an absolute reset of the verified unary copy
machine by delimiter-aware local-home control.  The preceding file proves the
individual transition laws.  Here those laws are closed under iteration.

For any embedded `00` home delimiter followed by `k` nonblank doubled pairs,
the adapter:

1. scans from the rightmost high cell back to the delimiter;
2. preserves the complete live tape;
3. lands exactly on the first local counter cell; and
4. resumes the exact copy state remembered by the intercepted transition.

The final `run_localCopy_reset_macro` includes the original copy transition
itself, including its optional write.  It is the reusable macro needed to
replace every absolute-reset step in the existing multi-round copy proof.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine
open LocalHomeState
open LocalCopyState

theorem step_home_scanHi_true (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step localCopyMachine ⟨.home resume scanHi, p, T⟩ =
      ⟨.home resume scanLo, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localCopyMachine, localHomeMachine, moveHead, h]

theorem step_home_scanHi_false (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step localCopyMachine ⟨.home resume scanHi, p, T⟩ =
      ⟨.home resume probeLo, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localCopyMachine, localHomeMachine, moveHead, h]

theorem step_home_scanLo (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} :
    step localCopyMachine ⟨.home resume scanLo, p, T⟩ =
      ⟨.home resume scanHi, p - 1, T⟩ := by
  simp [step, localCopyMachine, localHomeMachine, moveHead]

theorem step_home_probeLo_true (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step localCopyMachine ⟨.home resume probeLo, p, T⟩ =
      ⟨.home resume scanHi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localCopyMachine, localHomeMachine, moveHead, h]

theorem step_home_probeLo_false (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step localCopyMachine ⟨.home resume probeLo, p, T⟩ =
      ⟨.home resume advance, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localCopyMachine, localHomeMachine, moveHead, h]

theorem step_home_advance (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} :
    step localCopyMachine ⟨.home resume advance, p, T⟩ =
      ⟨.home resume done, p + 1, T⟩ := by
  simp [step, localCopyMachine, localHomeMachine, moveHead]

/-- The adapter crosses one non-`00` doubled pair in exactly two steps. -/
theorem run_two_homePair (resume : copyMachine.State)
    {p : ℕ} {T : List Bool} (hp : 0 < p)
    (hpair :
      T.getD p false = true ∨ T.getD (p + 1) false = true) :
    run localCopyMachine 2
      ⟨.home resume scanHi, p + 1, T⟩ =
      ⟨.home resume scanHi, p - 1, T⟩ := by
  rcases hpair with hlo | hhi
  · by_cases h : T.getD (p + 1) false = true
    · rw [run_succ, run_succ, run_zero,
        step_home_scanHi_true resume h,
        show p + 1 - 1 = p by omega,
        step_home_scanLo resume]
    · have hf : T.getD (p + 1) false = false := by
        simpa using h
      rw [run_succ, run_succ, run_zero,
        step_home_scanHi_false resume hf,
        show p + 1 - 1 = p by omega,
        step_home_probeLo_true resume hlo]
  · rw [run_succ, run_succ, run_zero,
      step_home_scanHi_true resume hhi,
      show p + 1 - 1 = p by omega,
      step_home_scanLo resume]

/-- The adapter recognizes `00` and reaches its internal completed-home state
at the first cell following the delimiter. -/
theorem run_three_homeDelimiter (resume : copyMachine.State)
    {q : ℕ} {T : List Bool}
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false) :
    run localCopyMachine 3
      ⟨.home resume scanHi, q + 1, T⟩ =
      ⟨.home resume done, q + 2, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero,
    step_home_scanHi_false resume hhi,
    show q + 1 - 1 = q by omega,
    step_home_probeLo_false resume hlo,
    step_home_advance resume]

/-- Run-level local-home theorem inside the reset-adapted copy controller. -/
theorem run_localCopy_home (resume : copyMachine.State)
    (T : List Bool) (q k : ℕ)
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (hpairs : ∀ i, i < k →
      T.getD (q + 2 + 2 * i) false = true ∨
        T.getD (q + 2 + 2 * i + 1) false = true) :
    run localCopyMachine (2 * k + 3)
      ⟨.home resume scanHi, q + 1 + 2 * k, T⟩ =
      ⟨.home resume done, q + 2, T⟩ := by
  induction k with
  | zero =>
      simpa using
        run_three_homeDelimiter resume (q := q) (T := T) hlo hhi
  | succ k ih =>
      rw [show 2 * (k + 1) + 3 = 2 + (2 * k + 3) by omega,
        run_add,
        show q + 1 + 2 * (k + 1) =
          (q + 2 + 2 * k) + 1 by omega,
        run_two_homePair resume (p := q + 2 + 2 * k)
          (T := T) (by omega) (hpairs k (by omega)),
        show q + 2 + 2 * k - 1 = q + 1 + 2 * k by omega]
      apply ih
      intro i hi
      exact hpairs i (by omega)

/-- One additional pure-control step resumes the remembered copy state. -/
theorem run_localCopy_home_resume (resume : copyMachine.State)
    (T : List Bool) (q k : ℕ)
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (hpairs : ∀ i, i < k →
      T.getD (q + 2 + 2 * i) false = true ∨
        T.getD (q + 2 + 2 * i + 1) false = true) :
    run localCopyMachine (2 * k + 4)
      ⟨.home resume scanHi, q + 1 + 2 * k, T⟩ =
      ⟨.copy resume, q + 2, T⟩ := by
  rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega,
    run_add, run_localCopy_home resume T q k hlo hhi hpairs,
    run_succ, run_zero, step_localCopy_resume]

/-- A complete reset macro.  The first step is the original copy transition
(and therefore performs exactly its optional write); the remaining steps
return to local home and resume its requested next state. -/
theorem run_localCopy_reset_macro (c : Cfg copyMachine)
    (q k : ℕ)
    (hhalt : copyMachine.halt c.st = false)
    (hmove : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 3)
    (hpos : c.hd = q + 1 + 2 * k)
    (hlo :
      (match (copyMachine.δ c.st
        (c.tp.getD c.hd false)).2.1 with
      | none => c.tp
      | some w => writeAt c.tp c.hd w).getD q false = false)
    (hhi :
      (match (copyMachine.δ c.st
        (c.tp.getD c.hd false)).2.1 with
      | none => c.tp
      | some w => writeAt c.tp c.hd w).getD (q + 1) false = false)
    (hpairs : ∀ i, i < k →
      (match (copyMachine.δ c.st
        (c.tp.getD c.hd false)).2.1 with
      | none => c.tp
      | some w => writeAt c.tp c.hd w).getD
          (q + 2 + 2 * i) false = true ∨
      (match (copyMachine.δ c.st
        (c.tp.getD c.hd false)).2.1 with
      | none => c.tp
      | some w => writeAt c.tp c.hd w).getD
          (q + 2 + 2 * i + 1) false = true) :
    run localCopyMachine (2 * k + 5) (copyCfg c) =
      ⟨.copy
          (copyMachine.δ c.st (c.tp.getD c.hd false)).1,
        q + 2,
        match (copyMachine.δ c.st
          (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w⟩ := by
  let T' :=
    match (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.1 with
    | none => c.tp
    | some w => writeAt c.tp c.hd w
  have hfirst :
      run localCopyMachine 1 (copyCfg c) =
        ⟨.home
            (copyMachine.δ c.st (c.tp.getD c.hd false)).1 scanHi,
          c.hd, T'⟩ := by
    simpa [run_succ, T'] using
      step_localCopy_reset c hhalt hmove
  rw [show 2 * k + 5 = 1 + (2 * k + 4) by omega,
    run_add, hfirst]
  simpa [T', hpos] using
    run_localCopy_home_resume
      (copyMachine.δ c.st (c.tp.getD c.hd false)).1
      T' q k hlo hhi hpairs

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun.run_localCopy_home_resume
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalCopyRun.run_localCopy_reset_macro
