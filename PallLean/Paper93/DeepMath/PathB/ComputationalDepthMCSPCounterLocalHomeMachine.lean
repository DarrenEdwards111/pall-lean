import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterCopyScratchMachine

/-!
# MCSP verifier: delimiter-aware local counter home

The unary copy machine resets to absolute tape cell `0` after each copying
round.  A second counter embedded later in one physical tape instead needs a
*local* reset.  This file supplies the finite-control primitive for that weld.

The local counter is preceded by a doubled `00` delimiter.  Starting on the
high cell of the rightmost pair, `localHomeMachine` walks left by pairs.  It
does not confuse a processed `10` counter pair with the delimiter: on a false
high cell it probes the low cell, continuing across `10` and stopping only at
`00`.  It then advances exactly two cells and halts at the local counter's
first cell.

The main theorem is offset-parametric and tape-preserving.  It assumes only
that every intervening pair has at least one true cell, which covers `11`
data, `10` processed data, and `01` unary boundaries.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

inductive LocalHomeState
  | scanHi
  | scanLo
  | probeLo
  | advance
  | done
  deriving DecidableEq, Fintype

open LocalHomeState

/-- Fixed local-home controller.  The tape is never written. -/
def localHomeMachine : Machine where
  State := LocalHomeState
  fin := inferInstance
  dec := inferInstance
  start := scanHi
  halt
    | done => true
    | _ => false
  δ
    | scanHi, b =>
        if b then (scanLo, none, 0) else (probeLo, none, 0)
    | scanLo, _ => (scanHi, none, 0)
    | probeLo, b =>
        if b then (scanHi, none, 0) else (advance, none, 1)
    | advance, _ => (done, none, 1)
    | done, _ => (done, none, 2)
  accept
    | done => true
    | _ => false

theorem step_scanHi_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step localHomeMachine ⟨scanHi, p, T⟩ =
      ⟨scanLo, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localHomeMachine, moveHead, h]

theorem step_scanHi_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step localHomeMachine ⟨scanHi, p, T⟩ =
      ⟨probeLo, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localHomeMachine, moveHead, h]

theorem step_scanLo {p : ℕ} {T : List Bool} :
    step localHomeMachine ⟨scanLo, p, T⟩ =
      ⟨scanHi, p - 1, T⟩ := by
  simp [step, localHomeMachine, moveHead]

theorem step_probeLo_true {p : ℕ} {T : List Bool}
    (h : T.getD p false = true) :
    step localHomeMachine ⟨probeLo, p, T⟩ =
      ⟨scanHi, p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localHomeMachine, moveHead, h]

theorem step_probeLo_false {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    step localHomeMachine ⟨probeLo, p, T⟩ =
      ⟨advance, p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, localHomeMachine, moveHead, h]

theorem step_advance {p : ℕ} {T : List Bool} :
    step localHomeMachine ⟨advance, p, T⟩ =
      ⟨done, p + 1, T⟩ := by
  simp [step, localHomeMachine, moveHead]

/-- Move left across one non-`00` pair, from its high cell to the preceding
pair's high cell.  Both `high = true` and processed `10` are covered. -/
theorem run_two_pair {p : ℕ} {T : List Bool} (hp : 0 < p)
    (hpair :
      T.getD p false = true ∨ T.getD (p + 1) false = true) :
    run localHomeMachine 2 ⟨scanHi, p + 1, T⟩ =
      ⟨scanHi, p - 1, T⟩ := by
  rcases hpair with hlo | hhi
  · by_cases h : T.getD (p + 1) false = true
    · rw [run_succ, run_succ, run_zero, step_scanHi_true h,
        show p + 1 - 1 = p by omega, step_scanLo]
    · have hf : T.getD (p + 1) false = false := by
        simpa using h
      rw [run_succ, run_succ, run_zero, step_scanHi_false hf,
        show p + 1 - 1 = p by omega, step_probeLo_true hlo]
  · rw [run_succ, run_succ, run_zero, step_scanHi_true hhi,
      show p + 1 - 1 = p by omega, step_scanLo]

/-- Recognize the doubled `00` delimiter and halt at the first cell after it. -/
theorem run_three_delimiter {q : ℕ} {T : List Bool}
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false) :
    run localHomeMachine 3 ⟨scanHi, q + 1, T⟩ =
      ⟨done, q + 2, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero,
    step_scanHi_false hhi,
    show q + 1 - 1 = q by omega,
    step_probeLo_false hlo, step_advance]

/-- Scan `k` nonblank doubled pairs right-to-left, recognize the `00` local
home delimiter at `q,q+1`, and halt at `q+2`. -/
theorem run_localHome (T : List Bool) (q k : ℕ)
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (hpairs : ∀ i, i < k →
      T.getD (q + 2 + 2 * i) false = true ∨
        T.getD (q + 2 + 2 * i + 1) false = true) :
    run localHomeMachine (2 * k + 3)
      ⟨scanHi, q + 1 + 2 * k, T⟩ =
      ⟨done, q + 2, T⟩ := by
  induction k with
  | zero =>
      simpa using run_three_delimiter (q := q) (T := T) hlo hhi
  | succ k ih =>
      rw [show 2 * (k + 1) + 3 = 2 + (2 * k + 3) by omega,
        run_add,
        show q + 1 + 2 * (k + 1) =
          (q + 2 + 2 * k) + 1 by omega,
        run_two_pair (p := q + 2 + 2 * k) (T := T)
          (by omega) (hpairs k (by omega)),
        show q + 2 + 2 * k - 1 = q + 1 + 2 * k by omega]
      apply ih
      intro i hi
      exact hpairs i (by omega)

theorem localHome_halts (T : List Bool) (q k : ℕ)
    (hlo : T.getD q false = false)
    (hhi : T.getD (q + 1) false = false)
    (hpairs : ∀ i, i < k →
      T.getD (q + 2 + 2 * i) false = true ∨
        T.getD (q + 2 + 2 * i + 1) false = true) :
    localHomeMachine.halt
      (run localHomeMachine (2 * k + 3)
        ⟨scanHi, q + 1 + 2 * k, T⟩).st = true := by
  rw [run_localHome T q k hlo hhi hpairs]
  rfl

/-! ## Local-reset adapter for the real copy machine -/

open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy

/-- Control of the adapted copy machine.  A reset transition remembers the
copy state it must resume and invokes the local-home scanner. -/
inductive LocalCopyState
  | copy (s : copyMachine.State)
  | home (resume : copyMachine.State) (s : LocalHomeState)
  deriving DecidableEq, Fintype

open LocalCopyState

/-- The real unary copy transition table with absolute reset transitions
replaced by delimiter-aware local resets.  Every non-reset transition is
unchanged. -/
def localCopyMachine : Machine where
  State := LocalCopyState
  fin := inferInstance
  dec := inferInstance
  start := .copy copyMachine.start
  halt
    | .copy s => copyMachine.halt s
    | .home _ _ => false
  δ
    | .copy s, b =>
        let tr := copyMachine.δ s b
        if tr.2.2 = 3 then
          (.home tr.1 scanHi, tr.2.1, 2)
        else
          (.copy tr.1, tr.2.1, tr.2.2)
    | .home resume done, _ => (.copy resume, none, 2)
    | .home resume s, b =>
        let tr := localHomeMachine.δ s b
        (.home resume tr.1, tr.2.1, tr.2.2)
  accept
    | .copy s => copyMachine.accept s
    | .home _ _ => false

def copyCfg (c : Cfg copyMachine) : Cfg localCopyMachine :=
  ⟨.copy c.st, c.hd, c.tp⟩

def homeCfg (resume : copyMachine.State) (c : Cfg localHomeMachine) :
    Cfg localCopyMachine :=
  ⟨.home resume c.st, c.hd, c.tp⟩

/-- Non-reset copy transitions are simulated exactly. -/
theorem step_localCopy_nonreset (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hmove : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 ≠ 3) :
    step localCopyMachine (copyCfg c) =
      copyCfg (step copyMachine c) := by
  simp only [step, localCopyMachine, copyCfg, hhalt,
    Bool.false_eq_true, if_false]
  rw [if_neg hmove]

/-- An absolute-reset copy transition performs the same write and remembers
the same resume state, but stays at the current head and enters local-home
control. -/
theorem step_localCopy_reset (c : Cfg copyMachine)
    (hhalt : copyMachine.halt c.st = false)
    (hmove : (copyMachine.δ c.st
      (c.tp.getD c.hd false)).2.2 = 3) :
    step localCopyMachine (copyCfg c) =
      ⟨.home
          (copyMachine.δ c.st (c.tp.getD c.hd false)).1 scanHi,
        c.hd,
        match (copyMachine.δ c.st
          (c.tp.getD c.hd false)).2.1 with
        | none => c.tp
        | some w => writeAt c.tp c.hd w⟩ := by
  simp only [step, localCopyMachine, copyCfg, hhalt,
    Bool.false_eq_true, if_false]
  rw [if_pos hmove]
  simp [moveHead]
  rfl

/-- While local-home control has not reached `done`, the adapter simulates
the local-home machine exactly and retains the copy resume state. -/
theorem step_localCopy_home (resume : copyMachine.State)
    (c : Cfg localHomeMachine)
    (h : c.st ≠ done) :
    step localCopyMachine (homeCfg resume c) =
      homeCfg resume (step localHomeMachine c) := by
  rcases c with ⟨s, p, T⟩
  cases s <;> simp_all [step, localCopyMachine, localHomeMachine,
    homeCfg, moveHead]

/-- Local-home completion resumes the remembered copy state without moving
the head or changing the tape. -/
theorem step_localCopy_resume (resume : copyMachine.State)
    (p : ℕ) (T : List Bool) :
    step localCopyMachine
      ⟨.home resume done, p, T⟩ =
      ⟨.copy resume, p, T⟩ := by
  simp [step, localCopyMachine]
  simp [moveHead]

end PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine.run_localHome
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine.localHome_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine.step_localCopy_reset
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPCounterLocalHomeMachine.step_localCopy_home
