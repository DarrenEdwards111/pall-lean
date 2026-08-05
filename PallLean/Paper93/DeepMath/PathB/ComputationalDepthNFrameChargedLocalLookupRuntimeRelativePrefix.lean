import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeOutputLayout

/-!
# Reset-aware relative prefix transport

The runtime source selector intentionally uses machine reset to return to its
own origin.  When the source lives behind `outputCap`, a raw reset would land
at the global output origin.  `relativePrefixAdapter` repairs this exactly:
it performs the requested reset, rescans the protected prefix, and resumes
the body at relative head zero with the body's post-reset control state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixAdapter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal

/-- Scan state carries an optional body state. `none` is initial entry;
`some s` is resumption after a translated body reset. -/
abbrev RelativeScanState (P : Nat) (M : Machine) :=
  Fin (P + 1) × (Unit ⊕ M.State)

def relativeResumeState (M : Machine) : Unit ⊕ M.State → M.State
  | .inl _ => M.start
  | .inr s => s

def relativePrefixAdapter (P : Nat) (M : Machine) : Machine where
  State := RelativeScanState P M ⊕ M.State
  fin := letI := M.fin; inferInstance
  dec := letI := M.dec; inferInstance
  start := Sum.inl (⟨0, by omega⟩, Sum.inl ())
  halt := fun s => match s with
    | .inl _ => false
    | .inr sm => M.halt sm
  δ := fun s b => match s with
    | .inl (i, resume) =>
        if hi : i.val < P then
          (Sum.inl (⟨i.val + 1, by omega⟩, resume), none, 1)
        else
          (Sum.inr (relativeResumeState M resume), none, 2)
    | .inr sm =>
        if M.halt sm then (Sum.inr sm, none, 2)
        else
          let tr := M.δ sm b
          if tr.2.2 = 3 then
            (Sum.inl (⟨0, by omega⟩, Sum.inr tr.1), tr.2.1, 3)
          else
            (Sum.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with
    | .inl _ => false
    | .inr sm => M.accept sm

def embedRelativeBody (P : Nat) (M : Machine) (pre : List Bool)
    (c : Cfg M) : Cfg (relativePrefixAdapter P M) :=
  ⟨Sum.inr c.st, pre.length + c.hd, pre ++ c.tp⟩

theorem relativePrefix_step_scan (P : Nat) (M : Machine) (T : List Bool)
    (resume : Unit ⊕ M.State) (i : Nat) (hi : i < P) :
    step (relativePrefixAdapter P M)
        ⟨Sum.inl (⟨i, by omega⟩, resume), i, T⟩ =
      ⟨Sum.inl (⟨i + 1, by omega⟩, resume), i + 1, T⟩ := by
  simp [step, relativePrefixAdapter, hi, moveHead]

theorem relativePrefix_step_switch (P : Nat) (M : Machine) (T : List Bool)
    (resume : Unit ⊕ M.State) :
    step (relativePrefixAdapter P M)
        ⟨Sum.inl (⟨P, by omega⟩, resume), P, T⟩ =
      ⟨Sum.inr (relativeResumeState M resume), P, T⟩ := by
  simp [step, relativePrefixAdapter, moveHead]

theorem relativePrefix_run_scan (P : Nat) (M : Machine) (T : List Bool)
    (resume : Unit ⊕ M.State) (i : Nat) (hi : i ≤ P) :
    run (relativePrefixAdapter P M) i
        ⟨Sum.inl (⟨0, by omega⟩, resume), 0, T⟩ =
      ⟨Sum.inl (⟨i, by omega⟩, resume), i, T⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [run_succ, ih (by omega)]
      exact relativePrefix_step_scan P M T resume i (by omega)

theorem relativePrefix_enter (P : Nat) (M : Machine)
    (pre tail : List Bool) (hpre : pre.length = P) :
    run (relativePrefixAdapter P M) (P + 1)
        (init (relativePrefixAdapter P M) (pre ++ tail)) =
      embedRelativeBody P M pre (init M tail) := by
  change run (relativePrefixAdapter P M) (P + 1)
      ⟨Sum.inl (⟨0, by omega⟩, Sum.inl ()), 0, pre ++ tail⟩ = _
  rw [run_succ,
    relativePrefix_run_scan P M (pre ++ tail) (Sum.inl ()) P (by omega),
    relativePrefix_step_switch]
  simp [embedRelativeBody, init, relativeResumeState, hpre]

/-- A live body reset is translated into one real reset plus an exact prefix
rescan and handoff, landing at the body's post-step relative origin. -/
theorem relativePrefix_run_reset (P : Nat) (M : Machine)
    (pre : List Bool) (c : Cfg M) (hpre : pre.length = P)
    (hh : M.halt c.st = false)
    (hr : (M.δ c.st (c.tp.getD c.hd false)).2.2 = 3) :
    run (relativePrefixAdapter P M) (P + 2)
        (embedRelativeBody P M pre c) =
      embedRelativeBody P M pre (step M c) := by
  let tr := M.δ c.st (c.tp.getD c.hd false)
  have hread : (pre ++ c.tp).getD (pre.length + c.hd) false =
      c.tp.getD c.hd false := by
    rw [PallLean.Paper93.DeepMath.PathB.CookLevinInP.getD_append_ge
      (by omega)]
    simp
  have hfirst : run (relativePrefixAdapter P M) 1
      (embedRelativeBody P M pre c) =
      ⟨Sum.inl (⟨0, by omega⟩, Sum.inr tr.1), 0,
        pre ++ (match tr.2.1 with
          | none => c.tp
          | some w => writeAt c.tp c.hd w)⟩ := by
    rw [run_succ, run_zero]
    simp only [step, relativePrefixAdapter, embedRelativeBody, hh,
      Bool.false_eq_true, ↓reduceIte, hread, tr]
    rw [if_pos hr]
    cases hw : tr.2.1 with
    | none => simp [moveHead, hr]
    | some w =>
        simp only
        rw [writeAt_append_shift]
        simp [moveHead, hr]
  have hmoveBody : moveHead c.hd
      (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 := by
    rw [hr]
    rfl
  rw [show P + 2 = 1 + (P + 1) by omega, run_add, hfirst,
    run_succ, relativePrefix_run_scan P M _ (Sum.inr tr.1) P (by omega),
    relativePrefix_step_switch]
  simp only [embedRelativeBody, step, hh, Bool.false_eq_true, ↓reduceIte,
    tr, hpre, relativeResumeState]
  rw [hmoveBody]
  cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 <;> simp [hw]

/-- A non-reset body transition commutes with the relative embedding.  The
only side condition is the genuine tape-origin condition for a left move. -/
theorem relativePrefix_step_body_noReset (P : Nat) (M : Machine)
    (pre : List Bool) (c : Cfg M)
    (hreset : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3)
    (hleft : M.halt c.st = false →
      (M.δ c.st (c.tp.getD c.hd false)).2.2 = 0 → 0 < c.hd) :
    step (relativePrefixAdapter P M) (embedRelativeBody P M pre c) =
      embedRelativeBody P M pre (step M c) := by
  cases hh : M.halt c.st with
  | false =>
      have hread : (pre ++ c.tp).getD (pre.length + c.hd) false =
          c.tp.getD c.hd false := by
        rw [PallLean.Paper93.DeepMath.PathB.CookLevinInP.getD_append_ge
          (by omega)]
        simp
      have hmove := moveHead_add_of_no_reset pre.length c.hd
        (M.δ c.st (c.tp.getD c.hd false)).2.2
        (hreset hh) (hleft hh)
      simp only [step, relativePrefixAdapter, embedRelativeBody, hh,
        Bool.false_eq_true, ↓reduceIte, hread]
      rw [if_neg (hreset hh), hmove]
      cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
      | none => simp
      | some w =>
          simp only
          rw [writeAt_append_shift]
  | true =>
      simp [step, relativePrefixAdapter, embedRelativeBody, hh]

/-- Exact physical cost of transporting the first `n` body steps.  Each live
body reset pays for the reset step and an exact `P`-cell rescan plus handoff;
all other body steps cost one physical transition. -/
def relativeRunClock (P : Nat) (M : Machine) (c : Cfg M) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      relativeRunClock P M c n +
        if M.halt (run M n c).st = false ∧
            (M.δ (run M n c).st
              ((run M n c).tp.getD (run M n c).hd false)).2.2 = 3 then
          P + 2
        else 1

/-- A whole body run, including arbitrary body resets, commutes with the
relative-prefix embedding.  Reset relocation is unconditional; only the
actual left boundary of the body tape must remain safe. -/
theorem relativePrefix_run_body (P : Nat) (M : Machine)
    (pre : List Bool) (c : Cfg M) (n : Nat)
    (hpre : pre.length = P) (hleft : LeftSafeRun M c n) :
    run (relativePrefixAdapter P M) (relativeRunClock P M c n)
        (embedRelativeBody P M pre c) =
      embedRelativeBody P M pre (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hleftN : LeftSafeRun M c n := by
        intro i hi
        exact hleft i (by omega)
      rw [relativeRunClock, run_add, ih hleftN]
      cases hh : M.halt (run M n c).st with
      | true =>
          simp only [hh, Bool.true_eq_false, false_and, ↓reduceIte]
          rw [run_succ, run_zero]
          simpa only [run_succ] using
            relativePrefix_step_body_noReset P M pre (run M n c)
              (by simp [hh]) (by simp [hh])
      | false =>
          by_cases hr : (M.δ (run M n c).st
              ((run M n c).tp.getD (run M n c).hd false)).2.2 = 3
          · simp only [hh, true_and, hr, ↓reduceIte]
            simpa only [run_succ] using
              relativePrefix_run_reset P M pre (run M n c) hpre hh hr
          · simp only [hh, true_and, hr, ↓reduceIte]
            rw [run_succ, run_zero]
            simpa only [run_succ] using
              relativePrefix_step_body_noReset P M pre (run M n c)
                (by intro _; exact hr)
                (by
                  intro _ hm
                  exact hleft n (by omega) hh hm)

/-- Initial entry followed by a complete reset-aware body run. -/
theorem relativePrefix_run (P : Nat) (M : Machine) (pre tail : List Bool)
    (n : Nat) (hpre : pre.length = P)
    (hleft : LeftSafeRun M (init M tail) n) :
    run (relativePrefixAdapter P M)
        (P + 1 + relativeRunClock P M (init M tail) n)
        (init (relativePrefixAdapter P M) (pre ++ tail)) =
      embedRelativeBody P M pre (run M n (init M tail)) := by
  rw [run_add, relativePrefix_enter P M pre tail hpre]
  exact relativePrefix_run_body P M pre (init M tail) n hpre hleft

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix.relativePrefix_enter
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix.relativePrefix_run_reset
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix.relativePrefix_run
