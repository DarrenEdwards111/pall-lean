import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupOutputRouter

/-!
# Charged local lookup: dynamic accepting-bit router handoff

`acceptRouteMachine M` runs `M`, inspects its accepting bit at the first halt,
resets the head, and enters one of the two verified singleton append machines.
Thus branch selection occurs in finite control from the computed bit, not in
an external semantic theorem.

Both exact composition theorems absorb early body halting by the standard
least-halt argument.  The capacity specializations then prove that either
computed bit is routed into the reserved output while preserving the entire
following payload.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter

abbrev FalseRouterState := (appendMachine [false]).State
abbrev TrueRouterState := (appendMachine [true]).State

/-- Run `M`, then dynamically choose the false or true one-bit router from
`M.accept` at its halted state. -/
def acceptRouteMachine (M : Machine) : Machine where
  State := M.State ⊕ (FalseRouterState ⊕ TrueRouterState)
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl M.start
  halt := fun s => match s with
    | .inl _ => false
    | .inr (.inl sf) => (appendMachine [false]).halt sf
    | .inr (.inr st) => (appendMachine [true]).halt st
  δ := fun s b => match s with
    | .inl sm =>
        if M.halt sm then
          if M.accept sm then
            (Sum.inr (Sum.inr (appendMachine [true]).start), none, 3)
          else
            (Sum.inr (Sum.inl (appendMachine [false]).start), none, 3)
        else
          let tr := M.δ sm b
          (Sum.inl tr.1, tr.2.1, tr.2.2)
    | .inr (.inl sf) =>
        let tr := (appendMachine [false]).δ sf b
        (Sum.inr (Sum.inl tr.1), tr.2.1, tr.2.2)
    | .inr (.inr st) =>
        let tr := (appendMachine [true]).δ st b
        (Sum.inr (Sum.inr tr.1), tr.2.1, tr.2.2)
  accept := fun _ => false

def embedAcceptBody (M : Machine) (c : Cfg M) : Cfg (acceptRouteMachine M) :=
  ⟨Sum.inl c.st, c.hd, c.tp⟩

def embedFalseRouter (M : Machine) (c : Cfg (appendMachine [false])) :
    Cfg (acceptRouteMachine M) :=
  ⟨Sum.inr (Sum.inl c.st), c.hd, c.tp⟩

def embedTrueRouter (M : Machine) (c : Cfg (appendMachine [true])) :
    Cfg (acceptRouteMachine M) :=
  ⟨Sum.inr (Sum.inr c.st), c.hd, c.tp⟩

theorem acceptRoute_step_body (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = false) :
    step (acceptRouteMachine M) (embedAcceptBody M c) =
      embedAcceptBody M (step M c) := by
  simp only [step, acceptRouteMachine, embedAcceptBody, hh,
    Bool.false_eq_true, ↓reduceIte]

theorem acceptRoute_step_false (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = true) (ha : M.accept c.st = false) :
    step (acceptRouteMachine M) (embedAcceptBody M c) =
      embedFalseRouter M (init (appendMachine [false]) c.tp) := by
  simp [step, acceptRouteMachine, embedAcceptBody, embedFalseRouter,
    hh, ha, moveHead, init]

theorem acceptRoute_step_true (M : Machine) (c : Cfg M)
    (hh : M.halt c.st = true) (ha : M.accept c.st = true) :
    step (acceptRouteMachine M) (embedAcceptBody M c) =
      embedTrueRouter M (init (appendMachine [true]) c.tp) := by
  simp [step, acceptRouteMachine, embedAcceptBody, embedTrueRouter,
    hh, ha, moveHead, init]

theorem acceptRoute_step_falseRouter (M : Machine)
    (c : Cfg (appendMachine [false])) :
    step (acceptRouteMachine M) (embedFalseRouter M c) =
      embedFalseRouter M (step (appendMachine [false]) c) := by
  by_cases hh : (appendMachine [false]).halt c.st = true
  · have hw : (acceptRouteMachine M).halt (embedFalseRouter M c).st = true := by
      exact hh
    rw [step_of_halted _ hw, step_of_halted _ hh]
  · have hh' : (appendMachine [false]).halt c.st = false := by simpa using hh
    simp only [step, acceptRouteMachine, embedFalseRouter, hh',
      Bool.false_eq_true, ↓reduceIte]

theorem acceptRoute_step_trueRouter (M : Machine)
    (c : Cfg (appendMachine [true])) :
    step (acceptRouteMachine M) (embedTrueRouter M c) =
      embedTrueRouter M (step (appendMachine [true]) c) := by
  by_cases hh : (appendMachine [true]).halt c.st = true
  · have hw : (acceptRouteMachine M).halt (embedTrueRouter M c).st = true := by
      exact hh
    rw [step_of_halted _ hw, step_of_halted _ hh]
  · have hh' : (appendMachine [true]).halt c.st = false := by simpa using hh
    simp only [step, acceptRouteMachine, embedTrueRouter, hh',
      Bool.false_eq_true, ↓reduceIte]

theorem acceptRoute_run_body (M : Machine) (c : Cfg M) (n : Nat)
    (hactive : ∀ i, i < n → M.halt (run M i c).st = false) :
    run (acceptRouteMachine M) n (embedAcceptBody M c) =
      embedAcceptBody M (run M n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, ih (fun i hi => hactive i (by omega)),
        acceptRoute_step_body M _ (hactive n (by omega)), ← run_succ]

theorem acceptRoute_run_falseRouter (M : Machine)
    (c : Cfg (appendMachine [false])) (n : Nat) :
    run (acceptRouteMachine M) n (embedFalseRouter M c) =
      embedFalseRouter M (run (appendMachine [false]) n c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, acceptRoute_step_falseRouter, ← run_succ]

theorem acceptRoute_run_trueRouter (M : Machine)
    (c : Cfg (appendMachine [true])) (n : Nat) :
    run (acceptRouteMachine M) n (embedTrueRouter M c) =
      embedTrueRouter M (run (appendMachine [true]) n c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, acceptRoute_step_trueRouter, ← run_succ]

/-! ## Exact dynamic composition -/

theorem acceptRoute_run_false (M : Machine) (T : List Bool) (n r : Nat)
    (hh : M.halt (run M n (init M T)).st = true)
    (ha : M.accept (run M n (init M T)).st = false)
    (hroute : (appendMachine [false]).halt
      (run (appendMachine [false]) r
        (init (appendMachine [false]) (run M n (init M T)).tp)).st = true) :
    run (acceptRouteMachine M) (n + 1 + r)
        (init (acceptRouteMachine M) T) =
      embedFalseRouter M
        (run (appendMachine [false]) r (init (appendMachine [false])
          (run M n (init M T)).tp)) := by
  let c0 := init M T
  let cf := run M n c0
  have hex : ∃ i, M.halt (run M i c0).st = true := ⟨n, hh⟩
  have hfirst := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_le hh
  have hfrozen : run M (Nat.find hex) c0 = cf := by
    dsimp only [cf, c0]
    rw [← run_stable M T hle hfirst]
  have hactive : ∀ i, i < Nat.find hex →
      M.halt (run M i c0).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hb := acceptRoute_run_body M c0 (Nat.find hex) hactive
  rw [hfrozen] at hb
  have hs := acceptRoute_step_false M cf (by simpa [cf] using hh)
    (by simpa [cf] using ha)
  change run (acceptRouteMachine M) (n + 1 + r)
      (embedAcceptBody M c0) = _
  rw [show n + 1 + r = Nat.find hex + (1 + (r + (n - Nat.find hex))) by omega,
    run_add, hb, run_add, run_succ, run_zero, hs, run_add,
    acceptRoute_run_falseRouter,
    run_of_halted _ (by simpa [cf] using hroute)]

/- The true branch is the same least-halt composition. -/
theorem acceptRoute_run_true (M : Machine) (T : List Bool) (n r : Nat)
    (hh : M.halt (run M n (init M T)).st = true)
    (ha : M.accept (run M n (init M T)).st = true)
    (hroute : (appendMachine [true]).halt
      (run (appendMachine [true]) r
        (init (appendMachine [true]) (run M n (init M T)).tp)).st = true) :
    run (acceptRouteMachine M) (n + 1 + r)
        (init (acceptRouteMachine M) T) =
      embedTrueRouter M
        (run (appendMachine [true]) r (init (appendMachine [true])
          (run M n (init M T)).tp)) := by
  let c0 := init M T
  let cf := run M n c0
  have hex : ∃ i, M.halt (run M i c0).st = true := ⟨n, hh⟩
  have hfirst := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_le hh
  have hfrozen : run M (Nat.find hex) c0 = cf := by
    dsimp only [cf, c0]
    rw [← run_stable M T hle hfirst]
  have hactive : ∀ i, i < Nat.find hex →
      M.halt (run M i c0).st = false := by
    intro i hi
    simpa using Nat.find_min hex hi
  have hb := acceptRoute_run_body M c0 (Nat.find hex) hactive
  rw [hfrozen] at hb
  have hs := acceptRoute_step_true M cf (by simpa [cf] using hh)
    (by simpa [cf] using ha)
  change run (acceptRouteMachine M) (n + 1 + r)
      (embedAcceptBody M c0) = _
  rw [show n + 1 + r = Nat.find hex + (1 + (r + (n - Nat.find hex))) by omega,
    run_add, hb, run_add, run_succ, run_zero, hs, run_add,
    acceptRoute_run_trueRouter,
    run_of_halted _ (by simpa [cf] using hroute)]

/-! ## Reserved-output specializations -/

/-- If the body halts rejecting on a capacity-padded tape, the machine itself
selects the false router and appends `false` without disturbing the payload. -/
theorem acceptRoute_output_false (M : Machine) (T : List Bool) (n B : Nat)
    (out payload : List Bool) (sf : M.State) (p : Nat)
    (hbody : run M n (init M T) =
      ⟨sf, p, outputCap B out ++ payload⟩)
    (hh : M.halt sf = true) (ha : M.accept sf = false)
    (hout : out.length < B) :
    run (acceptRouteMachine M) (n + 1 + outputRouteClock out)
        (init (acceptRouteMachine M) T) =
      embedFalseRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [false]) ++ payload⟩ := by
  have hh' : M.halt (run M n (init M T)).st = true := by
    rw [hbody]
    exact hh
  have ha' : M.accept (run M n (init M T)).st = false := by
    rw [hbody]
    exact ha
  have hr : (appendMachine [false]).halt
      (run (appendMachine [false]) (outputRouteClock out)
        (init (appendMachine [false]) (run M n (init M T)).tp)).st = true := by
    rw [hbody]
    exact outputRouter_halts false B out payload hout
  have h := acceptRoute_run_false M T n (outputRouteClock out) hh' ha' hr
  rw [hbody, outputRouter_run false B out payload hout] at h
  exact h

/-- If the body halts accepting on a capacity-padded tape, the machine itself
selects the true router and appends `true` without disturbing the payload. -/
theorem acceptRoute_output_true (M : Machine) (T : List Bool) (n B : Nat)
    (out payload : List Bool) (sf : M.State) (p : Nat)
    (hbody : run M n (init M T) =
      ⟨sf, p, outputCap B out ++ payload⟩)
    (hh : M.halt sf = true) (ha : M.accept sf = true)
    (hout : out.length < B) :
    run (acceptRouteMachine M) (n + 1 + outputRouteClock out)
        (init (acceptRouteMachine M) T) =
      embedTrueRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [true]) ++ payload⟩ := by
  have hh' : M.halt (run M n (init M T)).st = true := by
    rw [hbody]
    exact hh
  have ha' : M.accept (run M n (init M T)).st = true := by
    rw [hbody]
    exact ha
  have hr : (appendMachine [true]).halt
      (run (appendMachine [true]) (outputRouteClock out)
        (init (appendMachine [true]) (run M n (init M T)).tp)).st = true := by
    rw [hbody]
    exact outputRouter_halts true B out payload hout
  have h := acceptRoute_run_true M T n (outputRouteClock out) hh' ha' hr
  rw [hbody, outputRouter_run true B out payload hout] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute.acceptRoute_run_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute.acceptRoute_run_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute.acceptRoute_output_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute.acceptRoute_output_true
