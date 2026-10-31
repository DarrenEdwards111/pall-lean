import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInitLoop

/-!
# Cook–Levin M2 emitter — the grand loop combinator

The last assembly mechanism: `repMachine M` runs the sub-machine `M` **a runtime-bounded number of
times** — the machine-level `for t in 0..B-1: run M`, where `B` lives on the tape.  The combinator
owns the tape's first region as the countdown-marking bound (`cntT B t`): each round it skips the `t`
marks, marks the next pair, resets the head, and hands off to `M`; when `M` halts it resets and
returns to the loop find; at the bound's terminator it heals the bound and halts.

**The composition theorem is unconditional in `M`'s halting behaviour**, but the early-halt slack can
no longer be absorbed at the end of the run as in `seq_run` — the loop continues, so per-round drift
accumulates.  The fix is the `reaches` relation (`∃ t ≤ T, run M t c = c'`): it composes transitively
(no freezing needed mid-flight), each round *reaches* its exit within its budget (the first-halt
`Nat.find` argument round-locally), and the total budget cashes out to an **exact clock** at the final
configuration because that one is halted (`reaches_halted` + the freeze semantics).

`rep_run` consumes a **tape-sequence hypothesis**: for each `t < B`, `M`'s run theorem on the tape
`cntT B (t+1) ++ rest t` — the marked bound as a passive prefix — ending halted on
`cntT B (t+1) ++ rest (t+1)`.  This is exactly the shape the emitter engines' theorems take after the
mechanical prefix-generalisation (their scans are content-driven; the bound's pairs are lo-`true` like
any counter), which is the E6 instantiation step.  The idle instance (`rep_idle_run`) validates the
skeleton: a body that halts immediately yields `B` rounds of pure loop control, the bound marked and
healed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice

/-! ## The `reaches` relation -/

/-- `c` evolves to `c'` within `T` steps. -/
def reaches (M : Machine) (T : ℕ) (c c' : Cfg M) : Prop := ∃ t ≤ T, run M t c = c'

theorem reaches_of_run {M : Machine} {T : ℕ} {c c' : Cfg M} (h : run M T c = c') :
    reaches M T c c' := ⟨T, le_refl T, h⟩

theorem reaches_trans {M : Machine} {a b : ℕ} {c c' c'' : Cfg M}
    (h1 : reaches M a c c') (h2 : reaches M b c' c'') : reaches M (a + b) c c'' := by
  obtain ⟨t1, ht1, hr1⟩ := h1
  obtain ⟨t2, ht2, hr2⟩ := h2
  exact ⟨t1 + t2, by omega, by rw [run_add, hr1, hr2]⟩

theorem reaches_mono {M : Machine} {a b : ℕ} {c c' : Cfg M} (hab : a ≤ b)
    (h : reaches M a c c') : reaches M b c c' := by
  obtain ⟨t, ht, hr⟩ := h
  exact ⟨t, by omega, hr⟩

/-- **The cash-out**: a budgeted arrival at a *halted* configuration is an exact-clock arrival. -/
theorem reaches_halted {M : Machine} {T : ℕ} {c c' : Cfg M} (h : reaches M T c c')
    (hh : M.halt c'.st = true) : run M T c = c' := by
  obtain ⟨t, ht, hr⟩ := h
  rw [show T = t + (T - t) from by omega, run_add, hr, run_of_halted M hh]

/-! ## The repeat combinator -/

/-- **The runtime-bounded repeat**: loop-find on the leading countdown bound, hand off to `M`, return
at `M`'s halts, heal the bound at its terminator, halt. -/
def repMachine (M : Machine) : Machine where
  State := (Fin 5 × Bool) ⊕ M.State
  fin := letI := M.fin; inferInstance
  dec := letI := M.dec; inferInstance
  start := Sum.inl (0, false)
  halt := fun s => match s with
    | .inl (ph, _) => decide (ph = 4)
    | .inr _ => false
  δ := fun s b => match s with
    | .inl (ph, st) =>
      if ph = 0 then (Sum.inl (1, b), none, 1)
      else if ph = 1 then
        (if st then
          (if b then (Sum.inr M.start, some false, 3)
           else (Sum.inl (0, st), none, 1))
         else (if b then (Sum.inl (2, st), none, 3)
               else (Sum.inl (4, st), none, 2)))
      else if ph = 2 then (Sum.inl (3, b), none, 1)
      else if ph = 3 then
        (if st then
          (if b then (Sum.inl (4, false), none, 2)
           else (Sum.inl (2, true), some true, 1))
         else (if b then (Sum.inl (4, false), none, 2)
               else (Sum.inl (4, false), none, 2)))
      else (Sum.inl (ph, st), none, 2)
    | .inr m =>
      if M.halt m then (Sum.inl (0, false), none, 3)
      else (Sum.inr (M.δ m b).1, (M.δ m b).2.1, (M.δ m b).2.2)
  accept := fun _ => false

def inrCfgR (M : Machine) (c : Cfg M) : Cfg (repMachine M) := ⟨.inr c.st, c.hd, c.tp⟩

theorem rep_halt_inl (M : Machine) (ph : Fin 5) (st : Bool) :
    (repMachine M).halt (Sum.inl (ph, st)) = decide (ph = 4) := rfl

theorem rep_halt_inr (M : Machine) (s : M.State) :
    (repMachine M).halt (Sum.inr s) = false := rfl

theorem init_rep (M : Machine) (x : List Bool) :
    init (repMachine M) x = ⟨Sum.inl (0, false), 0, x⟩ := rfl

/-! ### Control step laws -/

section Steps
variable {M : Machine} {s : Bool} {p : ℕ} {T : List Bool}

theorem rp_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (repMachine M) 2 ⟨Sum.inl (0, s), p, T⟩ = ⟨Sum.inl (0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repMachine M) ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inl (1, T.getD p false), p + 1, T⟩ := by
    simp only [step, repMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repMachine, moveHead, h2]

/-- The mark-and-handoff: mark the bound's pair, reset, enter `M`. -/
theorem rp_mark (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (repMachine M) 2 ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inr M.start, 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repMachine M) ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inl (1, T.getD p false), p + 1, T⟩ := by
    simp only [step, repMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repMachine, moveHead, h2]

theorem rp_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repMachine M) 2 ⟨Sum.inl (0, s), p, T⟩ = ⟨Sum.inl (2, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repMachine M) ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inl (1, T.getD p false), p + 1, T⟩ := by
    simp only [step, repMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repMachine, moveHead, h2]

theorem rp_heal (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (repMachine M) 2 ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (2, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repMachine M) ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (3, T.getD p false), p + 1, T⟩ := by
    simp only [step, repMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repMachine, moveHead, h2]

theorem rp_doneH (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repMachine M) 2 ⟨Sum.inl (2, s), p, T⟩ = ⟨Sum.inl (4, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repMachine M) ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (3, T.getD p false), p + 1, T⟩ := by
    simp only [step, repMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repMachine, moveHead, h2]

/-- The body simulation, below `M`'s halt. -/
theorem step_rep_inr (c : Cfg M) (h : M.halt c.st = false) :
    step (repMachine M) (inrCfgR M c) = inrCfgR M (step M c) := by
  unfold step
  rw [show (inrCfgR M c).st = Sum.inr c.st from rfl, rep_halt_inr]
  simp only [Bool.false_eq_true, if_false]
  unfold repMachine
  simp only [h, Bool.false_eq_true, if_false]
  rfl

/-- The return handoff: `M` halted — reset, re-enter the loop find. -/
theorem step_rep_return (c : Cfg M) (h : M.halt c.st = true) :
    step (repMachine M) (inrCfgR M c) = ⟨Sum.inl (0, false), 0, c.tp⟩ := by
  unfold step
  rw [show (inrCfgR M c).st = Sum.inr c.st from rfl, rep_halt_inr]
  simp only [Bool.false_eq_true, if_false]
  unfold repMachine
  simp only [h, if_true]
  rfl

end Steps

/-- The body simulation below the first halt. -/
theorem run_rep_inr (M : Machine) (c : Cfg M) (t : ℕ)
    (h : ∀ t', t' < t → M.halt (run M t' c).st = false) :
    run (repMachine M) t (inrCfgR M c) = inrCfgR M (run M t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun t' ht' => h t' (by omega)),
      step_rep_inr _ (h t (by omega)), ← run_succ]

/-- The loop-find skip invariant. -/
theorem rp_skipBs (M : Machine) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (repMachine M) (2 * k) ⟨Sum.inl (0, s), q, T⟩
      = ⟨Sum.inl (0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rp_skipB hk.1 hk.2]
    rfl

/-- The bound-heal invariant. -/
theorem rp_healBs (M : Machine) (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (repMachine M) (2 * i) ⟨Sum.inl (2, s), 0, hlT v 0 ++ E⟩
      = ⟨Sum.inl (2, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      rp_heal (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## THE GRAND LOOP THEOREM -/

/-- One round: find and mark the bound's pair `t`, run `M` to its halt, return. -/
theorem rep_round (M : Machine) (B t : ℕ) (ht : t < B) (rest rest' : List Bool)
    (clk : ℕ) (sf : M.State) (pf : ℕ)
    (hbody : run M clk (init M (cntT B (t + 1) ++ rest)) = ⟨sf, pf, cntT B (t + 1) ++ rest'⟩)
    (hhalt : M.halt sf = true) :
    reaches (repMachine M) (2 * t + 2 + (clk + 1))
      ⟨Sum.inl (0, false), 0, cntT B t ++ rest⟩
      ⟨Sum.inl (0, false), 0, cntT B (t + 1) ++ rest'⟩ := by
  have f1 := rp_skipBs M (cntT B t ++ rest) 0 t false
    (fun i hi => ⟨by simpa using cntE_mark_lo B t _ i hi,
                  by simpa using cntE_mark_hi B t _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := rp_mark (M := M) (s := if t = 0 then false else true) (p := 2 * t)
    (T := cntT B t ++ rest)
    (cntE_data B t _ (2 * t) (by omega) (by omega) (by omega))
    (cntE_data B t _ (2 * t + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark B t _ ht] at f2
  -- the body: first-halt argument
  have hex : ∃ u, M.halt (run M u (init M (cntT B (t + 1) ++ rest))).st = true :=
    ⟨clk, by rw [hbody]; exact hhalt⟩
  have htm : M.halt (run M (Nat.find hex) (init M (cntT B (t + 1) ++ rest))).st = true :=
    Nat.find_spec hex
  have htm_le : Nat.find hex ≤ clk := Nat.find_le (by rw [hbody]; exact hhalt)
  have hfrozen : run M (Nat.find hex) (init M (cntT B (t + 1) ++ rest))
      = ⟨sf, pf, cntT B (t + 1) ++ rest'⟩ := by
    rw [← run_stable M _ htm_le htm, hbody]
  have hno : ∀ u, u < Nat.find hex →
      M.halt (run M u (init M (cntT B (t + 1) ++ rest))).st = false := by
    intro u hu
    have := Nat.find_min hex hu
    simpa using this
  have hsim := run_rep_inr M (init M (cntT B (t + 1) ++ rest)) (Nat.find hex) hno
  rw [hfrozen] at hsim
  have hret := step_rep_return (M := M) (⟨sf, pf, cntT B (t + 1) ++ rest'⟩ : Cfg M) hhalt
  refine ⟨2 * t + 2 + (Nat.find hex + 1), by omega, ?_⟩
  rw [show 2 * t + 2 + (Nat.find hex + 1) = 2 * t + (2 + (Nat.find hex + 1)) from by omega,
    run_add, f1, run_add, f2,
    show (⟨Sum.inr M.start, 0, cntT B (t + 1) ++ rest⟩ : Cfg (repMachine M))
      = inrCfgR M (init M (cntT B (t + 1) ++ rest)) from rfl,
    run_add, hsim, run_succ, run_zero, hret]

/-- The cumulative round budget. -/
def repRounds (clk : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => repRounds clk t + (2 * t + 2 + (clk t + 1))

/-- The rounds, by `reaches`-composition. -/
theorem rep_rounds (M : Machine) (B : ℕ) (rest : ℕ → List Bool) (clk : ℕ → ℕ)
    (sf : ℕ → M.State) (pf : ℕ → ℕ)
    (hbody : ∀ t, t < B →
      run M (clk t) (init M (cntT B (t + 1) ++ rest t))
        = ⟨sf t, pf t, cntT B (t + 1) ++ rest (t + 1)⟩ ∧ M.halt (sf t) = true)
    (k : ℕ) (hk : k ≤ B) :
    reaches (repMachine M) (repRounds clk k)
      ⟨Sum.inl (0, false), 0, cntT B 0 ++ rest 0⟩
      ⟨Sum.inl (0, false), 0, cntT B k ++ rest k⟩ := by
  induction k with
  | zero => exact ⟨0, le_refl 0, rfl⟩
  | succ k ih =>
    exact reaches_trans (ih (by omega))
      (rep_round M B k (by omega) (rest k) (rest (k + 1)) (clk k) (sf k) (pf k)
        (hbody k (by omega)).1 (hbody k (by omega)).2)

/-- **THE GRAND LOOP RUNS TO COMPLETION.**  Given the tape-sequence hypothesis — `M`'s per-round run
theorem on `cntT B (t+1) ++ rest t`, halted, preserving the marked bound and advancing the rest — the
combinator marks, runs, and returns `B` times, heals the bound, and halts at **exactly** the budgeted
clock, with tape `unaryD B ++ rest B`. -/
theorem rep_run (M : Machine) (B : ℕ) (rest : ℕ → List Bool) (clk : ℕ → ℕ)
    (sf : ℕ → M.State) (pf : ℕ → ℕ)
    (hbody : ∀ t, t < B →
      run M (clk t) (init M (cntT B (t + 1) ++ rest t))
        = ⟨sf t, pf t, cntT B (t + 1) ++ rest (t + 1)⟩ ∧ M.halt (sf t) = true) :
    run (repMachine M) (repRounds clk B + (4 * B + 4))
      (init (repMachine M) (cntT B 0 ++ rest 0))
      = ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ rest B⟩ := by
  have hrounds := rep_rounds M B rest clk sf pf hbody B (le_refl B)
  have f1 := rp_skipBs M (cntT B B ++ rest B) 0 B false
    (fun i hi => ⟨by simpa using cntE_mark_lo B B _ i hi,
                  by simpa using cntE_mark_hi B B _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := rp_doneB (M := M) (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B B ++ rest B)
    (cntE_cm_lo B B _ (le_refl B)) (cntE_cm_hi B B _ (le_refl B))
  have f3 := rp_healBs M B (rest B) false B (le_refl B)
  have f4 := rp_doneH (M := M) (s := if B = 0 then false else true) (p := 2 * B)
    (T := hlT B B ++ rest B) (hlE_cm_lo B _) (hlE_cm_hi B _)
  have hfin : reaches (repMachine M) (repRounds clk B + (4 * B + 4))
      (init (repMachine M) (cntT B 0 ++ rest 0))
      ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ rest B⟩ := by
    rw [init_rep]
    refine reaches_trans hrounds (reaches_of_run ?_)
    rw [show 4 * B + 4 = 2 * B + (2 + (2 * B + 2)) from by omega,
      run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last]
  exact reaches_halted hfin rfl

/-! ## The idle instance

The immediately-halting body validates the skeleton: `B` rounds of pure loop control, the bound
marked pair by pair and healed at the end. -/

/-- The one-state, immediately-halting machine. -/
def idleMachine : Machine where
  State := Unit
  fin := inferInstance
  dec := inferInstance
  start := ()
  halt := fun _ => true
  δ := fun _ _ => ((), none, 2)
  accept := fun _ => false

/-- **The idle loop**: `B` rounds of pure control on a constant rest. -/
theorem rep_idle_run (B : ℕ) (rest : List Bool) :
    run (repMachine idleMachine) (repRounds (fun _ => 0) B + (4 * B + 4))
      (init (repMachine idleMachine) (cntT B 0 ++ rest))
      = ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ rest⟩ :=
  rep_run idleMachine B (fun _ => rest) (fun _ => 0) (fun _ => ()) (fun _ => 0)
    (fun _ _ => ⟨rfl, rfl⟩)

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep