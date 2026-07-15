import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMulT

/-!
# Cook–Levin M2 emitter — the prefixed grand-loop combinator

`repPMachine M` is `repMachine M` under a grand prefix: it owns the tape's SECOND region as its
countdown bound (`cntT G g ++ (cntT B t ++ rest)`), skipping the leading region on every find and
on the final heal — the same appended-pair lift, applied to the loop combinator itself.  This is
the nesting mechanism for E2's majorant: a `repP`-driven multiplier can be the per-round body of an
outer `rep`, so `c·(n+1)^k` evaluates as `k`-nested grand loops over the doubly-prefixed adder —
the healed inner counters re-enter as `cntT v 0 = unaryD v` for free.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The machine

`(Fin 9 × Bool) ⊕ M.State`: `0/1` skip the grand prefix into the find, `2/3` the loop find (mark
and hand off to `M`, or done), `5/6` skip the prefix into the heal, `7/8` the bound heal, `4`
halt; `M` runs inside `Sum.inr`, returning to `0` at its halts. -/

def repPMachine (M : Machine) : Machine where
  State := (Fin 9 × Bool) ⊕ M.State
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
        (if st then (Sum.inl (0, st), none, 1)
         else (if b then (Sum.inl (2, st), none, 1) else (Sum.inl (4, st), none, 2)))
      else if ph = 2 then (Sum.inl (3, b), none, 1)
      else if ph = 3 then
        (if st then
          (if b then (Sum.inr M.start, some false, 3)
           else (Sum.inl (2, st), none, 1))
         else (if b then (Sum.inl (5, st), none, 3)
               else (Sum.inl (4, st), none, 2)))
      else if ph = 5 then (Sum.inl (6, b), none, 1)
      else if ph = 6 then
        (if st then (Sum.inl (5, st), none, 1)
         else (if b then (Sum.inl (7, st), none, 1) else (Sum.inl (4, st), none, 2)))
      else if ph = 7 then (Sum.inl (8, b), none, 1)
      else if ph = 8 then
        (if st then
          (if b then (Sum.inl (4, false), none, 2)
           else (Sum.inl (7, true), some true, 1))
         else (if b then (Sum.inl (4, false), none, 2)
               else (Sum.inl (4, false), none, 2)))
      else (Sum.inl (ph, st), none, 2)
    | .inr m =>
      if M.halt m then (Sum.inl (0, false), none, 3)
      else (Sum.inr (M.δ m b).1, (M.δ m b).2.1, (M.δ m b).2.2)
  accept := fun _ => false

def inrCfgP (M : Machine) (c : Cfg M) : Cfg (repPMachine M) := ⟨.inr c.st, c.hd, c.tp⟩

theorem repP_halt_inr (M : Machine) (s : M.State) :
    (repPMachine M).halt (Sum.inr s) = false := rfl

theorem init_repP (M : Machine) (x : List Bool) :
    init (repPMachine M) x = ⟨Sum.inl (0, false), 0, x⟩ := rfl

/-! ### Control step laws -/

section Steps
variable {M : Machine} {s : Bool} {p : ℕ} {T : List Bool}

theorem rpp_skipW (h1 : T.getD p false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (0, s), p, T⟩ = ⟨Sum.inl (0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inl (1, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, repPMachine, moveHead]; rfl

theorem rpp_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (0, s), p, T⟩ = ⟨Sum.inl (2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (0, s), p, T⟩
      = ⟨Sum.inl (1, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem rpp_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (repPMachine M) 2 ⟨Sum.inl (2, s), p, T⟩ = ⟨Sum.inl (2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (3, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

/-- The mark-and-handoff. -/
theorem rpp_mark (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inr M.start, 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (3, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem rpp_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (2, s), p, T⟩ = ⟨Sum.inl (5, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (2, s), p, T⟩
      = ⟨Sum.inl (3, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem rpp_skipWh (h1 : T.getD p false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (5, s), p, T⟩ = ⟨Sum.inl (5, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (5, s), p, T⟩
      = ⟨Sum.inl (6, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, repPMachine, moveHead]; rfl

theorem rpp_crossWh (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (5, s), p, T⟩ = ⟨Sum.inl (7, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (5, s), p, T⟩
      = ⟨Sum.inl (6, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem rpp_heal (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (repPMachine M) 2 ⟨Sum.inl (7, s), p, T⟩
      = ⟨Sum.inl (7, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (7, s), p, T⟩
      = ⟨Sum.inl (8, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem rpp_doneH (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (repPMachine M) 2 ⟨Sum.inl (7, s), p, T⟩ = ⟨Sum.inl (4, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (repPMachine M) ⟨Sum.inl (7, s), p, T⟩
      = ⟨Sum.inl (8, T.getD p false), p + 1, T⟩ := by
    simp only [step, repPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, repPMachine, moveHead, h2]

theorem step_repP_inr (c : Cfg M) (h : M.halt c.st = false) :
    step (repPMachine M) (inrCfgP M c) = inrCfgP M (step M c) := by
  unfold step
  rw [show (inrCfgP M c).st = Sum.inr c.st from rfl, repP_halt_inr]
  simp only [Bool.false_eq_true, if_false]
  unfold repPMachine
  simp only [h, Bool.false_eq_true, if_false]
  rfl

theorem step_repP_return (c : Cfg M) (h : M.halt c.st = true) :
    step (repPMachine M) (inrCfgP M c) = ⟨Sum.inl (0, false), 0, c.tp⟩ := by
  unfold step
  rw [show (inrCfgP M c).st = Sum.inr c.st from rfl, repP_halt_inr]
  simp only [Bool.false_eq_true, if_false]
  unfold repPMachine
  simp only [h, if_true]
  rfl

end Steps

theorem run_repP_inr (M : Machine) (c : Cfg M) (t : ℕ)
    (h : ∀ t', t' < t → M.halt (run M t' c).st = false) :
    run (repPMachine M) t (inrCfgP M c) = inrCfgP M (run M t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun t' ht' => h t' (by omega)),
      step_repP_inr _ (h t (by omega)), ← run_succ]

theorem rpp_skipWs (M : Machine) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (repPMachine M) (2 * k) ⟨Sum.inl (0, s), q, T⟩
      = ⟨Sum.inl (0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rpp_skipW (h k (by omega))]
    rfl

theorem rpp_skipWhs (M : Machine) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (repPMachine M) (2 * k) ⟨Sum.inl (5, s), q, T⟩
      = ⟨Sum.inl (5, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rpp_skipWh (h k (by omega))]
    rfl

theorem rpp_skipBs (M : Machine) (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (repPMachine M) (2 * k) ⟨Sum.inl (2, s), q, T⟩
      = ⟨Sum.inl (2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rpp_skipB hk.1 hk.2]
    rfl

/-- The prefixed bound heal. -/
theorem rpp_healBs (M : Machine) (P : List Bool) (G v : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (repPMachine M) (2 * i) ⟨Sum.inl (7, s), 2 * G + 2, P ++ (hlT v 0 ++ E)⟩
      = ⟨Sum.inl (7, if i = 0 then s else true), 2 * G + 2 + 2 * i,
          P ++ (hlT v i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ P _ hP (hlE_pair_lo v i E (by omega))
    have h2 : (P ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ P _ hP (hlE_pair_hi v i E (by omega))
    have hw : writeAt (P ++ (hlT v i ++ E)) (2 * G + 2 + 2 * i + 1) true
        = P ++ (hlT v (i + 1) ++ E) := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
        writeAt_append_right P _ (2 * G + 2) (2 * i + 1) true hP
          (by rw [List.length_append, hlT_length v i (by omega)]; omega),
        hlT_heal v i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      rpp_heal h1 h2, hw]
    rfl

/-! ## THE PREFIXED GRAND LOOP THEOREM -/

/-- One prefixed round. -/
theorem repP_round (M : Machine) (G g : ℕ) (hg : g ≤ G) (B t : ℕ) (ht : t < B)
    (rest rest' : List Bool) (clk : ℕ) (sf : M.State) (pf : ℕ)
    (hbody : run M clk (init M (cntT G g ++ (cntT B (t + 1) ++ rest)))
      = ⟨sf, pf, cntT G g ++ (cntT B (t + 1) ++ rest')⟩)
    (hhalt : M.halt sf = true) :
    reaches (repPMachine M) (2 * G + 2 + 2 * t + 2 + (clk + 1))
      ⟨Sum.inl (0, false), 0, cntT G g ++ (cntT B t ++ rest)⟩
      ⟨Sum.inl (0, false), 0, cntT G g ++ (cntT B (t + 1) ++ rest')⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have f0 := rpp_skipWs M (cntT G g ++ (cntT B t ++ rest)) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := rpp_crossW (M := M) (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT B t ++ rest))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := rpp_skipBs M (cntT G g ++ (cntT B t ++ rest)) (2 * G + 2) t false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo B t _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi B t _ i hi)⟩)
  have f2 := rpp_mark (M := M) (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * t) (T := cntT G g ++ (cntT B t ++ rest))
    (by rw [show 2 * G + 2 + 2 * t = 2 * G + 2 + (2 * t) from rfl]
        exact liftJ _ _ hW (cntE_data B t _ (2 * t) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * t + 1 = 2 * G + 2 + (2 * t + 1) from by omega]
        exact liftJ _ _ hW (cntE_data B t _ (2 * t + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G g ++ (cntT B t ++ rest)) (2 * G + 2 + 2 * t + 1) false
      = cntT G g ++ (cntT B (t + 1) ++ rest) := by
    rw [show 2 * G + 2 + 2 * t + 1 = 2 * G + 2 + (2 * t + 1) from by omega,
      writeAt_append_right _ _ (2 * G + 2) (2 * t + 1) false hW
        (by rw [List.length_append, cntT_length B t (by omega)]; omega),
      cntT_mark B t _ ht]
  rw [hwm] at f2
  have hex : ∃ u, M.halt (run M u (init M (cntT G g ++ (cntT B (t + 1) ++ rest)))).st
      = true := ⟨clk, by rw [hbody]; exact hhalt⟩
  have htm := Nat.find_spec hex
  have htm_le : Nat.find hex ≤ clk := Nat.find_le (by rw [hbody]; exact hhalt)
  have hfrozen : run M (Nat.find hex) (init M (cntT G g ++ (cntT B (t + 1) ++ rest)))
      = ⟨sf, pf, cntT G g ++ (cntT B (t + 1) ++ rest')⟩ := by
    rw [← run_stable M _ htm_le htm, hbody]
  have hno : ∀ u, u < Nat.find hex →
      M.halt (run M u (init M (cntT G g ++ (cntT B (t + 1) ++ rest)))).st = false := by
    intro u hu
    have := Nat.find_min hex hu
    simpa using this
  have hsim := run_repP_inr M (init M (cntT G g ++ (cntT B (t + 1) ++ rest)))
    (Nat.find hex) hno
  rw [hfrozen] at hsim
  have hret := step_repP_return (M := M)
    (⟨sf, pf, cntT G g ++ (cntT B (t + 1) ++ rest')⟩ : Cfg M) hhalt
  refine ⟨2 * G + 2 + 2 * t + 2 + (Nat.find hex + 1), by omega, ?_⟩
  rw [show 2 * G + 2 + 2 * t + 2 + (Nat.find hex + 1)
      = 2 * G + (2 + (2 * t + (2 + (Nat.find hex + 1)))) from by omega,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2,
    show (⟨Sum.inr M.start, 0, cntT G g ++ (cntT B (t + 1) ++ rest)⟩
        : Cfg (repPMachine M))
      = inrCfgP M (init M (cntT G g ++ (cntT B (t + 1) ++ rest))) from rfl,
    run_add, hsim, run_succ, run_zero, hret]

def repPRounds (G : ℕ) (clk : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => repPRounds G clk t + (2 * G + 2 + 2 * t + 2 + (clk t + 1))

theorem repP_rounds (M : Machine) (G g : ℕ) (hg : g ≤ G) (B : ℕ)
    (rest : ℕ → List Bool) (clk : ℕ → ℕ) (sf : ℕ → M.State) (pf : ℕ → ℕ)
    (hbody : ∀ t, t < B →
      run M (clk t) (init M (cntT G g ++ (cntT B (t + 1) ++ rest t)))
        = ⟨sf t, pf t, cntT G g ++ (cntT B (t + 1) ++ rest (t + 1))⟩
        ∧ M.halt (sf t) = true)
    (k : ℕ) (hk : k ≤ B) :
    reaches (repPMachine M) (repPRounds G clk k)
      ⟨Sum.inl (0, false), 0, cntT G g ++ (cntT B 0 ++ rest 0)⟩
      ⟨Sum.inl (0, false), 0, cntT G g ++ (cntT B k ++ rest k)⟩ := by
  induction k with
  | zero => exact ⟨0, le_refl 0, rfl⟩
  | succ k ih =>
    exact reaches_trans (ih (by omega))
      (repP_round M G g hg B k (by omega) (rest k) (rest (k + 1)) (clk k) (sf k) (pf k)
        (hbody k (by omega)).1 (hbody k (by omega)).2)

/-- **THE PREFIXED GRAND LOOP RUNS TO COMPLETION** — the leading region preserved verbatim, itself
a `rep_run`-shaped per-round body one level up. -/
theorem repP_run (M : Machine) (G g : ℕ) (hg : g ≤ G) (B : ℕ) (rest : ℕ → List Bool)
    (clk : ℕ → ℕ) (sf : ℕ → M.State) (pf : ℕ → ℕ)
    (hbody : ∀ t, t < B →
      run M (clk t) (init M (cntT G g ++ (cntT B (t + 1) ++ rest t)))
        = ⟨sf t, pf t, cntT G g ++ (cntT B (t + 1) ++ rest (t + 1))⟩
        ∧ M.halt (sf t) = true) :
    run (repPMachine M) (repPRounds G clk B + (4 * G + 4 * B + 8))
      (init (repPMachine M) (cntT G g ++ (cntT B 0 ++ rest 0)))
      = ⟨Sum.inl (4, false), 2 * G + 2 + 2 * B + 1,
          cntT G g ++ (unaryD B ++ rest B)⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hrounds := repP_rounds M G g hg B rest clk sf pf hbody B (le_refl B)
  have f0 := rpp_skipWs M (cntT G g ++ (cntT B B ++ rest B)) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := rpp_crossW (M := M) (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT B B ++ rest B))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := rpp_skipBs M (cntT G g ++ (cntT B B ++ rest B)) (2 * G + 2) B false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo B B _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi B B _ i hi)⟩)
  have f2 := rpp_doneB (M := M) (s := if B = 0 then false else true)
    (p := 2 * G + 2 + 2 * B) (T := cntT G g ++ (cntT B B ++ rest B))
    (by rw [show 2 * G + 2 + 2 * B = 2 * G + 2 + (2 * B) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo B B _ (le_refl B)))
    (by rw [show 2 * G + 2 + 2 * B + 1 = 2 * G + 2 + (2 * B + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi B B _ (le_refl B)))
  have f3 := rpp_skipWhs M (cntT G g ++ (hlT B 0 ++ rest B)) 0 G false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f3
  have f3' := rpp_crossWh (M := M) (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (hlT B 0 ++ rest B))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f4 := rpp_healBs M (cntT G g) G B (rest B) hW false B (le_refl B)
  have f5 := rpp_doneH (M := M) (s := if B = 0 then false else true)
    (p := 2 * G + 2 + 2 * B) (T := cntT G g ++ (hlT B B ++ rest B))
    (by rw [show 2 * G + 2 + 2 * B = 2 * G + 2 + (2 * B) from rfl]
        exact liftJ _ _ hW (hlE_cm_lo B _))
    (by rw [show 2 * G + 2 + 2 * B + 1 = 2 * G + 2 + (2 * B + 1) from by omega]
        exact liftJ _ _ hW (hlE_cm_hi B _))
  have hfin : reaches (repPMachine M) (repPRounds G clk B + (4 * G + 4 * B + 8))
      (init (repPMachine M) (cntT G g ++ (cntT B 0 ++ rest 0)))
      ⟨Sum.inl (4, false), 2 * G + 2 + 2 * B + 1, cntT G g ++ (unaryD B ++ rest B)⟩ := by
    rw [init_repP]
    refine reaches_trans hrounds (reaches_of_run ?_)
    rw [show 4 * G + 4 * B + 8
        = 2 * G + (2 + (2 * B + (2 + (2 * G + (2 + (2 * B + 2)))))) from by omega,
      run_add, f0, run_add, f0', run_add, f1, run_add, f2, ← hlT_zero, run_add, f3,
      run_add, f3', run_add, f4, f5, hlT_last]
  exact reaches_halted hfin rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP