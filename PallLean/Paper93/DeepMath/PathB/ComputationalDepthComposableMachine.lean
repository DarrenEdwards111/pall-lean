import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# A composition-friendly, non-vacuous machine model — for `ReductionClosure`

The corpus's `ChargedMachine` is decision-only (run a fixed clock, read the accept bit): no halt state, memoryless
step, so transducers can't be sequenced.  This file builds a composition-friendly variant and (next file section)
proves **P is closed under poly many-one reductions**, discharging the `ReductionClosure` ingredient of the
observer-class SAT factoring.

Non-vacuity is preserved exactly as in `ChargedMachine`: **finite** state set (`Fintype`), **forced** init
(`⟨start, 0, x⟩`, copies input), local finite `δ` table.  Composition-friendliness is added by (i) a `halt` flag
(idempotent `step` once halted, so "run until done" is well-defined) and (ii) a `reset`-to-`0` `Move` (so a
sequenced machine reads from the start).  Both are benign (bounded, non-computational): they add no power to decide
languages, only the ability to *sequence*.

This section: the model, `run`, halting, deciders and transducers, and the basic stability lemmas.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ComposableMachine

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- Head moves: `0`=left, `1`=right, `2`=stay, `3`=reset-to-`0`. -/
abbrev Move := Fin 4

/-- Apply a move to a head position. -/
def moveHead (h : ℕ) (m : Move) : ℕ :=
  if m = 0 then h - 1 else if m = 1 then h + 1 else if m = 2 then h else 0

/-- Write `w` at position `p`, padding with `false` if needed. -/
def writeAt (tape : List Bool) (p : ℕ) (w : Bool) : List Bool :=
  (tape ++ List.replicate (p + 1 - tape.length) false).set p w

/-- A composition-friendly machine: finite control, halt flag, local table, decision. -/
structure Machine where
  /-- Finite state set. -/
  State : Type
  /-- Finiteness (locality). -/
  fin : Fintype State
  /-- Decidable equality of states. -/
  dec : DecidableEq State
  /-- Start state. -/
  start : State
  /-- Halting predicate. -/
  halt : State → Bool
  /-- Local transition (used only when not halted); the write is optional (`none` = leave the tape). -/
  δ : State → Bool → State × Option Bool × Move
  /-- Decision read at a halted state. -/
  accept : State → Bool

attribute [instance] Machine.fin Machine.dec

/-- A configuration. -/
structure Cfg (M : Machine) where
  /-- Control state. -/
  st : M.State
  /-- Head position. -/
  hd : ℕ
  /-- Tape. -/
  tp : List Bool

/-- Forced initializer: start state, head `0`, input on the tape. -/
def init (M : Machine) (x : List Bool) : Cfg M := ⟨M.start, 0, x⟩

/-- One step: idempotent once halted; else the local transition. -/
def step (M : Machine) (c : Cfg M) : Cfg M :=
  if M.halt c.st then c
  else
    let tr := M.δ c.st (c.tp.getD c.hd false)
    ⟨tr.1, moveHead c.hd tr.2.2, (match tr.2.1 with | none => c.tp | some w => writeAt c.tp c.hd w)⟩

/-- Run `t` steps. -/
def run (M : Machine) (t : ℕ) (c : Cfg M) : Cfg M := (step M)^[t] c

@[simp] theorem run_zero (M : Machine) (c : Cfg M) : run M 0 c = c := rfl

theorem run_succ (M : Machine) (t : ℕ) (c : Cfg M) : run M (t + 1) c = step M (run M t c) :=
  Function.iterate_succ_apply' (step M) t c

/-- A halted configuration is a fixed point of `step`. -/
theorem step_of_halted (M : Machine) {c : Cfg M} (h : M.halt c.st = true) : step M c = c := by
  unfold step; rw [h]; rfl

/-- Once halted, running does nothing (halt is stable). -/
theorem run_of_halted (M : Machine) {c : Cfg M} (h : M.halt c.st = true) (t : ℕ) :
    run M t c = c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_of_halted M h]

/-- Splitting a run. -/
theorem run_add (M : Machine) (a b : ℕ) (c : Cfg M) : run M (a + b) c = run M b (run M a c) := by
  unfold run; rw [add_comm a b]; exact Function.iterate_add_apply (step M) b a c

/-- If halted by time `t`, it stays halted at any later time with the same config. -/
theorem run_stable (M : Machine) (x : List Bool) {t T : ℕ} (hle : t ≤ T)
    (h : M.halt (run M t (init M x)).st = true) :
    run M T (init M x) = run M t (init M x) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run_add]; exact run_of_halted M h d

/-- The decision read after `T` steps. -/
def decideOut (M : Machine) (x : List Bool) (T : ℕ) : Bool := M.accept (run M T (init M x)).st

/-- The transducer output after `T` steps (the tape). -/
def transOut (M : Machine) (x : List Bool) (T : ℕ) : List Bool := (run M T (init M x)).tp

/-- `M` halts by `T`. -/
def HaltsBy (M : Machine) (x : List Bool) (T : ℕ) : Prop := M.halt (run M T (init M x)).st = true

/-- `M` decides `L` within clock `T`. -/
def Decides (M : Machine) (L : List Bool → Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, HaltsBy M x (T x.length) ∧ decideOut M x (T x.length) = L x

/-- The languages decided in poly time — genuine, uniform, non-vacuous P. -/
def InP (L : List Bool → Bool) : Prop := ∃ (M : Machine) (T : ℕ → ℕ), PolyBounded T ∧ Decides M L T

/-- `M` transduces `f` within clock `T`. -/
def Transduces (M : Machine) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, HaltsBy M x (T x.length) ∧ transOut M x (T x.length) = f x

/-- Poly-time string functions. -/
def PolyComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ), PolyBounded T ∧ Transduces M f T

/-- Poly many-one reduction. -/
def PolyReduces (L L' : List Bool → Bool) : Prop :=
  ∃ f, PolyComputable f ∧ ∀ x, L x = L' (f x)

/-! ## Sequential composition and its simulation lemmas -/

/-- The sequential composition: run `Mf` (a transducer); when it halts, switch — with a pure control step
(`none` write, `reset` move) that leaves the tape and moves the head to `0` — to `Mg` (a decider). -/
def comp (Mf Mg : Machine) : Machine where
  State := Mf.State ⊕ Mg.State
  fin := inferInstance
  dec := inferInstance
  start := Sum.inl Mf.start
  halt := fun s => match s with | .inl _ => false | .inr sg => Mg.halt sg
  δ := fun s b => match s with
    | .inl sf => if Mf.halt sf then (Sum.inr Mg.start, none, (3 : Move))
                 else let tr := Mf.δ sf b; (Sum.inl tr.1, tr.2.1, tr.2.2)
    | .inr sg => let tr := Mg.δ sg b; (Sum.inr tr.1, tr.2.1, tr.2.2)
  accept := fun s => match s with | .inl _ => false | .inr sg => Mg.accept sg

/-- Embed an `Mf` config into the composition (first phase). -/
def embedL (Mf Mg : Machine) (c : Cfg Mf) : Cfg (comp Mf Mg) := ⟨Sum.inl c.st, c.hd, c.tp⟩

/-- Embed an `Mg` config into the composition (second phase). -/
def embedR (Mf Mg : Machine) (c : Cfg Mg) : Cfg (comp Mf Mg) := ⟨Sum.inr c.st, c.hd, c.tp⟩

/-- Phase-1 step: while `Mf` has not halted, the composition mirrors `Mf`. -/
theorem comp_step_inl (Mf Mg : Machine) (cf : Cfg Mf) (h : Mf.halt cf.st = false) :
    step (comp Mf Mg) (embedL Mf Mg cf) = embedL Mf Mg (step Mf cf) := by
  simp only [step, comp, embedL, h, Bool.false_eq_true, ↓reduceIte]

/-- The switch step: when `Mf` has halted, one composition step moves to `Mg`'s start, resets the head to `0`,
and leaves the tape (`= f x`) intact. -/
theorem comp_step_switch (Mf Mg : Machine) (cf : Cfg Mf) (h : Mf.halt cf.st = true) :
    step (comp Mf Mg) (embedL Mf Mg cf) = embedR Mf Mg ⟨Mg.start, 0, cf.tp⟩ := by
  simp only [step, comp, embedL, embedR, h, Bool.false_eq_true, ↓reduceIte, moveHead]
  rfl

/-- Phase-2 step: the composition mirrors `Mg`. -/
theorem comp_step_inr (Mf Mg : Machine) (cg : Cfg Mg) :
    step (comp Mf Mg) (embedR Mf Mg cg) = embedR Mf Mg (step Mg cg) := by
  simp only [step, comp, embedR]
  by_cases h : Mg.halt cg.st = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-- **Phase 1**: for `t` up to (just before) `Mf`'s first halt, the composition simulates `Mf`. -/
theorem comp_phase1 (Mf Mg : Machine) (x : List Bool) (t : ℕ)
    (hmin : ∀ s < t, Mf.halt (run Mf s (init Mf x)).st = false) :
    run (comp Mf Mg) t (init (comp Mf Mg) x) = embedL Mf Mg (run Mf t (init Mf x)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, ih (fun s hs => hmin s (Nat.lt_succ_of_lt hs))]
    rw [comp_step_inl Mf Mg _ (hmin t (Nat.lt_succ_self t)), ← run_succ]

/-- **Phase 2**: from the switched configuration, the composition simulates `Mg`. -/
theorem comp_phase2 (Mf Mg : Machine) (x : List Bool) (hf : ℕ) (y : List Bool) (s : ℕ)
    (hsw : run (comp Mf Mg) (hf + 1) (init (comp Mf Mg) x) = embedR Mf Mg ⟨Mg.start, 0, y⟩) :
    run (comp Mf Mg) (hf + 1 + s) (init (comp Mf Mg) x)
      = embedR Mf Mg (run Mg s (init Mg y)) := by
  induction s with
  | zero => rw [Nat.add_zero, hsw]; rfl
  | succ s ih =>
    rw [← Nat.add_assoc, run_succ, ih, comp_step_inr, ← run_succ]

end PallLean.Paper93.DeepMath.PathB.ComposableMachine
