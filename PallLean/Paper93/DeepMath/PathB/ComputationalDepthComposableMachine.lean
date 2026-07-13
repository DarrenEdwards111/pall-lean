import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# A composition-friendly, non-vacuous machine model — for `ReductionClosure`

The corpus's `ChargedMachine` is decision-only (run a fixed clock, read the accept bit): no halt state, memoryless
step, so transducers can't be sequenced.  This file builds a composition-friendly variant and proves
`reductionClosure`: **this model's P is closed under poly many-one reductions**, as a genuine *theorem* (not an
assumption).  This is what makes the closure real: in a model that *can* sequence a reducer before a decider, the
closure is provable; the decision-only `ChargedMachine` cannot, which is exactly why the observer-class SAT
factoring had to leave `ReductionClosure` as an opaque ingredient.

SCOPE / HONEST CAVEAT: this discharges `ReductionClosure` **for `ComposableMachine.InP`**.  The observer-class
fence (`ObserverClassSemantics.ReductionClosure`) is stated over `ChargedMachine.InP`.  Transporting this theorem
to that fence requires a poly-time *equivalence bridge* `ChargedMachine.InP ↔ ComposableMachine.InP` (mutual
simulation with polynomial overhead) — a standard but separate model-robustness result, NOT proved here.  Absent
that bridge, this file is a self-contained proof that a composition-friendly P is closed under reductions; it does
not by itself close the fence.

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

/-! ## Growth bounds and polynomial-clock closure -/

/-- A move advances the head by at most one cell. -/
theorem moveHead_le (h : ℕ) (m : Move) : moveHead h m ≤ h + 1 := by
  unfold moveHead; split_ifs <;> omega

/-- Writing pads the tape to `max (old length) (p+1)`. -/
theorem writeAt_length (tape : List Bool) (p : ℕ) (w : Bool) :
    (writeAt tape p w).length = max tape.length (p + 1) := by
  unfold writeAt
  rw [List.length_set, List.length_append, List.length_replicate]
  omega

/-- **Linear space growth.** After `t` steps from the forced initial config, the head is within `|x|+t`
and the tape within `|x|+t+1`.  (A right-move without a write can push the head one past the tape, so the
`+1` is genuine.)  This gives the polynomial bound on a transducer's output length. -/
theorem run_bounds (M : Machine) (x : List Bool) (t : ℕ) :
    (run M t (init M x)).hd ≤ x.length + t ∧
      (run M t (init M x)).tp.length ≤ x.length + t + 1 := by
  induction t with
  | zero => refine ⟨?_, ?_⟩ <;> simp only [run_zero, init] <;> omega
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [run_succ]
    set c := run M t (init M x) with hc
    by_cases hh : M.halt c.st = true
    · rw [step_of_halted M hh]; exact ⟨by omega, by omega⟩
    · simp only [Bool.not_eq_true] at hh
      have hstep : step M c =
          ⟨(M.δ c.st (c.tp.getD c.hd false)).1,
            moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
            (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
              | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
        unfold step; rw [hh]; rfl
      rw [hstep]
      refine ⟨?_, ?_⟩
      · exact le_trans (moveHead_le _ _) (by omega)
      · cases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with
        | none => simp only [hw]; omega
        | some w => simp only [hw, writeAt_length]; omega

/-- **Polynomial-clock closure.** If `Tf` is polynomially bounded (witnessed by `cf,kf`), then the composed
clock `Tf n + 1 + cg·(n + Tf n + 2)^kg` is polynomially bounded — a sum/composition of polynomials is a
polynomial.  This is exactly the clock the reduction-composition needs. -/
theorem polyBounded_comp_clock {Tf : ℕ → ℕ} (cf kf cg kg : ℕ)
    (hTf : ∀ n, Tf n ≤ cf * (n + 1) ^ kf) :
    PolyBounded (fun n => Tf n + 1 + cg * (n + Tf n + 2) ^ kg) := by
  refine ⟨(cf + 1) + cg * (cf + 3) ^ kg, max (max kf 1) ((max kf 1) * kg), fun n => ?_⟩
  have hA : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have e_one_K1 : 1 ≤ (n + 1) ^ (max kf 1) := Nat.one_le_pow _ _ hA
  have hTfK1 : Tf n ≤ cf * (n + 1) ^ (max kf 1) := by
    refine (hTf n).trans ?_; gcongr <;> first | exact hA | exact le_max_left kf 1
  have hn : n ≤ (n + 1) ^ (max kf 1) := by
    calc n ≤ n + 1 := Nat.le_succ n
      _ = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (max kf 1) := by gcongr <;> first | exact hA | exact le_max_right kf 1
  have hmid : n + Tf n + 2 ≤ (cf + 3) * (n + 1) ^ (max kf 1) := by
    have hexp : (cf + 3) * (n + 1) ^ (max kf 1)
        = cf * (n + 1) ^ (max kf 1) + (n + 1) ^ (max kf 1)
          + (n + 1) ^ (max kf 1) + (n + 1) ^ (max kf 1) := by ring
    rw [hexp]; omega
  have hpow : (n + Tf n + 2) ^ kg ≤ (cf + 3) ^ kg * (n + 1) ^ ((max kf 1) * kg) := by
    calc (n + Tf n + 2) ^ kg ≤ ((cf + 3) * (n + 1) ^ (max kf 1)) ^ kg := by gcongr
      _ = (cf + 3) ^ kg * (n + 1) ^ ((max kf 1) * kg) := by rw [Nat.mul_pow, ← pow_mul]
  have hpart1 : Tf n + 1 ≤ (cf + 1) * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) := by
    calc Tf n + 1 ≤ cf * (n + 1) ^ (max kf 1) + (n + 1) ^ (max kf 1) := by omega
      _ = (cf + 1) * (n + 1) ^ (max kf 1) := by ring
      _ ≤ (cf + 1) * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) :=
          Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right hA (le_max_left _ _))
  have hpart2 : cg * (n + Tf n + 2) ^ kg
      ≤ cg * (cf + 3) ^ kg * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) := by
    calc cg * (n + Tf n + 2) ^ kg
        ≤ cg * ((cf + 3) ^ kg * (n + 1) ^ ((max kf 1) * kg)) := by gcongr
      _ ≤ cg * ((cf + 3) ^ kg * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg))) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _)
            (Nat.pow_le_pow_right hA (le_max_right _ _)))
      _ = cg * (cf + 3) ^ kg * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) := by ring
  calc Tf n + 1 + cg * (n + Tf n + 2) ^ kg
      ≤ (cf + 1) * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg))
        + cg * (cf + 3) ^ kg * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) :=
        Nat.add_le_add hpart1 hpart2
    _ = ((cf + 1) + cg * (cf + 3) ^ kg) * (n + 1) ^ (max (max kf 1) ((max kf 1) * kg)) := by ring

/-! ## `ReductionClosure`: P is closed under polynomial many-one reductions -/

/-- **`ReductionClosure`.** If `L` poly-many-one reduces to `L'` and `L' ∈ P`, then `L ∈ P`.

The witness is `comp Mf Mg` (reducer `Mf`, decider `Mg`): run `Mf` on `x` until it first halts (time
`Nat.find`, `≤ Tf|x|`), producing `f x` on the tape (`run_bounds` ⇒ `|f x| ≤ |x| + Tf|x| + 1`); one control
step switches to `Mg` with the tape intact and head reset; then `Mg` decides `L'(f x) = L x`.  Phase-1/switch/
phase-2 give exact simulation; `run_stable` lifts the run to the polynomial clock
`Tf n + 1 + cg·(n + Tf n + 2)^kg`, shown polynomial by `polyBounded_comp_clock`.  No decision power is added —
only sequencing — so this is a genuine closure, not a vacuous one. -/
theorem reductionClosure {L L' : List Bool → Bool}
    (hred : PolyReduces L L') (hL' : InP L') : InP L := by
  obtain ⟨f, ⟨Mf, Tf, hTf, hMf⟩, hfL⟩ := hred
  obtain ⟨Mg, Tg, hTg, hMg⟩ := hL'
  obtain ⟨cf, kf, hcf⟩ := hTf
  obtain ⟨cg, kg, hcg⟩ := hTg
  refine ⟨comp Mf Mg, fun n => Tf n + 1 + cg * (n + Tf n + 2) ^ kg,
          polyBounded_comp_clock cf kf cg kg hcf, fun x => ?_⟩
  obtain ⟨hMfhalt, hMfout⟩ := hMf x
  obtain ⟨hMghalt, hMgdec⟩ := hMg (f x)
  -- syntactic (unfolded) forms of the halt/output facts
  have hMfhalt' : Mf.halt (run Mf (Tf x.length) (init Mf x)).st = true := hMfhalt
  have hMfout' : (run Mf (Tf x.length) (init Mf x)).tp = f x := hMfout
  have hMghalt' : Mg.halt (run Mg (Tg (f x).length) (init Mg (f x))).st = true := hMghalt
  have hMgdec' : Mg.accept (run Mg (Tg (f x).length) (init Mg (f x))).st = L' (f x) := hMgdec
  -- the first-halt time of `Mf`
  have hex : ∃ t, Mf.halt (run Mf t (init Mf x)).st = true := ⟨Tf x.length, hMfhalt'⟩
  have hspec : Mf.halt (run Mf (Nat.find hex) (init Mf x)).st = true := Nat.find_spec hex
  have hle : Nat.find hex ≤ Tf x.length := Nat.find_le hMfhalt'
  have hmin : ∀ s < Nat.find hex, Mf.halt (run Mf s (init Mf x)).st = false :=
    fun s hs => by simpa using Nat.find_min hex hs
  -- at the first halt, the tape holds `f x`
  have htp : (run Mf (Nat.find hex) (init Mf x)).tp = f x := by
    rw [← run_stable Mf x hle hspec]; exact hMfout'
  -- phase 1: mirror `Mf` up to the first halt
  have hp1 : run (comp Mf Mg) (Nat.find hex) (init (comp Mf Mg) x)
      = embedL Mf Mg (run Mf (Nat.find hex) (init Mf x)) := comp_phase1 Mf Mg x (Nat.find hex) hmin
  -- the switch step lands on `Mg`'s init config for `f x`
  have hsw : run (comp Mf Mg) (Nat.find hex + 1) (init (comp Mf Mg) x)
      = embedR Mf Mg (init Mg (f x)) := by
    rw [run_succ, hp1, comp_step_switch Mf Mg _ hspec, htp]; rfl
  -- phase 2: mirror `Mg`
  have hp2 : run (comp Mf Mg) (Nat.find hex + 1 + Tg (f x).length) (init (comp Mf Mg) x)
      = embedR Mf Mg (run Mg (Tg (f x).length) (init Mg (f x))) :=
    comp_phase2 Mf Mg x (Nat.find hex) (f x) (Tg (f x).length) hsw
  -- output length is polynomial
  have hmlen : (f x).length ≤ x.length + Tf x.length + 1 := by
    have hb := (run_bounds Mf x (Tf x.length)).2
    rw [hMfout'] at hb; exact hb
  have hTgm : Tg (f x).length ≤ cg * (x.length + Tf x.length + 2) ^ kg := by
    calc Tg (f x).length ≤ cg * ((f x).length + 1) ^ kg := hcg (f x).length
      _ ≤ cg * (x.length + Tf x.length + 2) ^ kg := by gcongr <;> omega
  -- the composition has halted by the switch-plus-`Mg` time, which is within the clock
  have ht0_halt : (comp Mf Mg).halt
      (run (comp Mf Mg) (Nat.find hex + 1 + Tg (f x).length) (init (comp Mf Mg) x)).st = true := by
    rw [hp2]; exact hMghalt'
  have ht0_le : Nat.find hex + 1 + Tg (f x).length
      ≤ Tf x.length + 1 + cg * (x.length + Tf x.length + 2) ^ kg := by omega
  refine ⟨?_, ?_⟩
  · show (comp Mf Mg).halt (run (comp Mf Mg)
        (Tf x.length + 1 + cg * (x.length + Tf x.length + 2) ^ kg) (init (comp Mf Mg) x)).st = true
    rw [run_stable (comp Mf Mg) x ht0_le ht0_halt]; exact ht0_halt
  · show (comp Mf Mg).accept (run (comp Mf Mg)
        (Tf x.length + 1 + cg * (x.length + Tf x.length + 2) ^ kg) (init (comp Mf Mg) x)).st = L x
    rw [run_stable (comp Mf Mg) x ht0_le ht0_halt, hp2]
    exact hMgdec'.trans (hfL x).symm

end PallLean.Paper93.DeepMath.PathB.ComposableMachine
