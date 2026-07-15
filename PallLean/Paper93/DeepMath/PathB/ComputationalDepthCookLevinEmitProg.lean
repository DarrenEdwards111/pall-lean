import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitReadX
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitTemplates

/-!
# Cook–Levin M2 emitter — the program emitter, and the first family (accept)

The tableau families' bodies are **interleavings**: fixed skeleton blocks alternating with counter
splices.  This file builds the universal engine for the straight-line case and instantiates it on the
first real family.

`progMachine prog` executes a hard-wired instruction list `prog : List (Option Bool)` against the layout
`unaryD v ++ encodeD out`: instruction `some b` appends the bit `b` to the doubled output (skip the
counter, seek the terminator, four-write snoc, reset); instruction `none` **splices the counter's value**
(`encodeNat v`) by the E3 marking discipline — mark a counter pair, seek to the output terminator, emit a
doubled `true`, reset; on exhaustion emit the closing `false` and **heal the counter**.  The instruction
pointer lives in the finite control (`Fin (|prog|+1)`).  **Top theorem** (`prog_run`): the machine halts
by itself at the explicit clock with tape **exactly** `unaryD v ++ encodeD (out ++ progOut prog v)`, the
counter preserved — where `progOut` is the evident denotation (`some b ↦ [b]`, `none ↦ encodeNat v`).

**The first family emitter falls out as an instantiation**: the accept family's single clause is
`encodeNat |acceptStates| · (encodeNat B · encodeNat q̂ · encodeNat 2 · [true])*` — a fixed skeleton with
`B` spliced (`encodeClause'_accept` of `...EmitTemplates`).  `acceptProg M` is that program;
`acceptProg_out` proves its denotation **is** the accept clause's coordinate encoding, and
`accept_family_run` runs the machine: the accept family of the tableau at time `v`, emitted by an actual
`ComposableMachine`, counter preserved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar

/-! ## The program denotation -/

/-- One instruction's output. -/
def instrOut (v : ℕ) : Option Bool → List Bool
  | some b => [b]
  | none => encodeNat v

/-- The whole program's output. -/
def progOut (prog : List (Option Bool)) (v : ℕ) : List Bool :=
  (prog.map (instrOut v)).flatten

/-- The first `n` instructions' output. -/
def progOutN (prog : List (Option Bool)) (v : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => progOutN prog v n ++ instrOut v (prog.getD n none)

theorem progOut_append (p1 p2 : List (Option Bool)) (v : ℕ) :
    progOut (p1 ++ p2) v = progOut p1 v ++ progOut p2 v := by
  simp [progOut, List.map_append]

theorem progOut_map_some (bits : List Bool) (v : ℕ) :
    progOut (bits.map some) v = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, progOut, List.flatten_cons] at ih ⊢
    rw [show instrOut v (some b) = [b] from rfl]
    rw [show ([b] : List Bool) ++ (List.map (instrOut v) (List.map some bs)).flatten
        = b :: (List.map (instrOut v) (List.map some bs)).flatten from rfl, ih]

theorem progOut_none (v : ℕ) : progOut [none] v = encodeNat v := by
  simp [progOut, instrOut]

/-- The staged and the whole denotations agree at full length. -/
theorem progOutN_full (prog : List (Option Bool)) (v : ℕ) :
    progOutN prog v prog.length = progOut prog v := by
  suffices h : ∀ n, n ≤ prog.length → progOutN prog v n = ((prog.take n).map (instrOut v)).flatten by
    rw [h prog.length (le_refl _), List.take_length]
    rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show progOutN prog v (n + 1) = progOutN prog v n ++ instrOut v (prog.getD n none)
        from rfl,
      ih (by omega), take_snoc_getD prog none n (by omega), List.map_append,
      List.flatten_append]
    simp

/-! ## The program machine

Control: `Fin 31 × Fin (|prog|+1) × Bool` — phase, instruction pointer, stored cell.  Phases: `0` the
instruction dispatch (a pure control step: `some` ⇒ the append track, `none` ⇒ the splice track,
exhausted ⇒ halt), `2/3` skip the counter, `4/5` seek the output terminator, `6–9` append the
instruction's bit (advance the pointer, reset), `10/11` find in the counter (mark ⇒ splice a `true`,
boundary ⇒ the closing `false`), `12/13`+`14/15` the splice seeks, `16–19` the doubled-`true` snoc,
`22/23` the final seek, `24–27` the doubled-`false` snoc, `28/29` heal the counter (done ⇒ advance the
pointer, reset), `30` = halt. -/

def progMachine (prog : List (Option Bool)) : Machine where
  State := Fin 31 × Fin (prog.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 30)
  δ := fun s b =>
    if s.1 = 0 then
      (if s.2.1.val < prog.length then
        (match prog.getD s.2.1.val none with
         | some _ => ((2, s.2.1, s.2.2), none, 2)
         | none => ((10, s.2.1, s.2.2), none, 2))
       else ((30, s.2.1, s.2.2), none, 2))
    else if s.1 = 2 then ((3, s.2.1, b), none, 1)
    else if s.1 = 3 then
      (if s.2.2 then ((2, s.2.1, s.2.2), none, 1)
       else (if b then ((4, s.2.1, s.2.2), none, 1) else ((30, s.2.1, s.2.2), none, 2)))
    else if s.1 = 4 then ((5, s.2.1, b), none, 1)
    else if s.1 = 5 then
      (if b = s.2.2 then ((4, s.2.1, s.2.2), none, 1) else ((6, s.2.1, s.2.2), none, 0))
    else if s.1 = 6 then ((7, s.2.1, s.2.2), some ((prog.getD s.2.1.val none).getD false), 1)
    else if s.1 = 7 then ((8, s.2.1, s.2.2), some ((prog.getD s.2.1.val none).getD false), 1)
    else if s.1 = 8 then ((9, s.2.1, s.2.2), some false, 1)
    else if s.1 = 9 then
      (if h : s.2.1.val + 1 < prog.length + 1 then
        ((0, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((30, s.2.1, s.2.2), some true, 2))
    else if s.1 = 10 then ((11, s.2.1, b), none, 1)
    else if s.1 = 11 then
      (if s.2.2 then
        (if b then ((12, s.2.1, s.2.2), some false, 1) else ((10, s.2.1, s.2.2), none, 1))
       else (if b then ((22, s.2.1, s.2.2), none, 1) else ((30, s.2.1, s.2.2), none, 2)))
    else if s.1 = 12 then ((13, s.2.1, b), none, 1)
    else if s.1 = 13 then
      (if b = s.2.2 then ((12, s.2.1, s.2.2), none, 1) else ((14, s.2.1, s.2.2), none, 1))
    else if s.1 = 14 then ((15, s.2.1, b), none, 1)
    else if s.1 = 15 then
      (if b = s.2.2 then ((14, s.2.1, s.2.2), none, 1) else ((16, s.2.1, s.2.2), none, 0))
    else if s.1 = 16 then ((17, s.2.1, s.2.2), some true, 1)
    else if s.1 = 17 then ((18, s.2.1, s.2.2), some true, 1)
    else if s.1 = 18 then ((19, s.2.1, s.2.2), some false, 1)
    else if s.1 = 19 then ((10, s.2.1, s.2.2), some true, 3)
    else if s.1 = 22 then ((23, s.2.1, b), none, 1)
    else if s.1 = 23 then
      (if b = s.2.2 then ((22, s.2.1, s.2.2), none, 1) else ((24, s.2.1, s.2.2), none, 0))
    else if s.1 = 24 then ((25, s.2.1, s.2.2), some false, 1)
    else if s.1 = 25 then ((26, s.2.1, s.2.2), some false, 1)
    else if s.1 = 26 then ((27, s.2.1, s.2.2), some false, 1)
    else if s.1 = 27 then ((28, s.2.1, s.2.2), some true, 3)
    else if s.1 = 28 then ((29, s.2.1, b), none, 1)
    else if s.1 = 29 then
      (if s.2.2 then
        (if b then ((30, s.2.1, s.2.2), none, 2) else ((28, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < prog.length + 1 then
                ((0, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((30, s.2.1, s.2.2), none, 2))
             else ((30, s.2.1, s.2.2), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_pg (prog : List (Option Bool)) (t : List Bool) :
    init (progMachine prog) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

/-! ### Step and pair-step lemmas -/

section Steps
variable {prog : List (Option Bool)} {idx : Fin (prog.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem pg_dispatch_some {b : Bool} (h : idx.val < prog.length)
    (hp : prog.getD idx.val none = some b) :
    run (progMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(2, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : prog[(idx : ℕ)]'h = some b := by
    rwa [List.getD_eq_getElem prog none h] at hp
  simp [step, progMachine, moveHead, h, hp']

theorem pg_dispatch_none (h : idx.val < prog.length)
    (hp : prog.getD idx.val none = none) :
    run (progMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(10, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : prog[(idx : ℕ)]'h = none := by
    rwa [List.getD_eq_getElem prog none h] at hp
  simp [step, progMachine, moveHead, h, hp']

theorem pg_dispatch_halt (h : ¬(idx.val < prog.length)) :
    run (progMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(30, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, progMachine, moveHead, h]

theorem pg_skipW (h1 : T.getD p false = true) :
    run (progMachine prog) 2 ⟨(2, idx, s), p, T⟩ = ⟨(2, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, progMachine, moveHead]; rfl

theorem pg_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(2, idx, s), p, T⟩ = ⟨(4, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_seekO (h : T.getD p false = T.getD (p + 1) false) :
    run (progMachine prog) 2 ⟨(4, idx, s), p, T⟩ = ⟨(4, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(4, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_detectO (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(4, idx, s), p, T⟩ = ⟨(6, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(4, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

/-- The append instruction's four writes, advancing the instruction pointer. -/
theorem pg_four_append (h : idx.val + 1 < prog.length + 1) :
    run (progMachine prog) 4 ⟨(6, idx, s), p, T⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p ((prog.getD idx.val none).getD false))
            (p + 1) ((prog.getD idx.val none).getD false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e6 : step (progMachine prog) ⟨(6, idx, s), p, T⟩
      = ⟨(7, idx, s), p + 1, writeAt T p ((prog.getD idx.val none).getD false)⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  have e7 : ∀ p' T', step (progMachine prog) ⟨(7, idx, s), p', T'⟩
      = ⟨(8, idx, s), p' + 1, writeAt T' p' ((prog.getD idx.val none).getD false)⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e8 : ∀ p' T', step (progMachine prog) ⟨(8, idx, s), p', T'⟩
      = ⟨(9, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e9 : ∀ p' T', step (progMachine prog) ⟨(9, idx, s), p', T'⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'
    simp [step, progMachine, moveHead, h]
  rw [e6, e7, e8, e9]

theorem pg_skipJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (progMachine prog) 2 ⟨(10, idx, s), p, T⟩ = ⟨(10, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(10, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(10, idx, s), p, T⟩
      = ⟨(12, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(10, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(10, idx, s), p, T⟩ = ⟨(22, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(10, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_seekA (h : T.getD p false = T.getD (p + 1) false) :
    run (progMachine prog) 2 ⟨(12, idx, s), p, T⟩ = ⟨(12, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(12, idx, s), p, T⟩
      = ⟨(13, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_crossA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(12, idx, s), p, T⟩ = ⟨(14, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(12, idx, s), p, T⟩
      = ⟨(13, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progMachine, moveHead, h2']

theorem pg_seekB (h : T.getD p false = T.getD (p + 1) false) :
    run (progMachine prog) 2 ⟨(14, idx, s), p, T⟩ = ⟨(14, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(14, idx, s), p, T⟩
      = ⟨(15, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_detectB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(14, idx, s), p, T⟩ = ⟨(16, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(14, idx, s), p, T⟩
      = ⟨(15, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem pg_four_true :
    run (progMachine prog) 4 ⟨(16, idx, s), p, T⟩
      = ⟨(10, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e16 : step (progMachine prog) ⟨(16, idx, s), p, T⟩
      = ⟨(17, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  have e17 : ∀ p' T', step (progMachine prog) ⟨(17, idx, s), p', T'⟩
      = ⟨(18, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e18 : ∀ p' T', step (progMachine prog) ⟨(18, idx, s), p', T'⟩
      = ⟨(19, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e19 : ∀ p' T', step (progMachine prog) ⟨(19, idx, s), p', T'⟩
      = ⟨(10, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  rw [e16, e17, e18, e19]

theorem pg_seekF (h : T.getD p false = T.getD (p + 1) false) :
    run (progMachine prog) 2 ⟨(22, idx, s), p, T⟩ = ⟨(22, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(22, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

theorem pg_detectF (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(22, idx, s), p, T⟩ = ⟨(24, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(22, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem pg_four_false :
    run (progMachine prog) 4 ⟨(24, idx, s), p, T⟩
      = ⟨(28, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e24 : step (progMachine prog) ⟨(24, idx, s), p, T⟩
      = ⟨(25, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  have e25 : ∀ p' T', step (progMachine prog) ⟨(25, idx, s), p', T'⟩
      = ⟨(26, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e26 : ∀ p' T', step (progMachine prog) ⟨(26, idx, s), p', T'⟩
      = ⟨(27, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  have e27 : ∀ p' T', step (progMachine prog) ⟨(27, idx, s), p', T'⟩
      = ⟨(28, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progMachine, moveHead]; rfl
  rw [e24, e25, e26, e27]

theorem pg_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (progMachine prog) 2 ⟨(28, idx, s), p, T⟩
      = ⟨(28, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(28, idx, s), p, T⟩
      = ⟨(29, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2]

/-- The heal completes: advance the instruction pointer and reset. -/
theorem pg_doneHeal (h : idx.val + 1 < prog.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progMachine prog) 2 ⟨(28, idx, s), p, T⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progMachine prog) ⟨(28, idx, s), p, T⟩
      = ⟨(29, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progMachine, moveHead, h2, h]

end Steps

/-! ### Scan run-invariants -/

theorem pg_skipWs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (progMachine prog) (2 * k) ⟨(2, idx, s), q, T⟩
      = ⟨(2, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_skipW (h k (by omega))]
    rfl

theorem pg_seekOs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progMachine prog) (2 * k) ⟨(4, idx, s), q, T⟩
      = ⟨(4, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_seekO (h k (by omega))]
    rfl

theorem pg_skipJs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (progMachine prog) (2 * k) ⟨(10, idx, s), q, T⟩
      = ⟨(10, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_skipJ hk.1 hk.2]
    rfl

theorem pg_seekAs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progMachine prog) (2 * k) ⟨(12, idx, s), q, T⟩
      = ⟨(12, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_seekA (h k (by omega))]
    rfl

theorem pg_seekBs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progMachine prog) (2 * k) ⟨(14, idx, s), q, T⟩
      = ⟨(14, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_seekB (h k (by omega))]
    rfl

theorem pg_seekFs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progMachine prog) (2 * k) ⟨(22, idx, s), q, T⟩
      = ⟨(22, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pg_seekF (h k (by omega))]
    rfl

/-- The counter-heal invariant. -/
theorem pg_healJs (prog : List (Option Bool)) (v : ℕ) (E : List Bool)
    (idx : Fin (prog.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (progMachine prog) (2 * i) ⟨(28, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(28, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      pg_healJ (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The instruction lemmas -/

/-- **An append instruction** (`prog[idx] = some b`): dispatch, cross the counter, seek the output
terminator, snoc the doubled bit, advance the pointer. -/
theorem pg_instr_append (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (h : idx.val < prog.length) {b : Bool} (hp : prog.getD idx.val none = some b)
    (v : ℕ) (OUT : List Bool) (s : Bool) :
    run (progMachine prog) (2 * v + 2 * OUT.length + 9)
      ⟨(0, idx, s), 0, cntT v 0 ++ encodeD OUT⟩
      = ⟨(0, ⟨idx.val + 1, by omega⟩, false), 0, cntT v 0 ++ encodeD (OUT ++ [b])⟩ := by
  have hcb : (cntT v 0).length = 2 * v + 2 := cntT_length v 0 (by omega)
  have st0 := pg_dispatch_some (s := s) (p := 0) (T := cntT v 0 ++ encodeD OUT) h hp
  have st1 := pg_skipWs prog (cntT v 0 ++ encodeD OUT) 0 v idx s
    (fun i hi => by simpa using cntE_lo v 0 _ i (by omega) hi)
  simp only [Nat.zero_add] at st1
  have st2 := pg_crossW (prog := prog) (idx := idx) (s := if v = 0 then s else true) (p := 2 * v)
    (T := cntT v 0 ++ encodeD OUT)
    (cntE_cm_lo v 0 _ (by omega)) (cntE_cm_hi v 0 _ (by omega))
  have st3 := pg_seekOs prog (cntT v 0 ++ encodeD OUT) (2 * v + 2) OUT.length idx false
    (fun i hi => preD_data_eq (cntT v 0) OUT (2 * v + 2) i hcb hi)
  have st4 := pg_detectO (prog := prog) (idx := idx)
    (s := storedD (cntT v 0 ++ encodeD OUT) (2 * v + 2) false OUT.length)
    (p := 2 * v + 2 + 2 * OUT.length)
    (preD_mark_lo (cntT v 0) OUT (2 * v + 2) hcb)
    (preD_mark_hi (cntT v 0) OUT (2 * v + 2) hcb)
  have st5 := pg_four_append (prog := prog) (idx := idx) (s := false)
    (p := 2 * v + 2 + 2 * OUT.length) (T := cntT v 0 ++ encodeD OUT) (by omega)
  rw [hp] at st5
  simp only [Option.getD_some] at st5
  rw [writes_snoc (cntT v 0) OUT (2 * v + 2) hcb b] at st5
  rw [show 2 * v + 2 * OUT.length + 9
      = 1 + (2 * v + (2 + (2 * OUT.length + (2 + 4)))) from by omega,
    run_add, st0, run_add, st1, run_add, st2, run_add, st3, run_add, st4, st5]

/-! ### The splice instruction -/

/-- The splice sub-round clock. -/
def pgSpRounds (v L : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => pgSpRounds v L j + (2 * v + 2 * (L + j) + 8)

/-- One splice sub-round: mark the counter's pair `j`, seek out, emit a doubled `true`. -/
theorem pg_sp_round (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (v j : ℕ) (hj : j < v) (OUT : List Bool) (s : Bool) :
    run (progMachine prog) (2 * v + 2 * (OUT.length + j) + 8)
      ⟨(10, idx, s), 0, cntT v j ++ encodeD (OUT ++ List.replicate j true)⟩
      = ⟨(10, idx, false), 0,
          cntT v (j + 1) ++ encodeD (OUT ++ List.replicate (j + 1) true)⟩ := by
  have hcb1 : (cntT v (j + 1)).length = 2 * v + 2 := cntT_length v (j + 1) (by omega)
  have hlen : (OUT ++ List.replicate j true).length = OUT.length + j := by
    rw [List.length_append, List.length_replicate]
  have r1 := pg_skipJs prog (cntT v j ++ encodeD (OUT ++ List.replicate j true)) 0 j idx s
    (fun i hi => ⟨by simpa using cntE_mark_lo v j _ i hi,
                  by simpa using cntE_mark_hi v j _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := pg_markJ (prog := prog) (idx := idx) (s := if j = 0 then s else true) (p := 2 * j)
    (T := cntT v j ++ encodeD (OUT ++ List.replicate j true))
    (cntE_data v j _ (2 * j) (by omega) (by omega) (by omega))
    (cntE_data v j _ (2 * j + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark v j _ hj] at r2
  have r3 := pg_seekAs prog
    (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)) (2 * j + 2) (v - j - 1) idx true
    (fun i hi => by
      rw [cntE_data v (j + 1) _ (2 * j + 2 + 2 * i) (by omega) (by omega) (by omega),
        cntE_data v (j + 1) _ (2 * j + 2 + 2 * i + 1) (by omega) (by omega) (by omega)])
  rw [show 2 * j + 2 + 2 * (v - j - 1) = 2 * v from by omega] at r3
  have r4 := pg_crossA (prog := prog) (idx := idx)
    (s := storedD (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))
      (2 * j + 2) true (v - j - 1))
    (p := 2 * v) (T := cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))
    (cntE_cm_lo v (j + 1) (encodeD (OUT ++ List.replicate j true)) (by omega))
    (cntE_cm_hi v (j + 1) (encodeD (OUT ++ List.replicate j true)) (by omega))
  have r5 := pg_seekBs prog
    (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)) (2 * v + 2)
    (OUT.length + j) idx false
    (fun i hi => preD_data_eq (cntT v (j + 1)) (OUT ++ List.replicate j true)
      (2 * v + 2) i hcb1 (by omega))
  have hm1 := preD_mark_lo (cntT v (j + 1)) (OUT ++ List.replicate j true) (2 * v + 2) hcb1
  have hm2 := preD_mark_hi (cntT v (j + 1)) (OUT ++ List.replicate j true) (2 * v + 2) hcb1
  rw [hlen] at hm1 hm2
  have r6 := pg_detectB (prog := prog) (idx := idx)
    (s := storedD (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))
      (2 * v + 2) false (OUT.length + j))
    (p := 2 * v + 2 + 2 * (OUT.length + j)) hm1 hm2
  have hsn := writes_snoc (cntT v (j + 1)) (OUT ++ List.replicate j true) (2 * v + 2)
    hcb1 true
  rw [hlen, List.append_assoc,
    show (List.replicate j true ++ [true] : List Bool) = List.replicate (j + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have r7 := pg_four_true (prog := prog) (idx := idx) (s := false)
    (p := 2 * v + 2 + 2 * (OUT.length + j))
    (T := cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))
  rw [hsn] at r7
  rw [show 2 * v + 2 * (OUT.length + j) + 8
      = 2 * j + (2 + (2 * (v - j - 1) + (2 + (2 * (OUT.length + j) + (2 + 4)))))
      from by omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6, r7]

/-- The splice sub-rounds invariant. -/
theorem pg_sp_rounds (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (v : ℕ) (OUT : List Bool) (j : ℕ) (hj : j ≤ v) (s : Bool) :
    run (progMachine prog) (pgSpRounds v OUT.length j)
      ⟨(10, idx, s), 0, cntT v 0 ++ encodeD OUT⟩
      = ⟨(10, idx, if j = 0 then s else false), 0,
          cntT v j ++ encodeD (OUT ++ List.replicate j true)⟩ := by
  induction j with
  | zero => simp only [pgSpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show pgSpRounds v OUT.length (j + 1)
        = pgSpRounds v OUT.length j + (2 * v + 2 * (OUT.length + j) + 8) from rfl,
      run_add, ih (by omega), pg_sp_round prog idx v j (by omega) OUT _, if_neg (by omega)]

/-- The splice instruction's full clock. -/
def pgSpliceCost (v L : ℕ) : ℕ :=
  1 + (pgSpRounds v L v + (2 * v + (2 + (2 * (L + v) + (2 + (4 + (2 * v + 2)))))))

/-- **A splice instruction** (`prog[idx] = none`): emit `encodeNat v` by the marking discipline, close
with the doubled `false`, heal the counter, advance the pointer. -/
theorem pg_instr_splice (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (h : idx.val < prog.length) (hp : prog.getD idx.val none = none)
    (v : ℕ) (OUT : List Bool) (s : Bool) :
    run (progMachine prog) (pgSpliceCost v OUT.length)
      ⟨(0, idx, s), 0, cntT v 0 ++ encodeD OUT⟩
      = ⟨(0, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT v 0 ++ encodeD (OUT ++ encodeNat v)⟩ := by
  have hcbv : (cntT v v).length = 2 * v + 2 := cntT_length v v (le_refl v)
  have hlen2 : (OUT ++ List.replicate v true).length = OUT.length + v := by
    rw [List.length_append, List.length_replicate]
  have d0 := pg_dispatch_none (s := s) (p := 0) (T := cntT v 0 ++ encodeD OUT) h hp
  have d1 := pg_sp_rounds prog idx v OUT v (le_refl v) s
  have d2 := pg_skipJs prog (cntT v v ++ encodeD (OUT ++ List.replicate v true)) 0 v idx
    (if v = 0 then s else false)
    (fun i hi => ⟨by simpa using cntE_mark_lo v v _ i hi,
                  by simpa using cntE_mark_hi v v _ i hi⟩)
  simp only [Nat.zero_add] at d2
  have d3 := pg_doneJ (prog := prog) (idx := idx) (s := if v = 0 then (if v = 0 then s else false) else true) (p := 2 * v)
    (T := cntT v v ++ encodeD (OUT ++ List.replicate v true))
    (cntE_cm_lo v v _ (le_refl v)) (cntE_cm_hi v v _ (le_refl v))
  have d4 := pg_seekFs prog
    (cntT v v ++ encodeD (OUT ++ List.replicate v true)) (2 * v + 2)
    (OUT.length + v) idx false
    (fun i hi => preD_data_eq (cntT v v) (OUT ++ List.replicate v true)
      (2 * v + 2) i hcbv (by omega))
  have hm1 := preD_mark_lo (cntT v v) (OUT ++ List.replicate v true) (2 * v + 2) hcbv
  have hm2 := preD_mark_hi (cntT v v) (OUT ++ List.replicate v true) (2 * v + 2) hcbv
  rw [hlen2] at hm1 hm2
  have d5 := pg_detectF (prog := prog) (idx := idx)
    (s := storedD (cntT v v ++ encodeD (OUT ++ List.replicate v true))
      (2 * v + 2) false (OUT.length + v))
    (p := 2 * v + 2 + 2 * (OUT.length + v)) hm1 hm2
  have hsn := writes_snoc (cntT v v) (OUT ++ List.replicate v true) (2 * v + 2) hcbv false
  rw [hlen2, List.append_assoc,
    show (List.replicate v true ++ [false] : List Bool) = encodeNat v from rfl] at hsn
  have d6 := pg_four_false (prog := prog) (idx := idx) (s := false)
    (p := 2 * v + 2 + 2 * (OUT.length + v))
    (T := cntT v v ++ encodeD (OUT ++ List.replicate v true))
  rw [hsn] at d6
  have d7 := pg_healJs prog v (encodeD (OUT ++ encodeNat v)) idx false v (le_refl v)
  have d8 := pg_doneHeal (prog := prog) (idx := idx)
    (s := if v = 0 then false else true) (p := 2 * v)
    (T := hlT v v ++ encodeD (OUT ++ encodeNat v)) (by omega)
    (hlE_cm_lo v _) (hlE_cm_hi v _)
  rw [show pgSpliceCost v OUT.length
      = 1 + (pgSpRounds v OUT.length v
          + (2 * v + (2 + (2 * (OUT.length + v) + (2 + (4 + (2 * v + 2))))))) from rfl,
    run_add, d0, run_add, d1, run_add, d2, run_add, d3, run_add, d4, run_add, d5, run_add,
    d6, ← hlT_zero, run_add, d7, d8, hlT_last, ← cntT_zero]

/-! ## The program induction and the top theorem -/

/-- One instruction's clock (the output grown by the preceding instructions). -/
def pgInstrCost (prog : List (Option Bool)) (v L : ℕ) (n : ℕ) : ℕ :=
  match prog.getD n none with
  | some _ => 2 * v + 2 * (L + (progOutN prog v n).length) + 9
  | none => pgSpliceCost v (L + (progOutN prog v n).length)

/-- The cumulative clock over the first `n` instructions. -/
def pgClockN (prog : List (Option Bool)) (v L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pgClockN prog v L n + pgInstrCost prog v L n

/-- **The instruction invariant**: `n` instructions executed, their denotation appended. -/
theorem pg_run_instrs (prog : List (Option Bool)) (v : ℕ) (out : List Bool) (n : ℕ)
    (hn : n ≤ prog.length) (s : Bool) :
    run (progMachine prog) (pgClockN prog v out.length n)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT v 0 ++ encodeD out⟩
      = ⟨(0, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT v 0 ++ encodeD (out ++ progOutN prog v n)⟩ := by
  induction n with
  | zero => simp only [pgClockN]; rw [run_zero]; simp [progOutN]
  | succ n ih =>
    rw [show pgClockN prog v out.length (n + 1)
        = pgClockN prog v out.length n + pgInstrCost prog v out.length n from rfl,
      run_add, ih (by omega)]
    cases hp : prog.getD n none with
    | none =>
      have hin := pg_instr_splice prog ⟨n, by omega⟩
        (show n < prog.length from by omega) hp v (out ++ progOutN prog v n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN prog v n ++ encodeNat v = progOutN prog v (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [pgInstrCost, hp]
      rw [hin]
      simp
    | some b =>
      have hin := pg_instr_append prog ⟨n, by omega⟩
        (show n < prog.length from by omega) hp v (out ++ progOutN prog v n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN prog v n ++ [b] = progOutN prog v (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [pgInstrCost, hp]
      rw [hin]
      simp

/-- The whole program's clock: all instructions plus the halting dispatch. -/
def pgClock (prog : List (Option Bool)) (v L : ℕ) : ℕ :=
  pgClockN prog v L prog.length + 1

/-- **The program emitter runs to completion.**  On `unaryD v ++ encodeD out` the machine halts by itself
at the explicit clock with tape **exactly** `unaryD v ++ encodeD (out ++ progOut prog v)` — the program's
denotation appended doubled, the counter preserved. -/
theorem prog_run (prog : List (Option Bool)) (v : ℕ) (out : List Bool) :
    run (progMachine prog) (pgClock prog v out.length)
      (init (progMachine prog) (unaryD v ++ encodeD out))
      = ⟨(30, ⟨prog.length, Nat.lt_succ_self _⟩, false), 0,
          unaryD v ++ encodeD (out ++ progOut prog v)⟩ := by
  rw [init_pg, ← cntT_zero]
  simp only [pgClock]
  rw [run_add, pg_run_instrs prog v out prog.length (le_refl _) false, ite_self,
    pg_dispatch_halt (Nat.lt_irrefl _), progOutN_full, cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem prog_halted (prog : List (Option Bool)) (v : ℕ) (out : List Bool) :
    (progMachine prog).halt
      (run (progMachine prog) (pgClock prog v out.length)
        (init (progMachine prog) (unaryD v ++ encodeD out))).st = true := by
  rw [prog_run]; rfl

/-- **The program emitter's output.** -/
theorem prog_output (prog : List (Option Bool)) (v : ℕ) (out : List Bool) :
    (run (progMachine prog) (pgClock prog v out.length)
      (init (progMachine prog) (unaryD v ++ encodeD out))).tp
      = unaryD v ++ encodeD (out ++ progOut prog v) := by
  rw [prog_run]

/-! ## Polynomial clock bounds -/

theorem progOutN_length_le (prog : List (Option Bool)) (v n : ℕ) :
    (progOutN prog v n).length ≤ n * (v + 1) := by
  induction n with
  | zero => simp [progOutN]
  | succ n ih =>
    rw [show progOutN prog v (n + 1) = progOutN prog v n ++ instrOut v (prog.getD n none)
        from rfl, List.length_append]
    have hone : (instrOut v (prog.getD n none)).length ≤ v + 1 := by
      cases prog.getD n none with
      | none => rw [show instrOut v none = encodeNat v from rfl, encodeNat_length]
      | some b => simp [instrOut]
    calc (progOutN prog v n).length + (instrOut v (prog.getD n none)).length
        ≤ n * (v + 1) + (v + 1) := Nat.add_le_add ih hone
      _ = (n + 1) * (v + 1) := by ring

theorem pgSpRounds_mono (v : ℕ) {L1 L2 : ℕ} (h : L1 ≤ L2) (j : ℕ) :
    pgSpRounds v L1 j ≤ pgSpRounds v L2 j := by
  induction j with
  | zero => exact le_refl _
  | succ j ih => exact Nat.add_le_add ih (by omega)

theorem pgSpliceCost_mono (v : ℕ) {L1 L2 : ℕ} (h : L1 ≤ L2) :
    pgSpliceCost v L1 ≤ pgSpliceCost v L2 := by
  have := pgSpRounds_mono v h v
  simp only [pgSpliceCost]
  omega

theorem pgSpRounds_le (v L j : ℕ) (hj : j ≤ v) :
    pgSpRounds v L j ≤ j * (2 * v + 2 * (L + v) + 8) := by
  induction j with
  | zero => simp [pgSpRounds]
  | succ j ih =>
    calc pgSpRounds v L (j + 1)
        = pgSpRounds v L j + (2 * v + 2 * (L + j) + 8) := rfl
      _ ≤ j * (2 * v + 2 * (L + v) + 8) + (2 * v + 2 * (L + v) + 8) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (j + 1) * (2 * v + 2 * (L + v) + 8) := by ring

/-- The splice clock is quadratic. -/
theorem pgSpliceCost_le (v L : ℕ) :
    pgSpliceCost v L ≤ v * (2 * v + 2 * (L + v) + 8) + (6 * v + 2 * L + 11) := by
  have := pgSpRounds_le v L v (le_refl v)
  simp only [pgSpliceCost]
  omega

theorem pgInstrCost_le (prog : List (Option Bool)) (v L n : ℕ) (hn : n ≤ prog.length) :
    pgInstrCost prog v L n
      ≤ pgSpliceCost v (L + prog.length * (v + 1))
          + (2 * v + 2 * (L + prog.length * (v + 1)) + 9) := by
  have hlen : (progOutN prog v n).length ≤ prog.length * (v + 1) :=
    le_trans (progOutN_length_le prog v n) (Nat.mul_le_mul_right _ hn)
  cases hp : prog.getD n none with
  | none =>
    simp only [pgInstrCost, hp]
    exact le_trans (pgSpliceCost_mono v (by omega)) (Nat.le_add_right _ _)
  | some b =>
    simp only [pgInstrCost, hp]
    omega

theorem pgClockN_le (prog : List (Option Bool)) (v L n : ℕ) (hn : n ≤ prog.length) :
    pgClockN prog v L n
      ≤ n * (pgSpliceCost v (L + prog.length * (v + 1))
          + (2 * v + 2 * (L + prog.length * (v + 1)) + 9)) := by
  induction n with
  | zero => simp [pgClockN]
  | succ n ih =>
    calc pgClockN prog v L (n + 1)
        = pgClockN prog v L n + pgInstrCost prog v L n := rfl
      _ ≤ n * (pgSpliceCost v (L + prog.length * (v + 1))
            + (2 * v + 2 * (L + prog.length * (v + 1)) + 9))
          + (pgSpliceCost v (L + prog.length * (v + 1))
            + (2 * v + 2 * (L + prog.length * (v + 1)) + 9)) :=
          Nat.add_le_add (ih (by omega)) (pgInstrCost_le prog v L n (by omega))
      _ = (n + 1) * (pgSpliceCost v (L + prog.length * (v + 1))
            + (2 * v + 2 * (L + prog.length * (v + 1)) + 9)) := by ring

/-- **The program clock is polynomial**: linear in `|prog|` times the (quadratic) per-instruction cap. -/
theorem pgClock_le (prog : List (Option Bool)) (v L : ℕ) :
    pgClock prog v L
      ≤ prog.length * (pgSpliceCost v (L + prog.length * (v + 1))
          + (2 * v + 2 * (L + prog.length * (v + 1)) + 9)) + 1 := by
  have := pgClockN_le prog v L prog.length (le_refl _)
  simp only [pgClock]
  omega

/-! ## The first family: accept

The accept family's single clause — the at-least-one over the accepting-state indices at the final time —
as a program: its fixed skeleton (`encodeClause'_accept` of `...EmitTemplates`) with the time value
spliced at each literal. -/

/-- The accept clause as an emitter program: literal count, then per accepting state a splice of the time
counter followed by the fixed coordinate tail. -/
noncomputable def acceptProg (M : Machine) : List (Option Bool) :=
  (encodeNat (acceptStates M).length).map some
    ++ ((acceptStates M).map
          (fun q => none :: (encodeNat q.val ++ (encodeNat 2 ++ [true])).map some)).flatten

theorem progOut_flatten (l : List (List (Option Bool))) (v : ℕ) :
    progOut l.flatten v = (l.map (fun p => progOut p v)).flatten := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatten_cons, progOut_append, ih, List.map_cons, List.flatten_cons]

theorem progOut_cons_none (p : List (Option Bool)) (v : ℕ) :
    progOut (none :: p) v = encodeNat v ++ progOut p v := rfl

/-- **The accept program's denotation is the accept clause's encoding** (at any time value `v`). -/
theorem acceptProg_out (M : Machine) (v : ℕ) :
    progOut (acceptProg M) v
      = encodeClause' (atLeastOne ((acceptStates M).map (fun q => stateVar v q.val))) := by
  rw [encodeClause'_accept M v, acceptProg, progOut_append, progOut_map_some, progOut_flatten,
    List.map_map]
  congr 2
  apply List.map_congr_left
  intro q hq
  show progOut (none :: (encodeNat q.val ++ (encodeNat 2 ++ [true])).map some) v = _
  rw [progOut_cons_none, progOut_map_some]

/-- **THE FIRST FAMILY EMITTER.**  `progMachine (acceptProg M)` — an actual `ComposableMachine` — halts by
itself at its explicit polynomial clock having appended **exactly** the accept family's clause encoding for
time value `v` (the counter's content) to the output, counter preserved. -/
theorem accept_family_run (M : Machine) (v : ℕ) (out : List Bool) :
    run (progMachine (acceptProg M)) (pgClock (acceptProg M) v out.length)
      (init (progMachine (acceptProg M)) (unaryD v ++ encodeD out))
      = ⟨(30, ⟨(acceptProg M).length, Nat.lt_succ_self _⟩, false), 0,
          unaryD v ++ encodeD (out
            ++ encodeClause' (atLeastOne ((acceptStates M).map
                 (fun q => stateVar v q.val))))⟩ := by
  rw [prog_run, acceptProg_out]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg