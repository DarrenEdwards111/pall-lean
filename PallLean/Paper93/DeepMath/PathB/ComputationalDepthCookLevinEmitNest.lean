import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRange

/-!
# Cook–Levin M2 emitter, E4 (iii) — the nested two-counter loop

Third brick of E4: **nesting**.  `nestMachine bits` runs `for t in range B: for p in range P: append bits`
— two counted-loop harnesses (E4 (i)) composed, the outer round's body being the inner loop's **full run**,
including the inner finale.  This is the shape of every tableau family with two index coordinates (tape,
dynamics, write), and the static-address layout of E4 (ii) is what makes it possible: the three regions —
outer bound `cntT B t`, inner bound `cntT P i`, doubled output — never move.

The nesting-specific mechanics proved here:

* **the outer body is an inner loop**: the outer round marks its bound pair (resetting), then the inner
  harness runs its `P` rounds *and its own finale* — the inner bound's restore pass runs once per outer
  round, handing the next outer round a pristine `cntT P 0`.  Bound preservation, proved for the standalone
  harness, is exactly what re-runnability of the inner loop requires;
* **two-boundary seeks from inside the inner region**: the emit seek crosses the inner bound's remaining
  pairs and its `01` boundary, then the output data, to the output terminator (the finite control counts
  the crossings);
* **generic-output round lemmas**: each round lemma is stated over an arbitrary accumulated output `OUT`,
  so all block-count products (`(tP+i)·|bits|`) appear only in the clock recursions, never in the tape
  reasoning.

Everything tape-level is reused (`cntT`/`cntE`, `hlT`/`hlE`, `preD2_*`, `writes_snoc2`, `liftJ`,
`writeAt_append_right`, `blkRep`); the machine layer is the practiced mirror.  **Top theorem**
(`nest_run`/`nest_halted`): on `unaryD B ++ (unaryD P ++ encodeD out)` the machine halts by itself at the
explicit clock `nestClock` (explicit polynomial bound `nestClock_le`) with tape **exactly**
`unaryD B ++ (unaryD P ++ encodeD (out ++ blkRep bits (B * P)))` — the `B·P`-fold block emission, both
bounds restored.  Remaining for the family instantiations: live loop variables in the body (E4 (ii)'s
splice/increment) and the inner-variable zeroing pass.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange

/-! ## Block-count arithmetic -/

theorem blkRep_add (bits : List Bool) (a b : ℕ) :
    blkRep bits (a + b) = blkRep bits a ++ blkRep bits b := by
  induction b with
  | zero => simp [blkRep]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from by omega]
    show blkRep bits (a + b) ++ bits = _
    rw [ih, List.append_assoc]
    rfl

/-! ## The nested-loop machine

Control: `Fin 21 × Fin (|bits|+1) × Bool` — phase, ROM index, stored low cell.  Phases: `0/1` find in the
outer bound (mark + reset ⇒ inner loop, boundary ⇒ outer restore), `2/3` skip the outer bound, `4/5` find
in the inner bound (mark ⇒ emit, boundary + reset ⇒ inner restore), `6/7` seek the inner bound's rest to
its boundary, `8/9` seek the output data to its terminator, `10–13` the ROM block splice (last bit resets
into the next inner round), `14/15` skip the outer bound again, `16/17` heal the inner bound (boundary +
reset ⇒ next outer round), `18/19` restore the outer bound, `20` = halt. -/

def nestMachine (bits : List Bool) : Machine where
  State := Fin 21 × Fin (bits.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 20)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, s.2.1, s.2.2), some false, 3) else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((18, s.2.1, s.2.2), none, 3) else ((20, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then ((3, s.2.1, b), none, 1)
    else if s.1 = 3 then
      (if s.2.2 then ((2, s.2.1, s.2.2), none, 1)
       else (if b then ((4, s.2.1, s.2.2), none, 1) else ((20, s.2.1, s.2.2), none, 2)))
    else if s.1 = 4 then ((5, s.2.1, b), none, 1)
    else if s.1 = 5 then
      (if s.2.2 then
        (if b then ((6, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 1)
         else ((4, s.2.1, s.2.2), none, 1))
       else (if b then ((14, s.2.1, s.2.2), none, 3) else ((20, s.2.1, s.2.2), none, 2)))
    else if s.1 = 6 then ((7, s.2.1, b), none, 1)
    else if s.1 = 7 then
      (if b = s.2.2 then ((6, s.2.1, s.2.2), none, 1) else ((8, s.2.1, s.2.2), none, 1))
    else if s.1 = 8 then ((9, s.2.1, b), none, 1)
    else if s.1 = 9 then
      (if b = s.2.2 then ((8, s.2.1, s.2.2), none, 1) else ((10, s.2.1, s.2.2), none, 0))
    else if s.1 = 10 then ((11, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 11 then ((12, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 12 then ((13, s.2.1, s.2.2), some false, 1)
    else if s.1 = 13 then
      (if h : s.2.1.val + 1 < bits.length then
        ((10, ⟨s.2.1.val + 1, by omega⟩, s.2.2), some true, 0)
       else ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some true, 3))
    else if s.1 = 14 then ((15, s.2.1, b), none, 1)
    else if s.1 = 15 then
      (if s.2.2 then ((14, s.2.1, s.2.2), none, 1)
       else (if b then ((16, s.2.1, s.2.2), none, 1) else ((20, s.2.1, s.2.2), none, 2)))
    else if s.1 = 16 then ((17, s.2.1, b), none, 1)
    else if s.1 = 17 then
      (if s.2.2 then
        (if b then ((20, s.2.1, s.2.2), none, 2) else ((16, s.2.1, true), some true, 1))
       else (if b then ((0, s.2.1, s.2.2), none, 3) else ((20, s.2.1, s.2.2), none, 2)))
    else if s.1 = 18 then ((19, s.2.1, b), none, 1)
    else if s.1 = 19 then
      (if s.2.2 then
        (if b then ((20, s.2.1, s.2.2), none, 2) else ((18, s.2.1, true), some true, 1))
       else ((20, s.2.1, s.2.2), none, 2))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_nest (bits x : List Bool) :
    init (nestMachine bits) x = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_n0 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(0, idx, s), p, T⟩ = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n1_mark {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(1, idx, true), p, T⟩ = ⟨(2, idx, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n1_skip {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (nestMachine bits) ⟨(1, idx, true), p, T⟩ = ⟨(0, idx, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n1_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(1, idx, false), p, T⟩ = ⟨(18, idx, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n2 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n3_skip {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(3, idx, true), p, T⟩ = ⟨(2, idx, true), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n3_cross {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(3, idx, false), p, T⟩ = ⟨(4, idx, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n4 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(4, idx, s), p, T⟩ = ⟨(5, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n5_mark {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(5, idx, true), p, T⟩
      = ⟨(6, ⟨0, Nat.succ_pos _⟩, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n5_skip {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (nestMachine bits) ⟨(5, idx, true), p, T⟩ = ⟨(4, idx, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n5_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(5, idx, false), p, T⟩ = ⟨(14, idx, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n6 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(6, idx, s), p, T⟩ = ⟨(7, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n7_eq {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = s) :
    step (nestMachine bits) ⟨(7, idx, s), p, T⟩ = ⟨(6, idx, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n7_ne {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false ≠ s) :
    step (nestMachine bits) ⟨(7, idx, s), p, T⟩ = ⟨(8, idx, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n8 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(8, idx, s), p, T⟩ = ⟨(9, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n9_eq {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = s) :
    step (nestMachine bits) ⟨(9, idx, s), p, T⟩ = ⟨(8, idx, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n9_ne {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false ≠ s) :
    step (nestMachine bits) ⟨(9, idx, s), p, T⟩ = ⟨(10, idx, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n10 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(10, idx, s), p, T⟩
      = ⟨(11, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n11 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n12 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(12, idx, s), p, T⟩ = ⟨(13, idx, s), p + 1, writeAt T p false⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n13_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    step (nestMachine bits) ⟨(13, idx, s), p, T⟩
      = ⟨(10, ⟨idx.val + 1, by omega⟩, s), p - 1, writeAt T p true⟩ := by
  simp [step, nestMachine, moveHead, h]

theorem step_n13_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    step (nestMachine bits) ⟨(13, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, writeAt T p true⟩ := by
  simp [step, nestMachine, moveHead, h]

theorem step_n14 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(14, idx, s), p, T⟩ = ⟨(15, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n15_skip {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(15, idx, true), p, T⟩ = ⟨(14, idx, true), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n15_cross {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(15, idx, false), p, T⟩ = ⟨(16, idx, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n16 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(16, idx, s), p, T⟩ = ⟨(17, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n17_heal {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (nestMachine bits) ⟨(17, idx, true), p, T⟩
      = ⟨(16, idx, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n17_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (nestMachine bits) ⟨(17, idx, false), p, T⟩ = ⟨(0, idx, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n18 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(18, idx, s), p, T⟩ = ⟨(19, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

theorem step_n19_heal {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (nestMachine bits) ⟨(19, idx, true), p, T⟩
      = ⟨(18, idx, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, nestMachine, moveHead, h]

theorem step_n19_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} :
    step (nestMachine bits) ⟨(19, idx, false), p, T⟩ = ⟨(20, idx, false), p, T⟩ := by
  simp only [step, nestMachine, moveHead]; rfl

/-! ### Pair-step lemmas -/

theorem run_two_skipB {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (nestMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n0, h1, step_n1_skip h2]

theorem run_two_markB {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, idx, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_n0, h1, step_n1_mark h2]

theorem run_two_toRstB {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(18, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n0, h1, step_n1_done h2]

theorem run_two_skipWn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) :
    run (nestMachine bits) 2 ⟨(2, idx, s), p, T⟩ = ⟨(2, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n2, h1, step_n3_skip]

theorem run_two_crossWn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(2, idx, s), p, T⟩ = ⟨(4, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n2, h1, step_n3_cross h2]

theorem run_two_skipP {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (nestMachine bits) 2 ⟨(4, idx, s), p, T⟩ = ⟨(4, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n4, h1, step_n5_skip h2]

theorem run_two_markP {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(4, idx, s), p, T⟩
      = ⟨(6, ⟨0, Nat.succ_pos _⟩, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_n4, h1, step_n5_mark h2]

theorem run_two_doneP {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(4, idx, s), p, T⟩ = ⟨(14, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n4, h1, step_n5_done h2]

theorem run_two_seekPn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = T.getD (p + 1) false) :
    run (nestMachine bits) 2 ⟨(6, idx, s), p, T⟩ = ⟨(6, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n6, step_n7_eq h.symm]

theorem run_two_crossPn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(6, idx, s), p, T⟩ = ⟨(8, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n6, h1, step_n7_ne (by rw [h2]; simp)]

theorem run_two_seekOn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = T.getD (p + 1) false) :
    run (nestMachine bits) 2 ⟨(8, idx, s), p, T⟩ = ⟨(8, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n8, step_n9_eq h.symm]

theorem run_two_detectOn {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(8, idx, s), p, T⟩ = ⟨(10, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n8, h1, step_n9_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_rom4n_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    run (nestMachine bits) 4 ⟨(10, idx, s), p, T⟩
      = ⟨(10, ⟨idx.val + 1, by omega⟩, s), p + 2,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_n10, step_n11, step_n12,
    step_n13_mid h, show p + 3 - 1 = p + 2 from by omega]

theorem run_rom4n_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    run (nestMachine bits) 4 ⟨(10, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_n10, step_n11, step_n12,
    step_n13_last h]

theorem run_two_skipW2n {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) :
    run (nestMachine bits) 2 ⟨(14, idx, s), p, T⟩ = ⟨(14, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n14, h1, step_n15_skip]

theorem run_two_crossW2n {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(14, idx, s), p, T⟩ = ⟨(16, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n14, h1, step_n15_cross h2]

theorem run_two_healP {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (nestMachine bits) 2 ⟨(16, idx, s), p, T⟩
      = ⟨(16, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_n16, h1, step_n17_heal h2]

theorem run_two_doneHealP {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (nestMachine bits) 2 ⟨(16, idx, s), p, T⟩ = ⟨(0, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n16, h1, step_n17_done h2]

theorem run_two_healB {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (nestMachine bits) 2 ⟨(18, idx, s), p, T⟩
      = ⟨(18, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_n18, h1, step_n19_heal h2]

theorem run_two_doneB {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) :
    run (nestMachine bits) 2 ⟨(18, idx, s), p, T⟩ = ⟨(20, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_n18, h1, step_n19_done]

/-! ### Scan run-invariants -/

theorem run_skipBs (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (nestMachine bits) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipB hk.1 hk.2]
    rfl

theorem run_skipWns (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool) (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (nestMachine bits) (2 * k) ⟨(2, idx, s), q, T⟩
      = ⟨(2, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipWn (h k (by omega))]
    rfl

theorem run_skipPs (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (nestMachine bits) (2 * k) ⟨(4, idx, s), q, T⟩
      = ⟨(4, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipP hk.1 hk.2]
    rfl

theorem run_seekPns (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (nestMachine bits) (2 * k) ⟨(6, idx, s), q, T⟩
      = ⟨(6, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekPn (h k (by omega))]
    rfl

theorem run_seekOns (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (nestMachine bits) (2 * k) ⟨(8, idx, s), q, T⟩
      = ⟨(8, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekOn (h k (by omega))]
    rfl

theorem run_skipW2ns (bits : List Bool) (T : List Bool) (q k : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool) (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (nestMachine bits) (2 * k) ⟨(14, idx, s), q, T⟩
      = ⟨(14, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipW2n (h k (by omega))]
    rfl

/-- The inner-bound heal invariant (evolving tape, past the outer-bound prefix). -/
theorem run_healPs (bits A : List Bool) (B P : ℕ) (E : List Bool) (hq : A.length = 2 * B + 2)
    (idx : Fin (bits.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ P) :
    run (nestMachine bits) (2 * i) ⟨(16, idx, s), 2 * B + 2, A ++ (hlT P 0 ++ E)⟩
      = ⟨(16, idx, if i = 0 then s else true), 2 * B + 2 + 2 * i, A ++ (hlT P i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hlo : (A ++ (hlT P i ++ E)).getD (2 * B + 2 + 2 * i) false = true :=
      liftJ A _ hq (hlE_pair_lo P i E (by omega))
    have hhi : (A ++ (hlT P i ++ E)).getD (2 * B + 2 + 2 * i + 1) false = false := by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
      exact liftJ A _ hq (hlE_pair_hi P i E (by omega))
    have hw : writeAt (A ++ (hlT P i ++ E)) (2 * B + 2 + 2 * i + 1) true
        = A ++ (hlT P (i + 1) ++ E) := by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
        writeAt_append_right A _ (2 * B + 2) (2 * i + 1) true hq
          (by rw [List.length_append, hlT_length P i (by omega)]; omega),
        hlT_heal P i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healP hlo hhi, hw]
    rfl

/-- The outer-bound restore invariant. -/
theorem run_healBs (bits : List Bool) (v : ℕ) (E : List Bool) (idx : Fin (bits.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (nestMachine bits) (2 * i) ⟨(18, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(18, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_healB (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ### The ROM block induction (two-part work prefix) -/

theorem run_romn (bits A B2 out : List Bool) (q : ℕ) (hq : A.length + B2.length = q) (s : Bool) :
    ∀ d j, (hjd : j + d = bits.length) → 0 < d →
      run (nestMachine bits) (4 * d)
        ⟨(10, ⟨j, by omega⟩, s), q + 2 * (out.length + j),
          A ++ (B2 ++ encodeD (out ++ bits.take j))⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, A ++ (B2 ++ encodeD (out ++ bits))⟩ := by
  intro d
  induction d with
  | zero => intro j hjd hd; omega
  | succ d ih =>
    intro j hjd hd
    have hsn := writes_snoc2 A B2 (out ++ bits.take j) q hq (bits.getD j false)
    rw [show (out ++ bits.take j).length = out.length + j from by
        rw [List.length_append, List.length_take]; omega] at hsn
    have htake : (out ++ bits.take j) ++ [bits.getD j false] = out ++ bits.take (j + 1) := by
      rw [List.append_assoc, ← take_snoc_getD bits false j (by omega)]
    rw [htake] at hsn
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      have hj : j = bits.length - 1 := by omega
      subst hj
      have hlast : ¬(bits.length - 1 + 1 < bits.length) := by omega
      rw [show 4 * (0 + 1) = 4 from rfl, run_rom4n_last (s := s) hlast, hsn,
        show bits.take (bits.length - 1 + 1) = bits from by
          rw [show bits.length - 1 + 1 = bits.length from by omega, List.take_length]]
    · have hmid : j + 1 < bits.length := by omega
      rw [show 4 * (d + 1) = 4 + 4 * d from by ring, run_add,
        run_rom4n_mid (s := s) hmid, hsn,
        show q + 2 * (out.length + j) + 2 = q + 2 * (out.length + (j + 1)) from by omega]
      exact ih (j + 1) (by omega) hd0

/-! ## The inner round -/

/-- **One inner round** (generic accumulated output `OUT`): skip the outer bound, mark the inner bound's
pair `i`, seek to the output terminator, splice the block, reset. -/
theorem run_inner_round (bits : List Bool) (B P a i : ℕ) (OUT : List Bool) (ha : a ≤ B)
    (hi : i < P) (hbits : bits ≠ []) (idx : Fin (bits.length + 1)) (s : Bool) :
    run (nestMachine bits) (2 * B + 2 * P + 2 * OUT.length + 4 * bits.length + 6)
      ⟨(2, idx, s), 0, cntT B a ++ (cntT P i ++ encodeD OUT)⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT B a ++ (cntT P (i + 1) ++ encodeD (OUT ++ bits))⟩ := by
  have hB : 0 < bits.length := List.length_pos_iff.mpr hbits
  have hcb := cntT_length B a ha
  -- skip the outer bound and cross
  have st1 := run_skipWns bits (cntT B a ++ (cntT P i ++ encodeD OUT)) 0 B idx s
    (fun i' hi' => by simpa using cntE_lo B a _ i' ha hi')
  simp only [Nat.zero_add] at st1
  have st2 := run_two_crossWn (idx := idx) (s := if B = 0 then s else true) (p := 2 * B)
    (T := cntT B a ++ (cntT P i ++ encodeD OUT))
    (cntE_cm_lo B a _ ha) (cntE_cm_hi B a _ ha)
  -- skip the inner bound's marks and mark its pair `i`
  have st3 := run_skipPs bits (cntT B a ++ (cntT P i ++ encodeD OUT)) (2 * B + 2) i idx false
    (fun i' hi' => ⟨liftJ _ _ hcb (cntE_mark_lo P i _ i' hi'), by
      rw [show 2 * B + 2 + 2 * i' + 1 = 2 * B + 2 + (2 * i' + 1) from by omega]
      exact liftJ _ _ hcb (cntE_mark_hi P i _ i' hi')⟩)
  have st4 := run_two_markP (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * B + 2 + 2 * i) (T := cntT B a ++ (cntT P i ++ encodeD OUT))
    (liftJ _ _ hcb (cntE_data P i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hcb (cntE_data P i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw4 : writeAt (cntT B a ++ (cntT P i ++ encodeD OUT)) (2 * B + 2 + 2 * i + 1) false
      = cntT B a ++ (cntT P (i + 1) ++ encodeD OUT) := by
    rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
      writeAt_append_right _ _ (2 * B + 2) (2 * i + 1) false hcb
        (by rw [List.length_append, cntT_length P i (by omega)]; omega),
      cntT_mark P i _ hi]
  rw [hw4] at st4
  -- seek the inner bound's rest and cross its boundary
  have st5 := run_seekPns bits (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT))
    (2 * B + 2 + 2 * i + 2) (P - i - 1) ⟨0, Nat.succ_pos _⟩ true (fun i' hi' => by
      have e1 : (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT)).getD
          (2 * B + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * B + 2 + 2 * i + 2 + 2 * i' = 2 * B + 2 + (2 * i + 2 + 2 * i') from by omega]
        exact liftJ _ _ hcb (cntE_data P (i + 1) _ (2 * i + 2 + 2 * i')
          (by omega) (by omega) (by omega))
      have e2 : (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT)).getD
          (2 * B + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * B + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * B + 2 + (2 * i + 2 + 2 * i' + 1) from by omega]
        exact liftJ _ _ hcb (cntE_data P (i + 1) _ (2 * i + 2 + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * B + 2 + 2 * i + 2 + 2 * (P - i - 1) = 2 * B + 2 + 2 * P from by omega] at st5
  have st6 := run_two_crossPn
    (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := storedD (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT)) (2 * B + 2 + 2 * i + 2) true
      (P - i - 1))
    (p := 2 * B + 2 + 2 * P) (T := cntT B a ++ (cntT P (i + 1) ++ encodeD OUT))
    (liftJ _ _ hcb (cntE_cm_lo P (i + 1) _ (by omega)))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P (i + 1) _ (by omega)))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at st6
  -- seek the output data and detect its terminator
  have hq2 : (cntT B a).length + (cntT P (i + 1)).length = 2 * B + 2 * P + 4 := by
    rw [hcb, cntT_length P (i + 1) (by omega)]; omega
  have st7 := run_seekOns bits (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT))
    (2 * B + 2 * P + 4) OUT.length ⟨0, Nat.succ_pos _⟩ false
    (fun i' hi' => preD2_data_eq (cntT B a) (cntT P (i + 1)) OUT (2 * B + 2 * P + 4) i' hq2 hi')
  have st8 := run_two_detectOn
    (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := storedD (cntT B a ++ (cntT P (i + 1) ++ encodeD OUT)) (2 * B + 2 * P + 4) false
      OUT.length)
    (p := 2 * B + 2 * P + 4 + 2 * OUT.length)
    (preD2_mark_lo (cntT B a) (cntT P (i + 1)) OUT (2 * B + 2 * P + 4) hq2)
    (preD2_mark_hi (cntT B a) (cntT P (i + 1)) OUT (2 * B + 2 * P + 4) hq2)
  -- splice the block
  have st9 := run_romn bits (cntT B a) (cntT P (i + 1)) OUT (2 * B + 2 * P + 4) hq2 false
    bits.length 0 (by omega) hB
  simp only [List.take_zero, List.append_nil, Nat.add_zero] at st9
  -- assemble
  rw [show 2 * B + 2 * P + 2 * OUT.length + 4 * bits.length + 6
      = 2 * B + (2 + (2 * i + (2 + (2 * (P - i - 1) + (2 + (2 * OUT.length
          + (2 + 4 * bits.length))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, st9]

/-! ## The inner rounds and the outer round -/

/-- Cumulative clock of the first `i` inner rounds. -/
def inners (B P L W : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => inners B P L W i + (2 * B + 2 * P + 2 * (L + i * W) + 4 * W + 6)

theorem run_inner_rounds (bits : List Bool) (B P a : ℕ) (OUT : List Bool) (ha : a ≤ B)
    (hbits : bits ≠ []) (s : Bool) (i'' : ℕ) (hi : i'' ≤ P) :
    run (nestMachine bits) (inners B P OUT.length bits.length i'')
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT B a ++ (cntT P 0 ++ encodeD OUT)⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, if i'' = 0 then s else false), 0,
          cntT B a ++ (cntT P i'' ++ encodeD (OUT ++ blkRep bits i''))⟩ := by
  induction i'' with
  | zero =>
    simp [blkRep]
    rfl
  | succ i'' ih =>
    have hrd := run_inner_round bits B P a i'' (OUT ++ blkRep bits i'') ha (by omega) hbits
      ⟨0, Nat.succ_pos _⟩ (if i'' = 0 then s else false)
    rw [show (OUT ++ blkRep bits i'').length = OUT.length + i'' * bits.length from by
        rw [List.length_append, blkRep_length],
      List.append_assoc, show blkRep bits i'' ++ bits = blkRep bits (i'' + 1) from rfl] at hrd
    rw [show inners B P OUT.length bits.length (i'' + 1)
        = inners B P OUT.length bits.length i''
            + (2 * B + 2 * P + 2 * (OUT.length + i'' * bits.length)
                + 4 * bits.length + 6) from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The outer round's clock: find-and-mark, the `P` inner rounds, and the inner finale. -/
def outerRC (B P L W t : ℕ) : ℕ := 2 * t + 2 + (inners B P L W P + (4 * B + 4 * P + 8))

/-- **One outer round** (generic accumulated output `OUT`): mark the outer bound's pair `t`, run the inner
loop to completion — including the inner bound's own restore — and reset. -/
theorem run_outer_round (bits : List Bool) (B P t : ℕ) (OUT : List Bool) (ht : t < B)
    (hbits : bits ≠ []) (s : Bool) :
    run (nestMachine bits) (outerRC B P OUT.length bits.length t)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT B t ++ (cntT P 0 ++ encodeD OUT)⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT B (t + 1) ++ (cntT P 0 ++ encodeD (OUT ++ blkRep bits P))⟩ := by
  have hcb := cntT_length B (t + 1) (by omega : t + 1 ≤ B)
  -- find and mark the outer bound's pair `t` (resetting)
  have st1 := run_skipBs bits (cntT B t ++ (cntT P 0 ++ encodeD OUT)) 0 t
    ⟨0, Nat.succ_pos _⟩ s
    (fun i hi => ⟨by simpa using cntE_mark_lo B t _ i hi,
                  by simpa using cntE_mark_hi B t _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_markB (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if t = 0 then s else true) (p := 2 * t)
    (T := cntT B t ++ (cntT P 0 ++ encodeD OUT))
    (cntE_data B t _ (2 * t) (by omega) (by omega) (by omega))
    (cntE_data B t _ (2 * t + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark B t _ ht] at st2
  -- the inner loop
  have st3 := run_inner_rounds bits B P (t + 1) OUT (by omega) hbits true P (le_refl P)
  -- the inner finale: exhaust the inner bound, restore it
  have st4 := run_skipWns bits (cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P)))
    0 B ⟨0, Nat.succ_pos _⟩ (if P = 0 then true else false)
    (fun i hi => by simpa using cntE_lo B (t + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st4
  have st5 := run_two_crossWn (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if B = 0 then (if P = 0 then true else false) else true) (p := 2 * B)
    (T := cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P)))
    (cntE_cm_lo B (t + 1) _ (by omega)) (cntE_cm_hi B (t + 1) _ (by omega))
  have st6 := run_skipPs bits
    (cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P))) (2 * B + 2) P
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨liftJ _ _ hcb (cntE_mark_lo P P _ i hi), by
      rw [show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hcb (cntE_mark_hi P P _ i hi)⟩)
  have st7 := run_two_doneP (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P)))
    (liftJ _ _ hcb (cntE_cm_lo P P _ (le_refl P)))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (cntE_cm_hi P P _ (le_refl P)))
  have st8 := run_skipW2ns bits
    (cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P))) 0 B
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => by simpa using cntE_lo B (t + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st8
  have st9 := run_two_crossW2n (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B (t + 1) ++ (cntT P P ++ encodeD (OUT ++ blkRep bits P)))
    (cntE_cm_lo B (t + 1) _ (by omega)) (cntE_cm_hi B (t + 1) _ (by omega))
  have st10 := run_healPs bits (cntT B (t + 1)) B P (encodeD (OUT ++ blkRep bits P)) hcb
    ⟨0, Nat.succ_pos _⟩ false P (le_refl P)
  rw [hlT_zero] at st10
  have st11 := run_two_doneHealP (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := cntT B (t + 1) ++ (hlT P P ++ encodeD (OUT ++ blkRep bits P)))
    (liftJ _ _ hcb (hlE_cm_lo P _))
    (by rw [show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega]
        exact liftJ _ _ hcb (hlE_cm_hi P _))
  -- assemble
  rw [show outerRC B P OUT.length bits.length t
      = 2 * t + (2 + (inners B P OUT.length bits.length P + (2 * B + (2 + (2 * P + (2
          + (2 * B + (2 + (2 * P + 2))))))))) from by rw [outerRC]; omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, st11, hlT_last, ← cntT_zero]

/-! ## The outer rounds and the top theorem -/

/-- Cumulative clock of the first `k` outer rounds. -/
def outers (B P L W : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => outers B P L W t + outerRC B P (L + t * P * W) W t

theorem run_outer_rounds (bits : List Bool) (B P : ℕ) (out : List Bool) (hbits : bits ≠ [])
    (k : ℕ) (hk : k ≤ B) (s : Bool) :
    run (nestMachine bits) (outers B P out.length bits.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT B 0 ++ (cntT P 0 ++ encodeD out)⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT B k ++ (cntT P 0 ++ encodeD (out ++ blkRep bits (k * P)))⟩ := by
  induction k with
  | zero =>
    simp [blkRep]
    rfl
  | succ k ih =>
    have hrd := run_outer_round bits B P k (out ++ blkRep bits (k * P)) (by omega) hbits
      (if k = 0 then s else false)
    rw [show (out ++ blkRep bits (k * P)).length = out.length + k * P * bits.length from by
        rw [List.length_append, blkRep_length, Nat.mul_assoc],
      List.append_assoc, ← blkRep_add,
      show k * P + P = (k + 1) * P from by ring] at hrd
    rw [show outers B P out.length bits.length (k + 1)
        = outers B P out.length bits.length k
            + outerRC B P (out.length + k * P * bits.length) bits.length k from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The nested loop's explicit clock. -/
def nestClock (B P L W : ℕ) : ℕ := outers B P L W B + (2 * B + (2 + (2 * B + 2)))

/-- **The nested loop runs to completion.**  On `unaryD B ++ (unaryD P ++ encodeD out)` the machine halts by
itself at the explicit clock with tape **exactly**
`unaryD B ++ (unaryD P ++ encodeD (out ++ blkRep bits (B·P)))` — the `B·P`-fold block emission, both bounds
restored. -/
theorem nest_run (bits : List Bool) (hbits : bits ≠ []) (B P : ℕ) (out : List Bool) :
    run (nestMachine bits) (nestClock B P out.length bits.length)
      (init (nestMachine bits) (unaryD B ++ (unaryD P ++ encodeD out)))
      = ⟨(20, ⟨0, Nat.succ_pos _⟩, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ encodeD (out ++ blkRep bits (B * P)))⟩ := by
  rw [init_nest, ← cntT_zero, ← cntT_zero, nestClock, run_add,
    run_outer_rounds bits B P out hbits B (le_refl B) false, ite_self]
  have st1 := run_skipBs bits
    (cntT B B ++ (cntT P 0 ++ encodeD (out ++ blkRep bits (B * P)))) 0 B
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by simpa using cntE_mark_lo B B _ i hi,
                  by simpa using cntE_mark_hi B B _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toRstB (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if B = 0 then false else true) (p := 2 * B)
    (T := cntT B B ++ (cntT P 0 ++ encodeD (out ++ blkRep bits (B * P))))
    (cntE_cm_lo B B _ (le_refl B)) (cntE_cm_hi B B _ (le_refl B))
  have st3 := run_healBs bits B (cntT P 0 ++ encodeD (out ++ blkRep bits (B * P)))
    ⟨0, Nat.succ_pos _⟩ false B (le_refl B)
  have st4 := run_two_doneB (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if B = 0 then false else true) (p := 2 * B)
    (hlE_cm_lo B (cntT P 0 ++ encodeD (out ++ blkRep bits (B * P))))
  rw [run_add, st1, run_add, st2, ← hlT_zero, run_add, st3, st4, hlT_last, cntT_zero,
    cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem nest_halted (bits : List Bool) (hbits : bits ≠ []) (B P : ℕ) (out : List Bool) :
    (nestMachine bits).halt
      (run (nestMachine bits) (nestClock B P out.length bits.length)
        (init (nestMachine bits) (unaryD B ++ (unaryD P ++ encodeD out)))).st = true := by
  rw [nest_run bits hbits B P out]; rfl

/-- **The nested loop's output.** -/
theorem nest_output (bits : List Bool) (hbits : bits ≠ []) (B P : ℕ) (out : List Bool) :
    (run (nestMachine bits) (nestClock B P out.length bits.length)
      (init (nestMachine bits) (unaryD B ++ (unaryD P ++ encodeD out)))).tp
      = unaryD B ++ (unaryD P ++ encodeD (out ++ blkRep bits (B * P))) := by
  rw [nest_run bits hbits B P out]

/-! ## Polynomial clock bounds -/

theorem inners_le (B P L W i : ℕ) (hi : i ≤ P) :
    inners B P L W i ≤ i * (2 * B + 2 * P + 2 * (L + P * W) + 4 * W + 6) := by
  induction i with
  | zero => simp [inners]
  | succ i ih =>
    calc inners B P L W (i + 1)
        = inners B P L W i + (2 * B + 2 * P + 2 * (L + i * W) + 4 * W + 6) := rfl
      _ ≤ i * (2 * B + 2 * P + 2 * (L + P * W) + 4 * W + 6)
          + (2 * B + 2 * P + 2 * (L + P * W) + 4 * W + 6) := by
          have hiw : i * W ≤ P * W := Nat.mul_le_mul_right W (by omega)
          exact Nat.add_le_add (ih (by omega)) (by omega)
      _ = (i + 1) * (2 * B + 2 * P + 2 * (L + P * W) + 4 * W + 6) := by ring

/-- The per-outer-round bound, atom-preserved. -/
def nestRB (B P L W : ℕ) : ℕ :=
  P * (2 * B + 2 * P + 2 * (L + P * W) + 4 * W + 6) + 6 * B + 4 * P + 10

theorem outerRC_le (B P L W t : ℕ) (ht : t ≤ B) :
    outerRC B P L W t ≤ nestRB B P L W := by
  have h := inners_le B P L W P (le_refl P)
  rw [outerRC, nestRB]
  omega

theorem nestRB_mono (B P W L1 L2 : ℕ) (h : L1 ≤ L2) : nestRB B P L1 W ≤ nestRB B P L2 W := by
  rw [nestRB, nestRB]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left P (by omega)) (le_refl _)) (le_refl _)) (le_refl _)

theorem outers_le (B P L W k : ℕ) (hk : k ≤ B) :
    outers B P L W k ≤ k * nestRB B P (L + B * P * W) W := by
  induction k with
  | zero => simp [outers]
  | succ k ih =>
    have hstep : outerRC B P (L + k * P * W) W k ≤ nestRB B P (L + B * P * W) W := by
      refine le_trans (outerRC_le B P (L + k * P * W) W k (by omega)) ?_
      refine nestRB_mono B P W _ _ ?_
      have : k * P * W ≤ B * P * W :=
        Nat.mul_le_mul_right W (Nat.mul_le_mul_right P (by omega))
      omega
    calc outers B P L W (k + 1)
        = outers B P L W k + outerRC B P (L + k * P * W) W k := rfl
      _ ≤ k * nestRB B P (L + B * P * W) W + nestRB B P (L + B * P * W) W :=
          Nat.add_le_add (ih (by omega)) hstep
      _ = (k + 1) * nestRB B P (L + B * P * W) W := by ring

/-- **The clock is polynomial** (explicit: `B` outer rounds, each bounded by the atom-preserved
`nestRB` at the maximal output length). -/
theorem nestClock_le (B P L W : ℕ) :
    nestClock B P L W ≤ B * nestRB B P (L + B * P * W) W + (4 * B + 4) := by
  have h := outers_le B P L W B (le_refl B)
  rw [nestClock]
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest
