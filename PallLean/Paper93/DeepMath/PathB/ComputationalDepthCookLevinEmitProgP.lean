import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Cook–Levin M2 emitter — the prefix-generalised program engine, and the first grand-loop run

The E6 instantiation pattern, executed on the straight-line engine: `progPMachine prog` is
`progMachine prog` re-derived for the layout `cntT G g ++ (unaryD v ++ encodeD out)` — **a passive
marked-counter prefix in front**, exactly what `rep_run`'s tape-sequence hypothesis presents (the
grand bound `cntT B (t+1)`).  Every track gains one leading skip of the prefix (its pairs are
lo-`true` like any counter, its terminator `01`), every position shifts by `2G+2`, and every fact
climbs one lift level (`liftJ → liftJ2`, `preD → preD2`, `writes_snoc → writes_snoc2`) — a mechanical
shift of the proven development, parametric in `(G, g)` with `g ≤ G`.  The top theorem
(`progP_run`) preserves the prefix verbatim.

**The crown: the first complete grand-loop stack.**  `rep_progP_run` feeds `progPMachine prog` to
`repMachine`: the combined machine — a runtime-bounded loop around a prefixed engine — emits **`B`
copies of the program's denotation** at the exact budgeted clock, the grand bound marked round by
round and healed.  This is the E6 assembly working end to end on a real engine; the remaining engine
variants (`loopProg2P`, `loopProg3P`, `initLoopP`, the prefixed re-armers) are the same shift applied
to their existing developments.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitProgP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The machine

Control: `Fin 34 × Fin (|prog|+1) × Bool`.  Phases: `0` the dispatch; `1–10` the append track (skip
the prefix, skip the counter, seek the output terminator, snoc, advance); `11–32` the splice track
(skip the prefix, find/mark in the counter, seek, snoc-`true` cycles, closing `false`, prefix-skip
and heal, advance); `33` = halt. -/

def progPMachine (prog : List (Option Bool)) : Machine where
  State := Fin 34 × Fin (prog.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 33)
  δ := fun s b =>
    if s.1 = 0 then
      (if s.2.1.val < prog.length then
        (match prog.getD s.2.1.val none with
         | some _ => ((1, s.2.1, s.2.2), none, 2)
         | none => ((11, s.2.1, s.2.2), none, 2))
       else ((33, s.2.1, s.2.2), none, 2))
    else if s.1 = 1 then ((2, s.2.1, b), none, 1)
    else if s.1 = 2 then
      (if s.2.2 then ((1, s.2.1, s.2.2), none, 1)
       else (if b then ((3, s.2.1, s.2.2), none, 1) else ((33, s.2.1, s.2.2), none, 2)))
    else if s.1 = 3 then ((4, s.2.1, b), none, 1)
    else if s.1 = 4 then
      (if s.2.2 then ((3, s.2.1, s.2.2), none, 1)
       else (if b then ((5, s.2.1, s.2.2), none, 1) else ((33, s.2.1, s.2.2), none, 2)))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if b = s.2.2 then ((5, s.2.1, s.2.2), none, 1) else ((7, s.2.1, s.2.2), none, 0))
    else if s.1 = 7 then
      ((8, s.2.1, s.2.2), some (prog.getD s.2.1.val none).bitVal', 1)
    else if s.1 = 8 then
      ((9, s.2.1, s.2.2), some (prog.getD s.2.1.val none).bitVal', 1)
    else if s.1 = 9 then ((10, s.2.1, s.2.2), some false, 1)
    else if s.1 = 10 then
      (if h : s.2.1.val + 1 < prog.length + 1 then
        ((0, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((33, s.2.1, s.2.2), some true, 2))
    else if s.1 = 11 then ((12, s.2.1, b), none, 1)
    else if s.1 = 12 then
      (if s.2.2 then ((11, s.2.1, s.2.2), none, 1)
       else (if b then ((13, s.2.1, s.2.2), none, 1) else ((33, s.2.1, s.2.2), none, 2)))
    else if s.1 = 13 then ((14, s.2.1, b), none, 1)
    else if s.1 = 14 then
      (if s.2.2 then
        (if b then ((15, s.2.1, s.2.2), some false, 1) else ((13, s.2.1, s.2.2), none, 1))
       else (if b then ((23, s.2.1, s.2.2), none, 1) else ((33, s.2.1, s.2.2), none, 2)))
    else if s.1 = 15 then ((16, s.2.1, b), none, 1)
    else if s.1 = 16 then
      (if b = s.2.2 then ((15, s.2.1, s.2.2), none, 1) else ((17, s.2.1, s.2.2), none, 1))
    else if s.1 = 17 then ((18, s.2.1, b), none, 1)
    else if s.1 = 18 then
      (if b = s.2.2 then ((17, s.2.1, s.2.2), none, 1) else ((19, s.2.1, s.2.2), none, 0))
    else if s.1 = 19 then ((20, s.2.1, s.2.2), some true, 1)
    else if s.1 = 20 then ((21, s.2.1, s.2.2), some true, 1)
    else if s.1 = 21 then ((22, s.2.1, s.2.2), some false, 1)
    else if s.1 = 22 then ((11, s.2.1, s.2.2), some true, 3)
    else if s.1 = 23 then ((24, s.2.1, b), none, 1)
    else if s.1 = 24 then
      (if b = s.2.2 then ((23, s.2.1, s.2.2), none, 1) else ((25, s.2.1, s.2.2), none, 0))
    else if s.1 = 25 then ((26, s.2.1, s.2.2), some false, 1)
    else if s.1 = 26 then ((27, s.2.1, s.2.2), some false, 1)
    else if s.1 = 27 then ((28, s.2.1, s.2.2), some false, 1)
    else if s.1 = 28 then ((29, s.2.1, s.2.2), some true, 3)
    else if s.1 = 29 then ((30, s.2.1, b), none, 1)
    else if s.1 = 30 then
      (if s.2.2 then ((29, s.2.1, s.2.2), none, 1)
       else (if b then ((31, s.2.1, s.2.2), none, 1) else ((33, s.2.1, s.2.2), none, 2)))
    else if s.1 = 31 then ((32, s.2.1, b), none, 1)
    else if s.1 = 32 then
      (if s.2.2 then
        (if b then ((33, s.2.1, s.2.2), none, 2) else ((31, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < prog.length + 1 then
                ((0, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((33, s.2.1, s.2.2), none, 2))
             else ((33, s.2.1, s.2.2), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_pgp (prog : List (Option Bool)) (t : List Bool) :
    init (progPMachine prog) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

section Steps
variable {prog : List (Option Bool)} {idx : Fin (prog.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem pp_dispatch_some {b : Bool} (h : idx.val < prog.length)
    (hp : prog.getD idx.val none = some b) :
    run (progPMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(1, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : prog[(idx : ℕ)]'h = some b := by
    rwa [List.getD_eq_getElem prog none h] at hp
  simp [step, progPMachine, moveHead, h, hp']

theorem pp_dispatch_none (h : idx.val < prog.length)
    (hp : prog.getD idx.val none = none) :
    run (progPMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(11, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : prog[(idx : ℕ)]'h = none := by
    rwa [List.getD_eq_getElem prog none h] at hp
  simp [step, progPMachine, moveHead, h, hp']

theorem pp_dispatch_halt (h : ¬(idx.val < prog.length)) :
    run (progPMachine prog) 1 ⟨(0, idx, s), p, T⟩ = ⟨(33, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, progPMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps2
variable {prog : List (Option Bool)} {idx : Fin (prog.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem pp_skipWa (h1 : T.getD p false = true) :
    run (progPMachine prog) 2 ⟨(1, idx, s), p, T⟩ = ⟨(1, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(1, idx, s), p, T⟩
      = ⟨(2, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, progPMachine, moveHead]; rfl

theorem pp_crossWa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(1, idx, s), p, T⟩ = ⟨(3, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(1, idx, s), p, T⟩
      = ⟨(2, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_skipCa (h1 : T.getD p false = true) :
    run (progPMachine prog) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, progPMachine, moveHead]; rfl

theorem pp_crossCa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_skipWj (h1 : T.getD p false = true) :
    run (progPMachine prog) 2 ⟨(11, idx, s), p, T⟩ = ⟨(11, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, progPMachine, moveHead]; rfl

theorem pp_crossWj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_skipWh (h1 : T.getD p false = true) :
    run (progPMachine prog) 2 ⟨(29, idx, s), p, T⟩ = ⟨(29, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, progPMachine, moveHead]; rfl

theorem pp_crossWh (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(29, idx, s), p, T⟩ = ⟨(31, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_scanO (h : T.getD p false = T.getD (p + 1) false) :
    run (progPMachine prog) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_scanA (h : T.getD p false = T.getD (p + 1) false) :
    run (progPMachine prog) 2 ⟨(15, idx, s), p, T⟩
      = ⟨(15, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_scanB (h : T.getD p false = T.getD (p + 1) false) :
    run (progPMachine prog) 2 ⟨(17, idx, s), p, T⟩
      = ⟨(17, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_scanF (h : T.getD p false = T.getD (p + 1) false) :
    run (progPMachine prog) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_crossSA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(15, idx, s), p, T⟩ = ⟨(17, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progPMachine, moveHead, h2']

theorem pp_detectO (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progPMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem pp_detectB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progPMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem pp_detectF (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, progPMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem pp_skipCm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (progPMachine prog) 2 ⟨(13, idx, s), p, T⟩ = ⟨(13, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_markC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(13, idx, s), p, T⟩
      = ⟨(15, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_doneC (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(13, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_healC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (progPMachine prog) 2 ⟨(31, idx, s), p, T⟩
      = ⟨(31, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2]

theorem pp_doneHealC (h : idx.val + 1 < prog.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (progPMachine prog) 2 ⟨(31, idx, s), p, T⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (progPMachine prog) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, progPMachine, moveHead, h2, h]

theorem pp_four_T :
    run (progPMachine prog) 4 ⟨(19, idx, s), p, T⟩
      = ⟨(11, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (progPMachine prog) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (progPMachine prog) ⟨(20, idx, s), p', T'⟩
      = ⟨(21, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (progPMachine prog) ⟨(21, idx, s), p', T'⟩
      = ⟨(22, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (progPMachine prog) ⟨(22, idx, s), p', T'⟩
      = ⟨(11, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem pp_four_F :
    run (progPMachine prog) 4 ⟨(25, idx, s), p, T⟩
      = ⟨(29, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (progPMachine prog) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (progPMachine prog) ⟨(26, idx, s), p', T'⟩
      = ⟨(27, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (progPMachine prog) ⟨(27, idx, s), p', T'⟩
      = ⟨(28, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (progPMachine prog) ⟨(28, idx, s), p', T'⟩
      = ⟨(29, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem pp_four_bit (h : idx.val + 1 < prog.length + 1) :
    run (progPMachine prog) 4 ⟨(7, idx, s), p, T⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (prog.getD idx.val none).bitVal')
            (p + 1) (prog.getD idx.val none).bitVal') (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (progPMachine prog) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, s), p + 1, writeAt T p (prog.getD idx.val none).bitVal'⟩ := by
    simp only [step, progPMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (progPMachine prog) ⟨(8, idx, s), p', T'⟩
      = ⟨(9, idx, s), p' + 1, writeAt T' p' (prog.getD idx.val none).bitVal'⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (progPMachine prog) ⟨(9, idx, s), p', T'⟩
      = ⟨(10, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, progPMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (progPMachine prog) ⟨(10, idx, s), p', T'⟩
      = ⟨(0, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, progPMachine, moveHead, h]
  rw [e1, e2, e3, e4]

end Steps2

/-! ### Scan run-invariants -/

theorem pp_skipWas (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (progPMachine prog) (2 * k) ⟨(1, idx, s), q, T⟩
      = ⟨(1, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_skipWa (h k (by omega))]
    rfl

theorem pp_skipCas (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (progPMachine prog) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_skipCa (h k (by omega))]
    rfl

theorem pp_skipWjs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (progPMachine prog) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_skipWj (h k (by omega))]
    rfl

theorem pp_skipWhs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (progPMachine prog) (2 * k) ⟨(29, idx, s), q, T⟩
      = ⟨(29, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_skipWh (h k (by omega))]
    rfl

theorem pp_scanOs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progPMachine prog) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_scanO (h k (by omega))]
    rfl

theorem pp_scanAs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progPMachine prog) (2 * k) ⟨(15, idx, s), q, T⟩
      = ⟨(15, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_scanA (h k (by omega))]
    rfl

theorem pp_scanBs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progPMachine prog) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_scanB (h k (by omega))]
    rfl

theorem pp_scanFs (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (progPMachine prog) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_scanF (h k (by omega))]
    rfl

theorem pp_skipCms (prog : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (prog.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (progPMachine prog) (2 * k) ⟨(13, idx, s), q, T⟩
      = ⟨(13, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), pp_skipCm hk.1 hk.2]
    rfl

/-- The counter heal (evolving `hlT`, past the prefix). -/
theorem pp_healCs (prog : List (Option Bool)) (P : List Bool) (G v : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (idx : Fin (prog.length + 1)) (s : Bool) (i : ℕ)
    (hi : i ≤ v) :
    run (progPMachine prog) (2 * i) ⟨(31, idx, s), 2 * G + 2, P ++ (hlT v 0 ++ E)⟩
      = ⟨(31, idx, if i = 0 then s else true), 2 * G + 2 + 2 * i, P ++ (hlT v i ++ E)⟩ := by
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
      pp_healC h1 h2, hw]
    rfl

/-! ## The instruction lemmas

Layout: `cntT G g ++ (unaryD v / cntT v j ++ encodeD OUT)` — prefix at `[0, 2G+2)`, counter at
`[2G+2, 2G+2v+4)`, output at `2G+2v+4`. -/

/-- **An append instruction**, prefixed. -/
theorem pp_instr_append (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (h : idx.val < prog.length) {b : Bool} (hp : prog.getD idx.val none = some b)
    (G g v : ℕ) (hg : g ≤ G) (OUT : List Bool) (s : Bool) :
    run (progPMachine prog) (2 * G + 2 * v + 2 * OUT.length + 11)
      ⟨(0, idx, s), 0, cntT G g ++ (cntT v 0 ++ encodeD OUT)⟩
      = ⟨(0, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT v 0 ++ encodeD (OUT ++ [b]))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hq2 : (cntT G g).length + (cntT v 0).length = 2 * G + 2 * v + 4 := by
    rw [hW, cntT_length v 0 (by omega)]; omega
  have a0 := pp_dispatch_some (s := s) (p := 0)
    (T := cntT G g ++ (cntT v 0 ++ encodeD OUT)) h hp
  have a1 := pp_skipWas prog (cntT G g ++ (cntT v 0 ++ encodeD OUT)) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at a1
  have a2 := pp_crossWa (prog := prog) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT v 0 ++ encodeD OUT))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have a3 := pp_skipCas prog (cntT G g ++ (cntT v 0 ++ encodeD OUT)) (2 * G + 2) v idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo v 0 _ i (by omega) hi))
  have a4 := pp_crossCa (prog := prog) (idx := idx) (s := if v = 0 then false else true)
    (p := 2 * G + 2 + 2 * v) (T := cntT G g ++ (cntT v 0 ++ encodeD OUT))
    (by rw [show 2 * G + 2 + 2 * v = 2 * G + 2 + (2 * v) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo v 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * v + 1 = 2 * G + 2 + (2 * v + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi v 0 _ (by omega)))
  have a5 := pp_scanOs prog (cntT G g ++ (cntT v 0 ++ encodeD OUT))
    (2 * G + 2 + 2 * v + 2) OUT.length idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * v + 2 + 2 * i = 2 * G + 2 * v + 4 + 2 * i from by omega,
        show 2 * G + 2 * v + 4 + 2 * i + 1 = 2 * G + 2 * v + 4 + 2 * i + 1 from rfl]
      exact preD2_data_eq (cntT G g) (cntT v 0) OUT (2 * G + 2 * v + 4) i hq2 hi)
  rw [show 2 * G + 2 + 2 * v + 2 + 2 * OUT.length = 2 * G + 2 * v + 4 + 2 * OUT.length
      from by omega] at a5
  have a6 := pp_detectO (prog := prog) (idx := idx)
    (s := storedD (cntT G g ++ (cntT v 0 ++ encodeD OUT)) (2 * G + 2 + 2 * v + 2) false
      OUT.length)
    (p := 2 * G + 2 * v + 4 + 2 * OUT.length)
    (preD2_mark_lo (cntT G g) (cntT v 0) OUT (2 * G + 2 * v + 4) hq2)
    (preD2_mark_hi (cntT G g) (cntT v 0) OUT (2 * G + 2 * v + 4) hq2)
  have a7 := pp_four_bit (prog := prog) (idx := idx) (s := false)
    (p := 2 * G + 2 * v + 4 + 2 * OUT.length)
    (T := cntT G g ++ (cntT v 0 ++ encodeD OUT)) (by omega)
  rw [hp] at a7
  simp only [Option.bitVal'] at a7
  rw [writes_snoc2 (cntT G g) (cntT v 0) OUT (2 * G + 2 * v + 4) hq2 b] at a7
  rw [show 2 * G + 2 * v + 2 * OUT.length + 11
      = 1 + (2 * G + (2 + (2 * v + (2 + (2 * OUT.length + (2 + 4)))))) from by omega,
    run_add, a0, run_add, a1, run_add, a2, run_add, a3, run_add, a4, run_add, a5,
    run_add, a6, a7]

/-- One splice sub-round, prefixed. -/
theorem pp_sp_round (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (G g v j : ℕ) (hg : g ≤ G) (hj : j < v) (OUT : List Bool) (s : Bool) :
    run (progPMachine prog) (2 * G + 2 * v + 2 * OUT.length + 2 * j + 10)
      ⟨(11, idx, s), 0, cntT G g ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true))⟩
      = ⟨(11, idx, false), 0, cntT G g
          ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate (j + 1) true))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hq2 : (cntT G g).length + (cntT v (j + 1)).length = 2 * G + 2 * v + 4 := by
    rw [hW, cntT_length v (j + 1) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j true).length = OUT.length + j := by
    rw [List.length_append, List.length_replicate]
  have r1 := pp_skipWjs prog (cntT G g
      ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at r1
  have r2 := pp_crossWj (prog := prog) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r3 := pp_skipCms prog (cntT G g
      ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true))) (2 * G + 2) j idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo v j _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi v j _ i hi)⟩)
  have r4 := pp_markC (prog := prog) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G + 2 + 2 * j)
    (T := cntT G g ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true)))
    (by rw [show 2 * G + 2 + 2 * j = 2 * G + 2 + (2 * j) from rfl]
        exact liftJ _ _ hW (cntE_data v j _ (2 * j) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * j + 1 = 2 * G + 2 + (2 * j + 1) from by omega]
        exact liftJ _ _ hW (cntE_data v j _ (2 * j + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true)))
      (2 * G + 2 + 2 * j + 1) false
      = cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)) := by
    rw [show 2 * G + 2 + 2 * j + 1 = 2 * G + 2 + (2 * j + 1) from by omega,
      writeAt_append_right _ _ (2 * G + 2) (2 * j + 1) false hW
        (by rw [List.length_append, cntT_length v j (by omega)]; omega),
      cntT_mark v j _ hj]
  rw [hw] at r4
  have r5 := pp_scanAs prog (cntT G g
      ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
    (2 * G + 2 + 2 * j + 2) (v - j - 1) idx true
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))).getD
          (2 * G + 2 + 2 * j + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * j + 2 + 2 * i = 2 * G + 2 + (2 * (j + 1) + 2 * i)
            from by omega]
        exact liftJ _ _ hW (cntE_data v (j + 1) _ (2 * (j + 1) + 2 * i) (by omega)
          (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true))).getD
          (2 * G + 2 + 2 * j + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * j + 2 + 2 * i + 1 = 2 * G + 2 + (2 * (j + 1) + 2 * i + 1)
            from by omega]
        exact liftJ _ _ hW (cntE_data v (j + 1) _ (2 * (j + 1) + 2 * i + 1) (by omega)
          (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * j + 2 + 2 * (v - j - 1) = 2 * G + 2 + 2 * v from by omega] at r5
  have r6 := pp_crossSA (prog := prog) (idx := idx)
    (s := storedD (cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
      (2 * G + 2 + 2 * j + 2) true (v - j - 1))
    (p := 2 * G + 2 + 2 * v)
    (T := cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
    (by rw [show 2 * G + 2 + 2 * v = 2 * G + 2 + (2 * v) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo v (j + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * v + 1 = 2 * G + 2 + (2 * v + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi v (j + 1) _ (by omega)))
  have r7 := pp_scanBs prog (cntT G g
      ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
    (2 * G + 2 + 2 * v + 2) (OUT.length + j) idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * v + 2 + 2 * i = 2 * G + 2 * v + 4 + 2 * i from by omega,
        show 2 * G + 2 * v + 4 + 2 * i + 1 = 2 * G + 2 * v + 4 + 2 * i + 1 from rfl]
      exact preD2_data_eq (cntT G g) (cntT v (j + 1)) (OUT ++ List.replicate j true)
        (2 * G + 2 * v + 4) i hq2
        (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * v + 2 + 2 * (OUT.length + j)
      = 2 * G + 2 * v + 4 + 2 * (OUT.length + j) from by omega] at r7
  have hm1 := preD2_mark_lo (cntT G g) (cntT v (j + 1)) (OUT ++ List.replicate j true)
    (2 * G + 2 * v + 4) hq2
  have hm2 := preD2_mark_hi (cntT G g) (cntT v (j + 1)) (OUT ++ List.replicate j true)
    (2 * G + 2 * v + 4) hq2
  rw [hlen] at hm1 hm2
  have r8 := pp_detectB (prog := prog) (idx := idx)
    (s := storedD (cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
      (2 * G + 2 + 2 * v + 2) false (OUT.length + j))
    (p := 2 * G + 2 * v + 4 + 2 * (OUT.length + j)) hm1 hm2
  have hsn := writes_snoc2 (cntT G g) (cntT v (j + 1)) (OUT ++ List.replicate j true)
    (2 * G + 2 * v + 4) hq2 true
  rw [hlen, List.append_assoc,
    show (List.replicate j true ++ [true] : List Bool) = List.replicate (j + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have r9 := pp_four_T (prog := prog) (idx := idx) (s := false)
    (p := 2 * G + 2 * v + 4 + 2 * (OUT.length + j))
    (T := cntT G g ++ (cntT v (j + 1) ++ encodeD (OUT ++ List.replicate j true)))
  rw [hsn] at r9
  rw [show 2 * G + 2 * v + 2 * OUT.length + 2 * j + 10
      = 2 * G + (2 + (2 * j + (2 + (2 * (v - j - 1) + (2 + (2 * (OUT.length + j)
          + (2 + 4))))))) from by omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, r9]

theorem pp_sp_rounds (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (G g v : ℕ) (hg : g ≤ G) (OUT : List Bool) (j : ℕ) (hj : j ≤ v) (s : Bool) :
    run (progPMachine prog) (lp3SpRounds (2 * G + 2 * v + 2 * OUT.length + 10) j)
      ⟨(11, idx, s), 0, cntT G g ++ (cntT v 0 ++ encodeD OUT)⟩
      = ⟨(11, idx, if j = 0 then s else false), 0, cntT G g
          ++ (cntT v j ++ encodeD (OUT ++ List.replicate j true))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 2 * v + 2 * OUT.length + 10) (j + 1)
        = lp3SpRounds (2 * G + 2 * v + 2 * OUT.length + 10) j
            + (2 * G + 2 * v + 2 * OUT.length + 10 + 2 * j) from rfl,
      show 2 * G + 2 * v + 2 * OUT.length + 10 + 2 * j
        = 2 * G + 2 * v + 2 * OUT.length + 2 * j + 10 from by omega,
      run_add, ih (by omega), pp_sp_round prog idx G g v j hg (by omega) OUT _,
      if_neg (by omega)]

def ppSpliceCost (G v L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 2 * v + 2 * L + 10) v
    + ((2 * G + 4 * v + 2 * L + 10) + (2 * G + 2 * v + 4)))

/-- **A splice instruction**, prefixed. -/
theorem pp_instr_splice (prog : List (Option Bool)) (idx : Fin (prog.length + 1))
    (h : idx.val < prog.length) (hp : prog.getD idx.val none = none)
    (G g v : ℕ) (hg : g ≤ G) (OUT : List Bool) (s : Bool) :
    run (progPMachine prog) (ppSpliceCost G v OUT.length)
      ⟨(0, idx, s), 0, cntT G g ++ (cntT v 0 ++ encodeD OUT)⟩
      = ⟨(0, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT v 0 ++ encodeD (OUT ++ encodeNat v))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hq2 : (cntT G g).length + (cntT v v).length = 2 * G + 2 * v + 4 := by
    rw [hW, cntT_length v v (le_refl v)]; omega
  have hlen2 : (OUT ++ List.replicate v true).length = OUT.length + v := by
    rw [List.length_append, List.length_replicate]
  have d0 := pp_dispatch_none (s := s) (p := 0)
    (T := cntT G g ++ (cntT v 0 ++ encodeD OUT)) h hp
  have d1 := pp_sp_rounds prog idx G g v hg OUT v (le_refl v) s
  have d2 := pp_skipWjs prog (cntT G g
      ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true))) 0 G idx
    (if v = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d2
  have d3 := pp_crossWj (prog := prog) (idx := idx)
    (s := if G = 0 then (if v = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d4 := pp_skipCms prog (cntT G g
      ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true))) (2 * G + 2) v idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo v v _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi v v _ i hi)⟩)
  have d5 := pp_doneC (prog := prog) (idx := idx) (s := if v = 0 then false else true)
    (p := 2 * G + 2 + 2 * v)
    (T := cntT G g ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true)))
    (by rw [show 2 * G + 2 + 2 * v = 2 * G + 2 + (2 * v) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo v v _ (le_refl v)))
    (by rw [show 2 * G + 2 + 2 * v + 1 = 2 * G + 2 + (2 * v + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi v v _ (le_refl v)))
  have d6 := pp_scanFs prog (cntT G g
      ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true)))
    (2 * G + 2 + 2 * v + 2) (OUT.length + v) idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * v + 2 + 2 * i = 2 * G + 2 * v + 4 + 2 * i from by omega,
        show 2 * G + 2 * v + 4 + 2 * i + 1 = 2 * G + 2 * v + 4 + 2 * i + 1 from rfl]
      exact preD2_data_eq (cntT G g) (cntT v v) (OUT ++ List.replicate v true)
        (2 * G + 2 * v + 4) i hq2
        (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * v + 2 + 2 * (OUT.length + v)
      = 2 * G + 2 * v + 4 + 2 * (OUT.length + v) from by omega] at d6
  have hm1 := preD2_mark_lo (cntT G g) (cntT v v) (OUT ++ List.replicate v true)
    (2 * G + 2 * v + 4) hq2
  have hm2 := preD2_mark_hi (cntT G g) (cntT v v) (OUT ++ List.replicate v true)
    (2 * G + 2 * v + 4) hq2
  rw [hlen2] at hm1 hm2
  have d7 := pp_detectF (prog := prog) (idx := idx)
    (s := storedD (cntT G g ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true)))
      (2 * G + 2 + 2 * v + 2) false (OUT.length + v))
    (p := 2 * G + 2 * v + 4 + 2 * (OUT.length + v)) hm1 hm2
  have hsn := writes_snoc2 (cntT G g) (cntT v v) (OUT ++ List.replicate v true)
    (2 * G + 2 * v + 4) hq2 false
  rw [hlen2, List.append_assoc,
    show (List.replicate v true ++ [false] : List Bool) = encodeNat v from rfl] at hsn
  have d8 := pp_four_F (prog := prog) (idx := idx) (s := false)
    (p := 2 * G + 2 * v + 4 + 2 * (OUT.length + v))
    (T := cntT G g ++ (cntT v v ++ encodeD (OUT ++ List.replicate v true)))
  rw [hsn] at d8
  have d9 := pp_skipWhs prog (cntT G g ++ (hlT v 0 ++ encodeD (OUT ++ encodeNat v))) 0 G
    idx false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d9
  have d10 := pp_crossWh (prog := prog) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G) (T := cntT G g ++ (hlT v 0 ++ encodeD (OUT ++ encodeNat v)))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d11 := pp_healCs prog (cntT G g) G v (encodeD (OUT ++ encodeNat v)) hW idx false v
    (le_refl v)
  have d12 := pp_doneHealC (prog := prog) (idx := idx)
    (s := if v = 0 then false else true) (p := 2 * G + 2 + 2 * v)
    (T := cntT G g ++ (hlT v v ++ encodeD (OUT ++ encodeNat v))) (by omega)
    (by rw [show 2 * G + 2 + 2 * v = 2 * G + 2 + (2 * v) from rfl]
        exact liftJ _ _ hW (hlE_cm_lo v _))
    (by rw [show 2 * G + 2 + 2 * v + 1 = 2 * G + 2 + (2 * v + 1) from by omega]
        exact liftJ _ _ hW (hlE_cm_hi v _))
  rw [show ppSpliceCost G v OUT.length
      = 1 + (lp3SpRounds (2 * G + 2 * v + 2 * OUT.length + 10) v
          + (2 * G + (2 + (2 * v + (2 + (2 * (OUT.length + v) + (2 + (4 + (2 * G + (2
            + (2 * v + 2)))))))))))
      from by simp only [ppSpliceCost]; omega,
    run_add, d0, run_add, d1, run_add, d2, run_add, d3, run_add, d4, run_add, d5,
    run_add, d6, run_add, d7, run_add, d8, ← hlT_zero, run_add, d9, run_add, d10,
    run_add, d11, d12, hlT_last, ← cntT_zero]

/-! ## The segment and the top theorem -/

def ppInstrCost (prog : List (Option Bool)) (G v L : ℕ) (n : ℕ) : ℕ :=
  match prog.getD n none with
  | some _ => 2 * G + 2 * v + 2 * (L + (progOutN prog v n).length) + 11
  | none => ppSpliceCost G v (L + (progOutN prog v n).length)

def ppSegN (prog : List (Option Bool)) (G v L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ppSegN prog G v L n + ppInstrCost prog G v L n

theorem pp_run_instrs (prog : List (Option Bool)) (G g v : ℕ) (hg : g ≤ G)
    (out : List Bool) (n : ℕ) (hn : n ≤ prog.length) (s : Bool) :
    run (progPMachine prog) (ppSegN prog G v out.length n)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G g ++ (cntT v 0 ++ encodeD out)⟩
      = ⟨(0, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT G g ++ (cntT v 0 ++ encodeD (out ++ progOutN prog v n))⟩ := by
  induction n with
  | zero => simp only [ppSegN]; rw [run_zero]; simp [progOutN]
  | succ n ih =>
    rw [show ppSegN prog G v out.length (n + 1)
        = ppSegN prog G v out.length n + ppInstrCost prog G v out.length n from rfl,
      run_add, ih (by omega)]
    cases hp : prog.getD n none with
    | none =>
      have hin := pp_instr_splice prog ⟨n, by omega⟩
        (show n < prog.length from by omega) hp G g v hg (out ++ progOutN prog v n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN prog v n ++ encodeNat v = progOutN prog v (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [ppInstrCost, hp]
      rw [hin]
      simp
    | some b =>
      have hin := pp_instr_append prog ⟨n, by omega⟩
        (show n < prog.length from by omega) hp G g v hg (out ++ progOutN prog v n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN prog v n ++ [b] = progOutN prog v (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [ppInstrCost, hp]
      rw [hin]
      simp

def ppClock (prog : List (Option Bool)) (G v L : ℕ) : ℕ :=
  ppSegN prog G v L prog.length + 1

/-- **The prefixed program emitter runs to completion**, the prefix preserved verbatim — the
`rep_run`-hypothesis shape. -/
theorem progP_run (prog : List (Option Bool)) (G g v : ℕ) (hg : g ≤ G) (out : List Bool) :
    run (progPMachine prog) (ppClock prog G v out.length)
      (init (progPMachine prog) (cntT G g ++ (unaryD v ++ encodeD out)))
      = ⟨(33, ⟨prog.length, Nat.lt_succ_self _⟩, false), 0,
          cntT G g ++ (unaryD v ++ encodeD (out ++ progOut prog v))⟩ := by
  rw [init_pgp, ← cntT_zero]
  simp only [ppClock]
  rw [run_add, pp_run_instrs prog G g v hg out prog.length (le_refl _) false, ite_self,
    pp_dispatch_halt (Nat.lt_irrefl _), progOutN_full, cntT_zero]

theorem progP_halted (prog : List (Option Bool)) (G g v : ℕ) (hg : g ≤ G)
    (out : List Bool) :
    (progPMachine prog).halt
      (run (progPMachine prog) (ppClock prog G v out.length)
        (init (progPMachine prog) (cntT G g ++ (unaryD v ++ encodeD out)))).st = true := by
  rw [progP_run prog G g v hg out]; rfl

/-! ## THE FIRST COMPLETE GRAND-LOOP STACK -/

/-- `B` copies of the program's denotation. -/
def repProgOut (prog : List (Option Bool)) (v : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => repProgOut prog v t ++ progOut prog v

/-- **The grand loop around the prefixed engine**: the combined machine emits `B` copies of the
program's denotation at the exact budgeted clock — the grand bound marked round by round and healed.
The E6 assembly pattern, end to end, on a real engine. -/
theorem rep_progP_run (prog : List (Option Bool)) (v B : ℕ) (out : List Bool) :
    run (repMachine (progPMachine prog))
      (repRounds (fun t => ppClock prog B v (out ++ repProgOut prog v t).length) B
        + (4 * B + 4))
      (init (repMachine (progPMachine prog))
        (cntT B 0 ++ (unaryD v ++ encodeD out)))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD v ++ encodeD (out ++ repProgOut prog v B))⟩ := by
  have h := rep_run (progPMachine prog) B
    (fun t => unaryD v ++ encodeD (out ++ repProgOut prog v t))
    (fun t => ppClock prog B v (out ++ repProgOut prog v t).length)
    (fun _ => (33, ⟨prog.length, Nat.lt_succ_self _⟩, false)) (fun _ => 0)
    (fun t ht => by
      constructor
      · have hr := progP_run prog B (t + 1) v (by omega) (out ++ repProgOut prog v t)
        rw [List.append_assoc,
          show repProgOut prog v t ++ progOut prog v = repProgOut prog v (t + 1) from rfl]
          at hr
        exact hr
      · rfl)
  simp only [show repProgOut prog v 0 = [] from rfl, List.append_nil] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitProgP