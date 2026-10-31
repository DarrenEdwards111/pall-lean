import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearm

/-!
# Cook–Levin M2 emitter — the init family emitter

The last engine: the init family's cell fixes are unit clauses whose **sign is the input bit**
(`initFormula_members`), so their emitter must fuse the loop engine with E5's cursored-input read.
`initLoopMachine body` runs

    for k in 0..N-1:  execute `body`;  read-emit the k-th input bit,

on the layout `cntT N k ++ (xVis x m ++ (jT N k ++ encodeD out))` — bound, cursored input, live
variable, output.  The body is a `loopProgMachine`-style instruction list (`some b` appends, `none`
splices the live index); the **hardwired read stage** after each body walks the cursored region to the
first unvisited unit, marks it, carries its value in the finite control, and emits it doubled — past
the input's end the walk meets the terminator and emits `false`, which is `getD`'s default, so round
`k` emits exactly `progOut body k ++ [x.getD k false]` and — as in E5 — **found and past-the-end
rounds cost the same clock**.  The finale heals the bound and every cursor.

**The init family instance**: `initCellBody = [.bit t, .bit f, .bit f, none, .bit f]` makes round `p`
emit exactly `encodeClause' [(cellVar 0 p, x.getD p false)]` (`encodeClause'_unit_cell` at `t = 0`
consumed); `initCell_family_run` emits the whole input-dependent part of `initFormula` in one run.
The two input-independent unit clauses at its head (start state, head at `0`) are fixed-bit programs —
their `progMachine` bodies and factorizations are provided (`initStateProg`/`initHeadProg`) for E6's
chain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

/-! ## The denotation -/

/-- The first `k` rounds' output: the body's denotation plus the input bit, per round. -/
def initOutN (body : List (Option Bool)) (x : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => initOutN body x k ++ (progOut body k ++ [x.getD k false])

def initOut (body : List (Option Bool)) (x : List Bool) (N : ℕ) : List Bool :=
  initOutN body x N

theorem initOut_eq_flatten (body : List (Option Bool)) (x : List Bool) (N : ℕ) :
    initOut body x N
      = ((List.range N).map (fun k => progOut body k ++ [x.getD k false])).flatten := by
  show initOutN body x N = _
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show initOutN body x (N + 1)
        = initOutN body x N ++ (progOut body N ++ [x.getD N false]) from rfl, ih,
      List.range_succ, List.map_append, List.flatten_append]
    simp

/-! ## The machine

Control: `Fin 97 × Fin (|body|+1) × Bool`.  Phase groups: `0/1` the loop find, `2` the dispatch
(instructions, then — pointer exhausted — the read stage), `3–16` the append track (the input region
crossed by the generic four-cell unit walk), `17–46` the splice track (seek, snoc-`true` cycles,
closing `false`, heal walk), `47–78` the **read stage** (visited-unit walk, value-dispatched cursor
mark, two emit tracks, the past-the-end fall-through to the `false` track), `79–89` the in-place
increment, `90/91` heal the bound, `92–95` heal the cursors, `96` = halt. -/

/-- The bit an append instruction writes. -/
def _root_.Option.bitVal' : Option Bool → Bool
  | some b => b
  | none => false

def initLoopMachine (body : List (Option Bool)) : Machine where
  State := Fin 97 × Fin (body.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 96)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 3)
         else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((90, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val none with
         | some _ => ((3, s.2.1, s.2.2), none, 2)
         | none => ((17, s.2.1, s.2.2), none, 2))
       else ((47, s.2.1, s.2.2), none, 2))
    else if s.1 = 3 then ((4, s.2.1, b), none, 1)
    else if s.1 = 4 then
      (if s.2.2 then ((3, s.2.1, s.2.2), none, 1)
       else (if b then ((5, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if b = s.2.2 then ((7, s.2.1, s.2.2), none, 1) else ((9, s.2.1, s.2.2), none, 1))
    else if s.1 = 7 then ((8, s.2.1, b), none, 1)
    else if s.1 = 8 then ((5, s.2.1, s.2.2), none, 1)
    else if s.1 = 9 then ((10, s.2.1, b), none, 1)
    else if s.1 = 10 then
      (if b = s.2.2 then ((9, s.2.1, s.2.2), none, 1) else ((11, s.2.1, s.2.2), none, 1))
    else if s.1 = 11 then ((12, s.2.1, b), none, 1)
    else if s.1 = 12 then
      (if b = s.2.2 then ((11, s.2.1, s.2.2), none, 1) else ((13, s.2.1, s.2.2), none, 0))
    else if s.1 = 13 then
      ((14, s.2.1, s.2.2), some (body.getD s.2.1.val none).bitVal', 1)
    else if s.1 = 14 then
      ((15, s.2.1, s.2.2), some (body.getD s.2.1.val none).bitVal', 1)
    else if s.1 = 15 then ((16, s.2.1, s.2.2), some false, 1)
    else if s.1 = 16 then
      (if h : s.2.1.val + 1 < body.length + 1 then
        ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((96, s.2.1, s.2.2), some true, 2))
    else if s.1 = 17 then ((18, s.2.1, b), none, 1)
    else if s.1 = 18 then
      (if s.2.2 then ((17, s.2.1, s.2.2), none, 1)
       else (if b then ((19, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 19 then ((20, s.2.1, b), none, 1)
    else if s.1 = 20 then
      (if b = s.2.2 then ((21, s.2.1, s.2.2), none, 1) else ((23, s.2.1, s.2.2), none, 1))
    else if s.1 = 21 then ((22, s.2.1, b), none, 1)
    else if s.1 = 22 then ((19, s.2.1, s.2.2), none, 1)
    else if s.1 = 23 then ((24, s.2.1, b), none, 1)
    else if s.1 = 24 then
      (if s.2.2 then
        (if b then ((25, s.2.1, s.2.2), some false, 1) else ((23, s.2.1, s.2.2), none, 1))
       else (if b then ((33, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 25 then ((26, s.2.1, b), none, 1)
    else if s.1 = 26 then
      (if b = s.2.2 then ((25, s.2.1, s.2.2), none, 1) else ((27, s.2.1, s.2.2), none, 1))
    else if s.1 = 27 then ((28, s.2.1, b), none, 1)
    else if s.1 = 28 then
      (if b = s.2.2 then ((27, s.2.1, s.2.2), none, 1) else ((29, s.2.1, s.2.2), none, 0))
    else if s.1 = 29 then ((30, s.2.1, s.2.2), some true, 1)
    else if s.1 = 30 then ((31, s.2.1, s.2.2), some true, 1)
    else if s.1 = 31 then ((32, s.2.1, s.2.2), some false, 1)
    else if s.1 = 32 then ((17, s.2.1, s.2.2), some true, 3)
    else if s.1 = 33 then ((34, s.2.1, b), none, 1)
    else if s.1 = 34 then
      (if b = s.2.2 then ((33, s.2.1, s.2.2), none, 1) else ((35, s.2.1, s.2.2), none, 0))
    else if s.1 = 35 then ((36, s.2.1, s.2.2), some false, 1)
    else if s.1 = 36 then ((37, s.2.1, s.2.2), some false, 1)
    else if s.1 = 37 then ((38, s.2.1, s.2.2), some false, 1)
    else if s.1 = 38 then ((39, s.2.1, s.2.2), some true, 3)
    else if s.1 = 39 then ((40, s.2.1, b), none, 1)
    else if s.1 = 40 then
      (if s.2.2 then ((39, s.2.1, s.2.2), none, 1)
       else (if b then ((41, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 41 then ((42, s.2.1, b), none, 1)
    else if s.1 = 42 then
      (if b = s.2.2 then ((43, s.2.1, s.2.2), none, 1) else ((45, s.2.1, s.2.2), none, 1))
    else if s.1 = 43 then ((44, s.2.1, b), none, 1)
    else if s.1 = 44 then ((41, s.2.1, s.2.2), none, 1)
    else if s.1 = 45 then ((46, s.2.1, b), none, 1)
    else if s.1 = 46 then
      (if s.2.2 then
        (if b then ((96, s.2.1, s.2.2), none, 2) else ((45, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((96, s.2.1, s.2.2), none, 2))
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 47 then ((48, s.2.1, b), none, 1)
    else if s.1 = 48 then
      (if s.2.2 then ((47, s.2.1, s.2.2), none, 1)
       else (if b then ((49, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 49 then ((50, s.2.1, b), none, 1)
    else if s.1 = 50 then
      (if b = s.2.2 then
        (if s.2.2 then ((55, s.2.1, s.2.2), none, 1) else ((51, s.2.1, s.2.2), none, 1))
       else ((61, s.2.1, false), none, 1))
    else if s.1 = 51 then ((52, s.2.1, b), none, 1)
    else if s.1 = 52 then
      (if b then ((59, s.2.1, s.2.2), some false, 1) else ((49, s.2.1, s.2.2), none, 1))
    else if s.1 = 55 then ((56, s.2.1, b), none, 1)
    else if s.1 = 56 then
      (if b then ((69, s.2.1, s.2.2), some false, 1) else ((49, s.2.1, s.2.2), none, 1))
    else if s.1 = 59 then ((60, s.2.1, b), none, 1)
    else if s.1 = 60 then
      (if b = s.2.2 then ((59, s.2.1, s.2.2), none, 1) else ((61, s.2.1, s.2.2), none, 1))
    else if s.1 = 61 then ((62, s.2.1, b), none, 1)
    else if s.1 = 62 then
      (if b = s.2.2 then ((61, s.2.1, s.2.2), none, 1) else ((63, s.2.1, s.2.2), none, 1))
    else if s.1 = 63 then ((64, s.2.1, b), none, 1)
    else if s.1 = 64 then
      (if b = s.2.2 then ((63, s.2.1, s.2.2), none, 1) else ((65, s.2.1, s.2.2), none, 0))
    else if s.1 = 65 then ((66, s.2.1, s.2.2), some false, 1)
    else if s.1 = 66 then ((67, s.2.1, s.2.2), some false, 1)
    else if s.1 = 67 then ((68, s.2.1, s.2.2), some false, 1)
    else if s.1 = 68 then ((79, s.2.1, s.2.2), some true, 3)
    else if s.1 = 69 then ((70, s.2.1, b), none, 1)
    else if s.1 = 70 then
      (if b = s.2.2 then ((69, s.2.1, s.2.2), none, 1) else ((71, s.2.1, s.2.2), none, 1))
    else if s.1 = 71 then ((72, s.2.1, b), none, 1)
    else if s.1 = 72 then
      (if b = s.2.2 then ((71, s.2.1, s.2.2), none, 1) else ((73, s.2.1, s.2.2), none, 1))
    else if s.1 = 73 then ((74, s.2.1, b), none, 1)
    else if s.1 = 74 then
      (if b = s.2.2 then ((73, s.2.1, s.2.2), none, 1) else ((75, s.2.1, s.2.2), none, 0))
    else if s.1 = 75 then ((76, s.2.1, s.2.2), some true, 1)
    else if s.1 = 76 then ((77, s.2.1, s.2.2), some true, 1)
    else if s.1 = 77 then ((78, s.2.1, s.2.2), some false, 1)
    else if s.1 = 78 then ((79, s.2.1, s.2.2), some true, 3)
    else if s.1 = 79 then ((80, s.2.1, b), none, 1)
    else if s.1 = 80 then
      (if s.2.2 then ((79, s.2.1, s.2.2), none, 1)
       else (if b then ((81, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 81 then ((82, s.2.1, b), none, 1)
    else if s.1 = 82 then
      (if b = s.2.2 then ((83, s.2.1, s.2.2), none, 1) else ((85, s.2.1, s.2.2), none, 1))
    else if s.1 = 83 then ((84, s.2.1, b), none, 1)
    else if s.1 = 84 then ((81, s.2.1, s.2.2), none, 1)
    else if s.1 = 85 then
      (if b then ((86, s.2.1, b), none, 1) else ((87, s.2.1, s.2.2), some true, 1))
    else if s.1 = 86 then ((85, s.2.1, s.2.2), none, 1)
    else if s.1 = 87 then ((88, s.2.1, s.2.2), some true, 1)
    else if s.1 = 88 then ((89, s.2.1, s.2.2), some false, 1)
    else if s.1 = 89 then ((0, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 90 then ((91, s.2.1, b), none, 1)
    else if s.1 = 91 then
      (if s.2.2 then
        (if b then ((92, s.2.1, false), none, 1) else ((90, s.2.1, true), some true, 1))
       else (if b then ((92, s.2.1, false), none, 1) else ((96, s.2.1, false), none, 2)))
    else if s.1 = 92 then ((93, s.2.1, b), none, 1)
    else if s.1 = 93 then
      (if b = s.2.2 then ((94, s.2.1, s.2.2), none, 1) else ((96, s.2.1, false), none, 2))
    else if s.1 = 94 then ((95, s.2.1, b), none, 1)
    else if s.1 = 95 then
      (if b then ((92, s.2.1, s.2.2), none, 1) else ((92, s.2.1, s.2.2), some true, 1))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_il (body : List (Option Bool)) (t : List Bool) :
    init (initLoopMachine body) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

section Steps
variable {body : List (Option Bool)} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem il_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val none = some b) :
    run (initLoopMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = some b := by
    rwa [List.getD_eq_getElem body none h] at hp
  simp [step, initLoopMachine, moveHead, h, hp']

theorem il_dispatch_spliceJ (h : idx.val < body.length)
    (hp : body.getD idx.val none = none) :
    run (initLoopMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(17, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = none := by
    rwa [List.getD_eq_getElem body none h] at hp
  simp [step, initLoopMachine, moveHead, h, hp']

theorem il_dispatch_read (h : ¬(idx.val < body.length)) :
    run (initLoopMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(47, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, initLoopMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps2
variable {body : List (Option Bool)} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem il_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (initLoopMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(90, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_skipR1a (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, initLoopMachine, moveHead]; rfl

theorem il_crossR1a (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_skipR1j (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(17, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, initLoopMachine, moveHead]; rfl

theorem il_crossR1j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_skipR1hj (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(39, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, initLoopMachine, moveHead]; rfl

theorem il_crossR1hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(41, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_skipR1r (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(47, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, initLoopMachine, moveHead]; rfl

theorem il_crossR1r (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(49, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_skipR1i (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, initLoopMachine, moveHead]; rfl

theorem il_crossR1i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(81, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

/-- The generic four-cell unit walk at phase `5`: value pair equal, cursor skipped blind. -/
theorem il_four_unitUa {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) :
    run (initLoopMachine body) 4 ⟨(5, idx, s), p, T⟩ = ⟨(5, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(6, idx, v), p + 1, T⟩
      = ⟨(7, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(7, idx, v), p + 2, T⟩
      = ⟨(8, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  simp only [step, initLoopMachine, moveHead]; rfl

/-- The unit walk meets the region terminator. -/
theorem il_crossUUa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

/-- The generic four-cell unit walk at phase `19`: value pair equal, cursor skipped blind. -/
theorem il_four_unitUj {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) :
    run (initLoopMachine body) 4 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(20, idx, v), p + 1, T⟩
      = ⟨(21, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(21, idx, v), p + 2, T⟩
      = ⟨(22, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  simp only [step, initLoopMachine, moveHead]; rfl

/-- The unit walk meets the region terminator. -/
theorem il_crossUUj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

/-- The generic four-cell unit walk at phase `41`: value pair equal, cursor skipped blind. -/
theorem il_four_unitUhj {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) :
    run (initLoopMachine body) 4 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(42, idx, v), p + 1, T⟩
      = ⟨(43, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(43, idx, v), p + 2, T⟩
      = ⟨(44, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  simp only [step, initLoopMachine, moveHead]; rfl

/-- The unit walk meets the region terminator. -/
theorem il_crossUUhj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

/-- The generic four-cell unit walk at phase `81`: value pair equal, cursor skipped blind. -/
theorem il_four_unitUi {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) :
    run (initLoopMachine body) 4 ⟨(81, idx, s), p, T⟩ = ⟨(81, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(82, idx, v), p + 1, T⟩
      = ⟨(83, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(83, idx, v), p + 2, T⟩
      = ⟨(84, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  simp only [step, initLoopMachine, moveHead]; rfl

/-- The unit walk meets the region terminator. -/
theorem il_crossUUi (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(81, idx, s), p, T⟩ = ⟨(85, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_scanB3 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanB4 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanJ3 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(25, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanJ4 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanJD (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(33, idx, s), p, T⟩
      = ⟨(33, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRF1 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(59, idx, s), p, T⟩
      = ⟨(59, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRF2 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(61, idx, s), p, T⟩
      = ⟨(61, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRF3 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(63, idx, s), p, T⟩
      = ⟨(63, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRT1 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(69, idx, s), p, T⟩
      = ⟨(69, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRT2 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(71, idx, s), p, T⟩
      = ⟨(71, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_scanRT3 (h : T.getD p false = T.getD (p + 1) false) :
    run (initLoopMachine body) 2 ⟨(73, idx, s), p, T⟩
      = ⟨(73, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_crossSB3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_crossSJ3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(27, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_crossSRF1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(61, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_crossSRF2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(63, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_crossSRT1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(71, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_crossSRT2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(71, idx, s), p, T⟩ = ⟨(73, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

theorem il_detectB4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem il_detectJ4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem il_detectJD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(35, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem il_detectRF3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(65, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem il_detectRT3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(73, idx, s), p, T⟩ = ⟨(75, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem il_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (initLoopMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(23, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(25, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(33, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (initLoopMachine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(45, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

theorem il_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2, h]

theorem il_four_TJ :
    run (initLoopMachine body) 4 ⟨(29, idx, s), p, T⟩
      = ⟨(17, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (initLoopMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(30, idx, s), p', T'⟩
      = ⟨(31, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(31, idx, s), p', T'⟩
      = ⟨(32, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (initLoopMachine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(17, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem il_four_FJ :
    run (initLoopMachine body) 4 ⟨(35, idx, s), p, T⟩
      = ⟨(39, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (initLoopMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(36, idx, s), p', T'⟩
      = ⟨(37, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(37, idx, s), p', T'⟩
      = ⟨(38, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (initLoopMachine body) ⟨(38, idx, s), p', T'⟩
      = ⟨(39, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem il_four_RF :
    run (initLoopMachine body) 4 ⟨(65, idx, s), p, T⟩
      = ⟨(79, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (initLoopMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(66, idx, s), p', T'⟩
      = ⟨(67, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(67, idx, s), p', T'⟩
      = ⟨(68, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (initLoopMachine body) ⟨(68, idx, s), p', T'⟩
      = ⟨(79, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem il_four_RT :
    run (initLoopMachine body) 4 ⟨(75, idx, s), p, T⟩
      = ⟨(79, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (initLoopMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(76, idx, s), p', T'⟩
      = ⟨(77, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(77, idx, s), p', T'⟩
      = ⟨(78, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (initLoopMachine body) ⟨(78, idx, s), p', T'⟩
      = ⟨(79, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

/-- The append snoc: the instruction's bit doubled; advance. -/
theorem il_four_bit (h : idx.val + 1 < body.length + 1) :
    run (initLoopMachine body) 4 ⟨(13, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val none).bitVal')
            (p + 1) (body.getD idx.val none).bitVal') (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (initLoopMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, s), p + 1, writeAt T p (body.getD idx.val none).bitVal'⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(14, idx, s), p', T'⟩
      = ⟨(15, idx, s), p' + 1, writeAt T' p' (body.getD idx.val none).bitVal'⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(15, idx, s), p', T'⟩
      = ⟨(16, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (initLoopMachine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, initLoopMachine, moveHead, h]
  rw [e1, e2, e3, e4]

/-- The read walk: a visited unit (cursor-hi `false`), four steps through the value dispatch. -/
theorem il_four_visited {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = false) :
    run (initLoopMachine body) 4 ⟨(49, idx, s), p, T⟩ = ⟨(49, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  cases v with
  | false =>
    have e1 : step (initLoopMachine body) ⟨(50, idx, false), p + 1, T⟩
        = ⟨(51, idx, false), p + 2, T⟩ := by
      simp [step, initLoopMachine, moveHead, h2']
    rw [e1]
    have e2 : step (initLoopMachine body) ⟨(51, idx, false), p + 2, T⟩
        = ⟨(52, idx, T.getD (p + 2) false), p + 3, T⟩ := by
      simp only [step, initLoopMachine, moveHead]; rfl
    rw [e2, h3]
    simp [step, initLoopMachine, moveHead, h4']
  | true =>
    have e1 : step (initLoopMachine body) ⟨(50, idx, true), p + 1, T⟩
        = ⟨(55, idx, true), p + 2, T⟩ := by
      simp [step, initLoopMachine, moveHead, h2']
    rw [e1]
    have e2 : step (initLoopMachine body) ⟨(55, idx, true), p + 2, T⟩
        = ⟨(56, idx, T.getD (p + 2) false), p + 3, T⟩ := by
      simp only [step, initLoopMachine, moveHead]; rfl
    rw [e2, h3]
    simp [step, initLoopMachine, moveHead, h4']

/-- The read walk finds the unvisited unit, value `false`: mark, enter the `false` emit track. -/
theorem il_four_mark0 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run (initLoopMachine body) 4 ⟨(49, idx, s), p, T⟩
      = ⟨(59, idx, true), p + 4, writeAt T (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(50, idx, false), p + 1, T⟩
      = ⟨(51, idx, false), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(51, idx, false), p + 2, T⟩
      = ⟨(52, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, initLoopMachine, moveHead, h4']

/-- The read walk finds the unvisited unit, value `true`: mark, enter the `true` emit track. -/
theorem il_four_mark1 (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run (initLoopMachine body) 4 ⟨(49, idx, s), p, T⟩
      = ⟨(69, idx, true), p + 4, writeAt T (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(50, idx, true), p + 1, T⟩
      = ⟨(55, idx, true), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(55, idx, true), p + 2, T⟩
      = ⟨(56, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, initLoopMachine, moveHead, h4']

/-- The read walk meets the input terminator: past the end, the carried value is `false`. -/
theorem il_two_toRF (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(61, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

/-- The increment walk: skip a data pair of the variable. -/
theorem il_walkI (h1 : T.getD p false = true) :
    run (initLoopMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, initLoopMachine, moveHead, h1']
  rw [e0]
  simp only [step, initLoopMachine, moveHead]; rfl

/-- The increment's four marker-advancing writes; reset into the next round. -/
theorem il_four_incr (h1 : T.getD p false = false) :
    run (initLoopMachine body) 4 ⟨(85, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(87, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, initLoopMachine, moveHead, h1']
  have e1 : ∀ p' T', step (initLoopMachine body) ⟨(87, idx, s), p', T'⟩
      = ⟨(88, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (initLoopMachine body) ⟨(88, idx, s), p', T'⟩
      = ⟨(89, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (initLoopMachine body) ⟨(89, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

/-- The finale: heal a marked bound pair. -/
theorem il_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (initLoopMachine body) 2 ⟨(90, idx, s), p, T⟩
      = ⟨(90, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

/-- The bound heal completes: cross into the cursor heal. -/
theorem il_doneHB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(90, idx, s), p, T⟩ = ⟨(92, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, initLoopMachine, moveHead, h2]

/-- Heal a visited unit's cursor (four steps). -/
theorem il_four_heal {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = false) :
    run (initLoopMachine body) 4 ⟨(92, idx, s), p, T⟩
      = ⟨(92, idx, true), p + 4, writeAt T (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(93, idx, v), p + 1, T⟩
      = ⟨(94, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(94, idx, v), p + 2, T⟩
      = ⟨(95, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, initLoopMachine, moveHead, h4']

/-- Skip an unvisited unit in the cursor heal (four steps, no write). -/
theorem il_four_healSkip {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run (initLoopMachine body) 4 ⟨(92, idx, s), p, T⟩ = ⟨(92, idx, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e1 : step (initLoopMachine body) ⟨(93, idx, v), p + 1, T⟩
      = ⟨(94, idx, v), p + 2, T⟩ := by
    simp [step, initLoopMachine, moveHead, h2']
  rw [e1]
  have e2 : step (initLoopMachine body) ⟨(94, idx, v), p + 2, T⟩
      = ⟨(95, idx, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e2, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, initLoopMachine, moveHead, h4']

/-- The cursor heal meets the input terminator: halt. -/
theorem il_two_healDone (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (initLoopMachine body) 2 ⟨(92, idx, s), p, T⟩ = ⟨(96, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (initLoopMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, initLoopMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, initLoopMachine, moveHead, h2']

end Steps2

/-! ### Scan run-invariants -/

theorem il_skipBs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (initLoopMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipB hk.1 hk.2]
    rfl

theorem il_skipR1as (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipR1a (h k (by omega))]
    rfl

theorem il_skipR1js (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipR1j (h k (by omega))]
    rfl

theorem il_skipR1hjs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(39, idx, s), q, T⟩
      = ⟨(39, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipR1hj (h k (by omega))]
    rfl

theorem il_skipR1rs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(47, idx, s), q, T⟩
      = ⟨(47, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipR1r (h k (by omega))]
    rfl

theorem il_skipR1is (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipR1i (h k (by omega))]
    rfl

theorem il_unitsUa (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true) :
    run (initLoopMachine body) (4 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_unitUa hv1 hv2 hv3]
    rfl

theorem il_unitsUj (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true) :
    run (initLoopMachine body) (4 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_unitUj hv1 hv2 hv3]
    rfl

theorem il_unitsUhj (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true) :
    run (initLoopMachine body) (4 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_unitUhj hv1 hv2 hv3]
    rfl

theorem il_unitsUi (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true) :
    run (initLoopMachine body) (4 * k) ⟨(81, idx, s), q, T⟩
      = ⟨(81, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_unitUi hv1 hv2 hv3]
    rfl

theorem il_scanB3s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanB3 (h k (by omega))]
    rfl

theorem il_scanB4s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanB4 (h k (by omega))]
    rfl

theorem il_scanJ3s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanJ3 (h k (by omega))]
    rfl

theorem il_scanJ4s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanJ4 (h k (by omega))]
    rfl

theorem il_scanJDs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(33, idx, s), q, T⟩
      = ⟨(33, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanJD (h k (by omega))]
    rfl

theorem il_scanRF1s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRF1 (h k (by omega))]
    rfl

theorem il_scanRF2s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(61, idx, s), q, T⟩
      = ⟨(61, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRF2 (h k (by omega))]
    rfl

theorem il_scanRF3s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(63, idx, s), q, T⟩
      = ⟨(63, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRF3 (h k (by omega))]
    rfl

theorem il_scanRT1s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(69, idx, s), q, T⟩
      = ⟨(69, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRT1 (h k (by omega))]
    rfl

theorem il_scanRT2s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(71, idx, s), q, T⟩
      = ⟨(71, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRT2 (h k (by omega))]
    rfl

theorem il_scanRT3s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (initLoopMachine body) (2 * k) ⟨(73, idx, s), q, T⟩
      = ⟨(73, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_scanRT3 (h k (by omega))]
    rfl

theorem il_skipJms (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (initLoopMachine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_skipJm hk.1 hk.2]
    rfl

/-- The read walk over the visited prefix. -/
theorem il_visiteds (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = false) :
    run (initLoopMachine body) (4 * k) ⟨(49, idx, s), q, T⟩
      = ⟨(49, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_visited hv1 hv2 hv3 hv4]
    rfl

theorem il_walkIs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (initLoopMachine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_walkI (h k (by omega))]
    rfl

/-- The splice-mark heal (evolving `jhT`, prefixes bound and input region). -/
theorem il_healJs2 (body : List (Option Bool)) (Q R : List Bool) (N X k : ℕ) (E : List Bool)
    (hQ : Q.length = 2 * N + 2) (hR : R.length = 4 * X + 2) (hk : k ≤ N)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (initLoopMachine body) (2 * i)
      ⟨(45, idx, s), 2 * N + 2 + 4 * X + 2, Q ++ (R ++ (jhT N k 0 ++ E))⟩
      = ⟨(45, idx, if i = 0 then s else true), 2 * N + 2 + 4 * X + 2 + 2 * i,
          Q ++ (R ++ (jhT N k i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (Q ++ (R ++ (jhT N k i ++ E))).getD (2 * N + 2 + 4 * X + 2 + 2 * i) false
        = true := by
      rw [show 2 * N + 2 + 4 * X + 2 + 2 * i = 2 * N + 2 + (4 * X + 2 + 2 * i) from by omega]
      exact liftJ2 Q R _ hQ hR (jhE_pair_lo N k i E (by omega))
    have h2 : (Q ++ (R ++ (jhT N k i ++ E))).getD (2 * N + 2 + 4 * X + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * N + 2 + 4 * X + 2 + 2 * i + 1 = 2 * N + 2 + (4 * X + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 Q R _ hQ hR (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (Q ++ (R ++ (jhT N k i ++ E)))
        (2 * N + 2 + 4 * X + 2 + 2 * i + 1) true = Q ++ (R ++ (jhT N k (i + 1) ++ E)) := by
      rw [show 2 * N + 2 + 4 * X + 2 + 2 * i + 1 = 2 * N + 2 + (4 * X + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 Q R _ (2 * N + 2) (4 * X + 2) (2 * i + 1) true hQ hR
          (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      il_healJ h1 h2, hw]
    rfl

/-- The bound heal (the finale, evolving `hlT`, no prefix). -/
theorem il_healBs (body : List (Option Bool)) (v : ℕ) (E : List Bool)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (initLoopMachine body) (2 * i) ⟨(90, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(90, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      il_healB (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-- The cursor heal over the visited prefix (evolving `xHl`, one prefix). -/
theorem il_healXs (body : List (Option Bool)) (A : List Bool) (N : ℕ) (x : List Bool)
    (M : ℕ) (E : List Bool) (ha : A.length = 2 * N + 2) (hM : M ≤ x.length)
    (idx : Fin (body.length + 1)) (s : Bool) (h'' : ℕ) (hh : h'' ≤ M) :
    run (initLoopMachine body) (4 * h'')
      ⟨(92, idx, s), 2 * N + 2, A ++ (xHl x 0 M ++ E)⟩
      = ⟨(92, idx, if h'' = 0 then s else true), 2 * N + 2 + 4 * h'',
          A ++ (xHl x h'' M ++ E)⟩ := by
  induction h'' with
  | zero => rfl
  | succ h'' ih =>
    have hx : h'' < x.length := by omega
    have hv1 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'') false
        = x.getD h'' false := by
      rw [show 2 * N + 2 + 4 * h'' = 2 * N + 2 + (4 * h'') from rfl]
      exact liftJ A _ ha (xHlE_val_lo x h'' M E h'' hx)
    have hv2 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 1) false
        = x.getD h'' false := by
      rw [show 2 * N + 2 + 4 * h'' + 1 = 2 * N + 2 + (4 * h'' + 1) from by omega]
      exact liftJ A _ ha (xHlE_val_hi x h'' M E h'' hx)
    have hv3 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 2) false = true := by
      rw [show 2 * N + 2 + 4 * h'' + 2 = 2 * N + 2 + (4 * h'' + 2) from by omega]
      exact liftJ A _ ha (xHlE_cur_lo x h'' M E h'' hx)
    have hv4 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 3) false = false := by
      rw [show 2 * N + 2 + 4 * h'' + 3 = 2 * N + 2 + (4 * h'' + 3) from by omega]
      exact liftJ A _ ha (xHlE_cur_hi_at x h'' M E (by omega) hx)
    have hw : writeAt (A ++ (xHl x h'' M ++ E)) (2 * N + 2 + 4 * h'' + 3) true
        = A ++ (xHl x (h'' + 1) M ++ E) := by
      rw [show 2 * N + 2 + 4 * h'' + 3 = 2 * N + 2 + (4 * h'' + 3) from by omega,
        writeAt_append_right A _ (2 * N + 2) (4 * h'' + 3) true ha
          (by rw [List.length_append, xHl_length]; omega),
        xHl_heal x h'' M E (by omega) hx]
    rw [show 4 * (h'' + 1) = 4 * h'' + 4 from by ring, run_add, ih (by omega),
      il_four_heal hv1 hv2 hv3 hv4, hw]
    rfl

/-- The unvisited tail of the cursor heal (static). -/
theorem il_healSkips (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = true) :
    run (initLoopMachine body) (4 * k) ⟨(92, idx, s), q, T⟩
      = ⟨(92, idx, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), il_four_healSkip hv1 hv2 hv3 hv4]
    rfl

/-! ## The instruction lemmas

Round-`k` layout: `cntT N (k+1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))` — regions at `[0, 2N+2)`,
`[2N+2, 2N+4X+4)`, `[2N+4X+4, 4N+4X+6)`, output at `4N+4X+6` (`X := |x|`).  The body instructions are
insensitive to the cursor state `m`. -/

/-- **An append instruction**: dispatch, skip the bound, cross the input by the unit walk, cross the
variable, snoc, advance. -/
theorem il_instr_bit (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val none = some b)
    (N k : ℕ) (hk : k < N) (x : List Bool) (m : ℕ) (OUT : List Bool) (s : Bool) :
    run (initLoopMachine body) (4 * N + 4 * x.length + 2 * OUT.length + 13)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD (OUT ++ [b])))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2 : (xVis x m).length = 4 * x.length + 2 := xVis_length x m
  have hq3 : (cntT N (k + 1)).length + (xVis x m).length + (jT N k).length
      = 4 * N + 4 * x.length + 6 := by
    rw [hR1, hR2, jT_length N k (by omega)]; omega
  have b0 := il_dispatch_bit (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))) h hp
  have b1 := il_skipR1as body (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))) 0 N
    idx s (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at b1
  have b2 := il_crossR1a (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have b3 := il_unitsUa body (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2) x.length idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x m i _ hi)⟩)
  have b4 := il_crossUUa (body := body) (idx := idx)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x m _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x m _))
  have b5 := il_scanB3s body (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2 + 4 * x.length + 2) k idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * x.length + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i
            = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * x.length + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i + 1
            = 2 * N + 2 + (4 * x.length + 2 + (2 * i + 1)) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := il_crossSB3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 4 * x.length + 2) false k)
    (p := 2 * N + 2 + 4 * x.length + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k
          = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_hi N k 0 _ (by omega)))
  have b7 := il_scanB4s body (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i + 1)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (xVis x m) (jT N k) OUT
          (4 * N + 4 * x.length + 6) (i - (N - k)) hq3 (by omega))
  rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 4 * N + 4 * x.length + 6 + 2 * OUT.length from by omega] at b7
  have b8 := il_detectB4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
    (preD3_mark_lo (cntT N (k + 1)) (xVis x m) (jT N k) OUT (4 * N + 4 * x.length + 6) hq3)
    (preD3_mark_hi (cntT N (k + 1)) (xVis x m) (jT N k) OUT (4 * N + 4 * x.length + 6) hq3)
  have b9 := il_four_bit (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))) (by omega)
  rw [hp] at b9
  simp only [Option.bitVal'] at b9
  rw [writes_snoc3 (cntT N (k + 1)) (xVis x m) (jT N k) OUT (4 * N + 4 * x.length + 6)
    hq3 b] at b9
  rw [show 4 * N + 4 * x.length + 2 * OUT.length + 13
      = 1 + (2 * N + (2 + (4 * x.length + (2 + (2 * k + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4)))))))) from by omega,
    run_add, b0, run_add, b1, run_add, b2, run_add, b3, run_add, b4, run_add, b5,
    run_add, b6, run_add, b7, run_add, b8, b9]

/-! ### The splice instruction -/

/-- One splice sub-round. -/
theorem il_spj_round (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k j' : ℕ) (hj : j' < k) (hk : k < N) (x : List Bool) (m : ℕ) (OUT : List Bool)
    (s : Bool) :
    run (initLoopMachine body) (4 * N + 4 * x.length + 2 * OUT.length + 2 * j' + 12)
      ⟨(17, idx, s), 0, cntT N (k + 1)
        ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))⟩
      = ⟨(17, idx, false), 0, cntT N (k + 1)
          ++ (xVis x m ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2 : (xVis x m).length = 4 * x.length + 2 := xVis_length x m
  have hq3 : (cntT N (k + 1)).length + (xVis x m).length + (jsT N k (j' + 1)).length
      = 4 * N + 4 * x.length + 6 := by
    rw [hR1, hR2, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have j1 := il_skipR1js body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at j1
  have j2 := il_crossR1j (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have j3 := il_unitsUj body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2) x.length idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x m i _ hi)⟩)
  have j4 := il_crossUUj (body := body) (idx := idx)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x m _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x m _))
  have j5 := il_skipJms body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 4 * x.length + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i
          = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega]
      exact liftJ2 _ _ _ hR1 hR2 (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hR1 hR2 (jsE_mark_hi N k j' _ i hi)⟩)
  have j6 := il_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * N + 2 + 4 * x.length + 2 + 2 * j')
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j'
          = 2 * N + 2 + (4 * x.length + 2 + 2 * j') from by omega]
        exact liftJ2 _ _ _ hR1 hR2
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j' + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * j' + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
      (2 * N + 2 + 4 * x.length + 2 + 2 * j' + 1) false
      = cntT N (k + 1) ++ (xVis x m
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))) := by
    rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j' + 1
        = 2 * N + 2 + (4 * x.length + 2 + (2 * j' + 1)) from by omega,
      writeAt_append_right2 _ _ _ (2 * N + 2) (4 * x.length + 2) (2 * j' + 1) false hR1 hR2
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at j6
  have j7 := il_scanJ3s body (cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (xVis x m
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2 + 2 * i
            = 2 * N + 2 + (4 * x.length + 2 + (2 * (j' + 1) + 2 * i)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i)
          (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x m
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * N + 2 + (4 * x.length + 2 + (2 * (j' + 1) + 2 * i + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * N + 2 + 4 * x.length + 2 + 2 * k from by omega] at j7
  have j8 := il_crossSJ3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
      (2 * N + 2 + 4 * x.length + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * N + 2 + 4 * x.length + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k
          = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_hi N k (j' + 1) _ (by omega)))
  have j9 := il_scanJ4s body (cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (xVis x m
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (xVis x m
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (xVis x m) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (4 * N + 4 * x.length + 6) (i - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 4 * N + 4 * x.length + 6 + 2 * (OUT.length + j') from by omega] at j9
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (xVis x m) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4 * x.length + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (xVis x m) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4 * x.length + 6) hq3
  rw [hlen] at hm1 hm2
  have j10 := il_detectJ4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
      (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) false ((N - k) + (OUT.length + j')))
    (p := 4 * N + 4 * x.length + 6 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (xVis x m) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4 * x.length + 6) hq3 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have j11 := il_four_TJ (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 * x.length + 6 + 2 * (OUT.length + j'))
    (T := cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
  rw [hsn] at j11
  rw [show 4 * N + 4 * x.length + 2 * OUT.length + 2 * j' + 12
      = 2 * N + (2 + (4 * x.length + (2 + (2 * j' + (2 + (2 * (k - j' - 1)
          + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4))))))))) from by omega,
    run_add, j1, run_add, j2, run_add, j3, run_add, j4, run_add, j5, run_add, j6,
    run_add, j7, run_add, j8, run_add, j9, run_add, j10, j11]

theorem il_spj_rounds (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k : ℕ) (hk : k < N) (x : List Bool) (m : ℕ) (OUT : List Bool) (j : ℕ) (hj : j ≤ k)
    (s : Bool) :
    run (initLoopMachine body)
      (lp3SpRounds (4 * N + 4 * x.length + 2 * OUT.length + 12) j)
      ⟨(17, idx, s), 0, cntT N (k + 1) ++ (xVis x m ++ (jsT N k 0 ++ encodeD OUT))⟩
      = ⟨(17, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (xVis x m ++ (jsT N k j ++ encodeD (OUT ++ List.replicate j true)))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (4 * N + 4 * x.length + 2 * OUT.length + 12) (j + 1)
        = lp3SpRounds (4 * N + 4 * x.length + 2 * OUT.length + 12) j
            + (4 * N + 4 * x.length + 2 * OUT.length + 12 + 2 * j) from rfl,
      show 4 * N + 4 * x.length + 2 * OUT.length + 12 + 2 * j
        = 4 * N + 4 * x.length + 2 * OUT.length + 2 * j + 12 from by omega,
      run_add, ih (by omega), il_spj_round body idx N k j (by omega) hk x m OUT _,
      if_neg (by omega)]

def iljCost (N X k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (4 * N + 4 * X + 2 * L + 12) k
    + ((4 * N + 4 * X + 2 * L + 2 * k + 12) + (2 * N + 4 * X + 2 * k + 6)))

/-- **A splice instruction**: emit `encodeNat k` from the live variable, heal it, advance. -/
theorem il_instr_spliceJ (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val none = none)
    (N k : ℕ) (hk : k < N) (x : List Bool) (m : ℕ) (OUT : List Bool) (s : Bool) :
    run (initLoopMachine body) (iljCost N x.length k OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD (OUT ++ encodeNat k)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2 : (xVis x m).length = 4 * x.length + 2 := xVis_length x m
  have hq3 : (cntT N (k + 1)).length + (xVis x m).length + (jsT N k k).length
      = 4 * N + 4 * x.length + 6 := by
    rw [hR1, hR2, jsT_length N k k (le_refl k) (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate k true).length = OUT.length + k := by
    rw [List.length_append, List.length_replicate]
  have d0 := il_dispatch_spliceJ (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD OUT))) h hp
  have d1 := il_spj_rounds body idx N k hk x m OUT k (le_refl k) s
  have d2 := il_skipR1js body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))) 0 N idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d2
  have d3 := il_crossR1j (body := body) (idx := idx)
    (s := if N = 0 then (if k = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d4 := il_unitsUj body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (2 * N + 2) x.length idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x m i _ hi)⟩)
  have d5 := il_crossUUj (body := body) (idx := idx)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x m _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x m _))
  have d6 := il_skipJms body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (2 * N + 2 + 4 * x.length + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i
          = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega]
      exact liftJ2 _ _ _ hR1 hR2 (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hR1 hR2 (jsE_mark_hi N k k _ i hi)⟩)
  have d7 := il_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * N + 2 + 4 * x.length + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k
          = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jsE_m_hi N k k _ (le_refl k)))
  have d8 := il_scanJDs body (cntT N (k + 1)
      ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) ((N - k) + (OUT.length + k)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (xVis x m
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (xVis x m
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))).getD
            (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hR1 hR2 (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1) (le_refl k)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (xVis x m) (jsT N k k)
          (OUT ++ List.replicate k true) (4 * N + 4 * x.length + 6) (i - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + k))
      = 4 * N + 4 * x.length + 6 + 2 * (OUT.length + k) from by omega] at d8
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (xVis x m) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4 * x.length + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (xVis x m) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4 * x.length + 6) hq3
  rw [hlen2] at hm1 hm2
  have d9 := il_detectJD (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x m
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
      (2 * N + 2 + 4 * x.length + 2 + 2 * k + 2) false ((N - k) + (OUT.length + k)))
    (p := 4 * N + 4 * x.length + 6 + 2 * (OUT.length + k)) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (xVis x m) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4 * x.length + 6) hq3 false
  rw [hlen2, List.append_assoc,
    show (List.replicate k true ++ [false] : List Bool) = encodeNat k from rfl] at hsn
  have d10 := il_four_FJ (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 * x.length + 6 + 2 * (OUT.length + k))
    (T := cntT N (k + 1) ++ (xVis x m ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
  rw [hsn] at d10
  have d11 := il_skipR1hjs body (cntT N (k + 1)
      ++ (xVis x m ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d11
  have d12 := il_crossR1hj (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d13 := il_unitsUhj body (cntT N (k + 1)
      ++ (xVis x m ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))) (2 * N + 2) x.length
    idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x m i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x m i _ hi)⟩)
  have d14 := il_crossUUhj (body := body) (idx := idx)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x m _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x m _))
  have d15 := il_healJs2 body (cntT N (k + 1)) (xVis x m) N x.length k
    (encodeD (OUT ++ encodeNat k)) hR1 hR2 (by omega) idx false k (le_refl k)
  have d16 := il_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true) (p := 2 * N + 2 + 4 * x.length + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (xVis x m ++ (jhT N k k ++ encodeD (OUT ++ encodeNat k))))
    (by omega)
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k
          = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jhE_m_lo N k _))
    (by rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * k + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hR2 (jhE_m_hi N k _))
  rw [show iljCost N x.length k OUT.length
      = 1 + (lp3SpRounds (4 * N + 4 * x.length + 2 * OUT.length + 12) k
          + (2 * N + (2 + (4 * x.length + (2 + (2 * k + (2
            + (2 * ((N - k) + (OUT.length + k)) + (2 + (4 + (2 * N + (2 + (4 * x.length
            + (2 + (2 * k + 2)))))))))))))))
      from by simp only [iljCost]; omega,
    run_add, d0, ← jsT_zero, run_add, d1, run_add, d2, run_add, d3, run_add, d4,
    run_add, d5, run_add, d6, run_add, d7, run_add, d8, run_add, d9, run_add, d10,
    ← jhT_zero, run_add, d11, run_add, d12, run_add, d13, run_add, d14, run_add, d15,
    d16, jhT_last, jsT_zero]

/-! ## The read stage

Entered from the exhausted dispatch: walk the visited prefix, mark the first unvisited cursor, carry
the value in the phase, seek out, emit doubled.  Past the input's end the walk meets the terminator and
falls into the `false` track — `getD`'s default — at **the same clock**. -/

/-- **The read stage, input found** (`k < |x|`). -/
theorem il_read_found (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k : ℕ) (hk : k < N) (x : List Bool) (hkx : k < x.length) (OUT : List Bool) (s : Bool) :
    run (initLoopMachine body) (4 * N + 4 * x.length + 2 * OUT.length + 12)
      ⟨(47, idx, s), 0, cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(79, idx, false), 0, cntT N (k + 1)
          ++ (xVis x (k + 1) ++ (jT N k ++ encodeD (OUT ++ [x.getD k false])))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2' : (xVis x (k + 1)).length = 4 * x.length + 2 := xVis_length x (k + 1)
  have hq3 : (cntT N (k + 1)).length + (xVis x (k + 1)).length + (jT N k).length
      = 4 * N + 4 * x.length + 6 := by
    rw [hR1, hR2', jT_length N k (by omega)]; omega
  have r1 := il_skipR1rs body (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))) 0 N
    idx s (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r1
  have r2 := il_crossR1r (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r3 := il_visiteds body (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2) k idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 3 = 2 * N + 2 + (4 * i + 3) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_hi_vis x k i _ hi (by omega))⟩)
  have hvlo : (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * k) false = x.getD k false :=
    liftJ _ _ hR1 (xVisE_val_lo x k k _ hkx)
  have hvhi : (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * k + 1) false = x.getD k false := by
    rw [show 2 * N + 2 + 4 * k + 1 = 2 * N + 2 + (4 * k + 1) from by omega]
    exact liftJ _ _ hR1 (xVisE_val_hi x k k _ hkx)
  have hclo : (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * k + 2) false = true := by
    rw [show 2 * N + 2 + 4 * k + 2 = 2 * N + 2 + (4 * k + 2) from by omega]
    exact liftJ _ _ hR1 (xVisE_cur_lo x k k _ hkx)
  have hchi : (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * k + 3) false = true := by
    rw [show 2 * N + 2 + 4 * k + 3 = 2 * N + 2 + (4 * k + 3) from by omega]
    exact liftJ _ _ hR1 (xVisE_cur_hi_unvis x k k _ (le_refl k) hkx)
  have hwmark : writeAt (cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 4 * k + 3) false
      = cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)) := by
    rw [show 2 * N + 2 + 4 * k + 3 = 2 * N + 2 + (4 * k + 3) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (4 * k + 3) false hR1
        (by rw [List.length_append, xVis_length]; omega),
      xVis_mark x k _ hkx]
  have hseek : ∀ i, i < 2 * (x.length - k - 1) →
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 2 + 4 * k + 4 + 2 * i) false
      = (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 2 + 4 * k + 4 + 2 * i + 1) false := by
    intro i hi
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (j + j)) false = x.getD (k + 1 + j) false := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (j + j) = 2 * N + 2 + (4 * (k + 1 + j))
            from by omega]
        exact liftJ _ _ hR1 (xVisE_val_lo x (k + 1) (k + 1 + j) _ (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (j + j) + 1) false = x.getD (k + 1 + j) false := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (j + j) + 1
            = 2 * N + 2 + (4 * (k + 1 + j) + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x (k + 1) (k + 1 + j) _ (by omega))
      rw [e1, e2]
    · have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1)) false = true := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1)
            = 2 * N + 2 + (4 * (k + 1 + j) + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x (k + 1) (k + 1 + j) _ (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1) + 1) false = true := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1) + 1
            = 2 * N + 2 + (4 * (k + 1 + j) + 3) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_hi_unvis x (k + 1) (k + 1 + j) _ (by omega) (by omega))
      rw [e1, e2]
  have htermlo : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * x.length) false = false := by
    rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
    exact liftJ _ _ hR1 (xVisE_term_lo x (k + 1) _)
  have htermhi : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 2 + 4 * x.length + 1) false = true := by
    rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
    exact liftJ _ _ hR1 (xVisE_term_hi x (k + 1) _)
  have hR3fact : ∀ i, i < k →
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * i) false
      = (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * i + 1) false := by
    intro i hi
    have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * i) false = true := by
      rw [show 2 * N + 4 * x.length + 4 + 2 * i
          = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega, ← jsT_zero N k]
      exact liftJ2 _ _ _ hR1 hR2' (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
    have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * i + 1) false = true := by
      rw [show 2 * N + 4 * x.length + 4 + 2 * i + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * i + 1)) from by omega, ← jsT_zero N k]
      exact liftJ2 _ _ _ hR1 hR2'
        (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
    rw [e1, e2]
  have hR3m1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 4 * x.length + 4 + 2 * k) false = false := by
    rw [show 2 * N + 4 * x.length + 4 + 2 * k = 2 * N + 2 + (4 * x.length + 2 + 2 * k)
        from by omega, ← jsT_zero N k]
    exact liftJ2 _ _ _ hR1 hR2' (jsE_m_lo N k 0 _ (by omega))
  have hR3m2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
      (2 * N + 4 * x.length + 4 + 2 * k + 1) false = true := by
    rw [show 2 * N + 4 * x.length + 4 + 2 * k + 1
        = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega, ← jsT_zero N k]
    exact liftJ2 _ _ _ hR1 hR2' (jsE_m_hi N k 0 _ (by omega))
  have hpad : ∀ i, i < (N - k) + OUT.length →
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i) false
      = (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
        (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i + 1) false := by
    intro i hi
    rcases Nat.lt_or_ge i (N - k) with hilt | hige
    · have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i) false = false := by
        rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i
            = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i)) from by omega,
          ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
          (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i + 1) false = false := by
        rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i + 1
            = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i + 1)) from by omega,
          ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega)
          (by omega) (by omega) (by omega))
      rw [e1, e2]
    · rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i
          = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) from by omega,
        show 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1
          = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1 from rfl]
      exact preD3_data_eq (cntT N (k + 1)) (xVis x (k + 1)) (jT N k) OUT
        (4 * N + 4 * x.length + 6) (i - (N - k)) hq3 (by omega)
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (xVis x (k + 1)) (jT N k) OUT
    (4 * N + 4 * x.length + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (xVis x (k + 1)) (jT N k) OUT
    (4 * N + 4 * x.length + 6) hq3
  have hsn := writes_snoc3 (cntT N (k + 1)) (xVis x (k + 1)) (jT N k) OUT
    (4 * N + 4 * x.length + 6) hq3
  rw [show 4 * N + 4 * x.length + 2 * OUT.length + 12
      = 2 * N + (2 + (4 * k + (4 + (2 * (2 * (x.length - k - 1)) + (2 + (2 * k + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4))))))))) from by omega,
    run_add, r1, run_add, r2, run_add, r3]
  cases hv : x.getD k false with
  | false =>
    have r4 := il_four_mark0 (body := body) (idx := idx) (s := if k = 0 then false else true)
      (p := 2 * N + 2 + 4 * k)
      (T := cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT)))
      (by rw [hvlo, hv]) (by rw [hvhi, hv]) hclo hchi
    rw [hwmark] at r4
    have r5 := il_scanRF1s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 4 * k + 4) (2 * (x.length - k - 1)) idx true hseek
    rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * (x.length - k - 1))
        = 2 * N + 2 + 4 * x.length from by omega] at r5
    have r6 := il_crossSRF1 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 2 + 4 * k + 4) true (2 * (x.length - k - 1)))
      (p := 2 * N + 2 + 4 * x.length) htermlo htermhi
    rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at r6
    have r7 := il_scanRF2s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4) k idx false hR3fact
    have r8 := il_crossSRF2 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 4 * x.length + 4) false k)
      (p := 2 * N + 4 * x.length + 4 + 2 * k) hR3m1 hR3m2
    have r9 := il_scanRF3s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4 + 2 * k + 2) ((N - k) + OUT.length) idx false hpad
    rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
        = 4 * N + 4 * x.length + 6 + 2 * OUT.length from by omega] at r9
    have r10 := il_detectRF3 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 4 * x.length + 4 + 2 * k + 2) false ((N - k) + OUT.length))
      (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length) hm1 hm2
    have r11 := il_four_RF (body := body) (idx := idx) (s := false)
      (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
      (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
    rw [hsn false] at r11
    rw [run_add, r4, run_add, r5, run_add, r6, run_add, r7, run_add, r8, run_add, r9,
      run_add, r10, r11]
  | true =>
    have r4 := il_four_mark1 (body := body) (idx := idx) (s := if k = 0 then false else true)
      (p := 2 * N + 2 + 4 * k)
      (T := cntT N (k + 1) ++ (xVis x k ++ (jT N k ++ encodeD OUT)))
      (by rw [hvlo, hv]) (by rw [hvhi, hv]) hclo hchi
    rw [hwmark] at r4
    have r5 := il_scanRT1s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 4 * k + 4) (2 * (x.length - k - 1)) idx true hseek
    rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * (x.length - k - 1))
        = 2 * N + 2 + 4 * x.length from by omega] at r5
    have r6 := il_crossSRT1 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 2 + 4 * k + 4) true (2 * (x.length - k - 1)))
      (p := 2 * N + 2 + 4 * x.length) htermlo htermhi
    rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at r6
    have r7 := il_scanRT2s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4) k idx false hR3fact
    have r8 := il_crossSRT2 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 4 * x.length + 4) false k)
      (p := 2 * N + 4 * x.length + 4 + 2 * k) hR3m1 hR3m2
    have r9 := il_scanRT3s body
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4 + 2 * k + 2) ((N - k) + OUT.length) idx false hpad
    rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
        = 4 * N + 4 * x.length + 6 + 2 * OUT.length from by omega] at r9
    have r10 := il_detectRT3 (body := body) (idx := idx)
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
        (2 * N + 4 * x.length + 4 + 2 * k + 2) false ((N - k) + OUT.length))
      (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length) hm1 hm2
    have r11 := il_four_RT (body := body) (idx := idx) (s := false)
      (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
      (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k ++ encodeD OUT)))
    rw [hsn true] at r11
    rw [run_add, r4, run_add, r5, run_add, r6, run_add, r7, run_add, r8, run_add, r9,
      run_add, r10, r11]

/-- **The read stage, past the end** (`|x| ≤ k`): the terminator falls into the `false` track at the
**same clock**. -/
theorem il_read_past (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k : ℕ) (hk : k < N) (x : List Bool) (hkx : x.length ≤ k) (OUT : List Bool) (s : Bool) :
    run (initLoopMachine body) (4 * N + 4 * x.length + 2 * OUT.length + 12)
      ⟨(47, idx, s), 0, cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(79, idx, false), 0, cntT N (k + 1)
          ++ (xVis x x.length ++ (jT N k ++ encodeD (OUT ++ [x.getD k false])))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2' : (xVis x x.length).length = 4 * x.length + 2 := xVis_length x x.length
  have hq3 : (cntT N (k + 1)).length + (xVis x x.length).length + (jT N k).length
      = 4 * N + 4 * x.length + 6 := by
    rw [hR1, hR2', jT_length N k (by omega)]; omega
  have r1 := il_skipR1rs body
    (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r1
  have r2 := il_crossR1r (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r3 := il_visiteds body
    (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))) (2 * N + 2) x.length
    idx false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 3 = 2 * N + 2 + (4 * i + 3) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_hi_vis x x.length i _ hi hi)⟩)
  have r4 := il_two_toRF (body := body) (idx := idx)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x x.length _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x x.length _))
  rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at r4
  have r5 := il_scanRF2s body
    (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
    (2 * N + 4 * x.length + 4) k idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 4 * x.length + 4 + 2 * i) false = true := by
        rw [show 2 * N + 4 * x.length + 4 + 2 * i
            = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2'
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 4 * x.length + 4 + 2 * i + 1) false = true := by
        rw [show 2 * N + 4 * x.length + 4 + 2 * i + 1
            = 2 * N + 2 + (4 * x.length + 2 + (2 * i + 1)) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2'
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have r6 := il_crossSRF2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4) false k)
    (p := 2 * N + 4 * x.length + 4 + 2 * k)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 4 * x.length + 4 + 2 * k
          = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 4 * x.length + 4 + 2 * k + 1
          = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 1)) from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_m_hi N k 0 _ (by omega)))
  have r7 := il_scanRF3s body
    (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
    (2 * N + 4 * x.length + 4 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hR2' (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (4 * x.length + 2 + (2 * k + 2 + 2 * i + 1)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hR2' (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * i
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 4 * x.length + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (xVis x x.length) (jT N k) OUT
          (4 * N + 4 * x.length + 6) (i - (N - k)) hq3 (by omega))
  rw [show 2 * N + 4 * x.length + 4 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 4 * N + 4 * x.length + 6 + 2 * OUT.length from by omega] at r7
  have r8 := il_detectRF3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
      (2 * N + 4 * x.length + 4 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
    (preD3_mark_lo (cntT N (k + 1)) (xVis x x.length) (jT N k) OUT
      (4 * N + 4 * x.length + 6) hq3)
    (preD3_mark_hi (cntT N (k + 1)) (xVis x x.length) (jT N k) OUT
      (4 * N + 4 * x.length + 6) hq3)
  have r9 := il_four_RF (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 * x.length + 6 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k ++ encodeD OUT)))
  have hsn := writes_snoc3 (cntT N (k + 1)) (xVis x x.length) (jT N k) OUT
    (4 * N + 4 * x.length + 6) hq3 false
  rw [show [false] = [x.getD k false] from by rw [List.getD_eq_default _ _ hkx]] at hsn
  rw [hsn] at r9
  rw [show 4 * N + 4 * x.length + 2 * OUT.length + 12
      = 2 * N + (2 + (4 * x.length + (2 + (2 * k + (2 + (2 * ((N - k) + OUT.length)
          + (2 + 4))))))) from by omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, r9]

/-! ## The instruction segment, the round, and the loop -/

def ilInstrCost (body : List (Option Bool)) (N X k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n none with
  | some _ => 4 * N + 4 * X + 2 * (L + (progOutN body k n).length) + 13
  | none => iljCost N X k (L + (progOutN body k n).length)

def ilSegN (body : List (Option Bool)) (N X k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ilSegN body N X k L n + ilInstrCost body N X k L n

/-- **The segment invariant** (cursor state `m` untouched). -/
theorem il_run_instrs (body : List (Option Bool)) (N k : ℕ) (hk : k < N) (x : List Bool)
    (m : ℕ) (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (initLoopMachine body) (ilSegN body N x.length k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N (k + 1)
        ++ (xVis x m ++ (jT N k ++ encodeD out'))⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT N (k + 1) ++ (xVis x m ++ (jT N k ++ encodeD (out' ++ progOutN body k n)))⟩ := by
  induction n with
  | zero => simp only [ilSegN]; rw [run_zero]; simp [progOutN]
  | succ n ih =>
    rw [show ilSegN body N x.length k out'.length (n + 1)
        = ilSegN body N x.length k out'.length n + ilInstrCost body N x.length k out'.length n
        from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n none with
    | none =>
      have hin := il_instr_spliceJ body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N k hk x m (out' ++ progOutN body k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN body k n ++ encodeNat k = progOutN body k (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [ilInstrCost, hp]
      rw [hin]
      simp
    | some b =>
      have hin := il_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N k hk x m (out' ++ progOutN body k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN body k n ++ [b] = progOutN body k (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [ilInstrCost, hp]
      rw [hin]
      simp

def ilRoundCost (body : List (Option Bool)) (N X k L : ℕ) : ℕ :=
  (2 * k + 2) + (ilSegN body N X k L body.length
    + (1 + ((4 * N + 4 * X + 2 * (L + (progOutN body k body.length).length) + 12)
        + (2 * N + 4 * X + 2 * k + 8))))

/-- **A found round** (`k < |x|`): mark, body, read the `k`-th input bit, increment. -/
theorem il_round_found (body : List (Option Bool)) (N k : ℕ) (hk : k < N) (x : List Bool)
    (hkx : k < x.length) (out' : List Bool) (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (initLoopMachine body) (ilRoundCost body N x.length k out'.length)
      ⟨(0, ptrIn, s), 0, cntT N k ++ (xVis x k ++ (jT N k ++ encodeD out'))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, cntT N (k + 1)
          ++ (xVis x (k + 1) ++ (jT N (k + 1)
            ++ encodeD (out' ++ (progOut body k ++ [x.getD k false]))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2' : (xVis x (k + 1)).length = 4 * x.length + 2 := xVis_length x (k + 1)
  have r1 := il_skipBs body (cntT N k ++ (xVis x k ++ (jT N k ++ encodeD out'))) 0 k ptrIn s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := il_markB (body := body) (idx := ptrIn) (s := if k = 0 then s else true)
    (p := 2 * k) (T := cntT N k ++ (xVis x k ++ (jT N k ++ encodeD out')))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at r2
  have r3 := il_run_instrs body N k hk x k out' body.length (le_refl _) true
  have r4 := il_dispatch_read (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT N (k + 1) ++ (xVis x k ++ (jT N k
      ++ encodeD (out' ++ progOutN body k body.length))))
    (Nat.lt_irrefl _)
  have r5 := il_read_found body ⟨body.length, Nat.lt_succ_self _⟩ N k hk x hkx
    (out' ++ progOutN body k body.length) (if body.length = 0 then true else false)
  rw [List.length_append] at r5
  have r6 := il_skipR1is body (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false])))) 0 N
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r6
  have r7 := il_crossR1i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r8 := il_unitsUi body (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (2 * N + 2) x.length ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x (k + 1) i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x (k + 1) i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x (k + 1) i _ hi)⟩)
  have r9 := il_crossUUi (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x (k + 1) _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x (k + 1) _))
  have r10 := il_walkIs body (cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (2 * N + 2 + 4 * x.length + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i
          = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega, ← jsT_zero N k]
      exact liftJ2 _ _ _ hR1 hR2'
        (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r11 := il_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * N + 2 + (4 * x.length + 2 + 2 * k))
    (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (by rw [← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right2 (cntT N (k + 1)) (xVis x (k + 1))
      (jT N k ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))
      (2 * N + 2) (4 * x.length + 2) (2 * k) true true false true hR1 hR2'
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r11
  rw [show ilRoundCost body N x.length k out'.length
      = 2 * k + (2 + (ilSegN body N x.length k out'.length body.length + (1
          + ((4 * N + 4 * x.length
              + 2 * (out'.length + (progOutN body k body.length).length) + 12)
            + (2 * N + (2 + (4 * x.length + (2 + (2 * k + 4)))))))))
      from by simp only [ilRoundCost]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, run_add, r9, run_add, r10,
    show 2 * N + 2 + 4 * x.length + 2 + 2 * k
      = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega,
    r11, List.append_assoc, progOutN_full]

/-- **A past-the-end round** (`|x| ≤ k`). -/
theorem il_round_past (body : List (Option Bool)) (N k : ℕ) (hk : k < N) (x : List Bool)
    (hkx : x.length ≤ k) (out' : List Bool) (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (initLoopMachine body) (ilRoundCost body N x.length k out'.length)
      ⟨(0, ptrIn, s), 0, cntT N k ++ (xVis x x.length ++ (jT N k ++ encodeD out'))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, cntT N (k + 1)
          ++ (xVis x x.length ++ (jT N (k + 1)
            ++ encodeD (out' ++ (progOut body k ++ [x.getD k false]))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hR2' : (xVis x x.length).length = 4 * x.length + 2 := xVis_length x x.length
  have r1 := il_skipBs body (cntT N k ++ (xVis x x.length ++ (jT N k ++ encodeD out'))) 0 k
    ptrIn s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := il_markB (body := body) (idx := ptrIn) (s := if k = 0 then s else true)
    (p := 2 * k) (T := cntT N k ++ (xVis x x.length ++ (jT N k ++ encodeD out')))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at r2
  have r3 := il_run_instrs body N k hk x x.length out' body.length (le_refl _) true
  have r4 := il_dispatch_read (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD (out' ++ progOutN body k body.length))))
    (Nat.lt_irrefl _)
  have r5 := il_read_past body ⟨body.length, Nat.lt_succ_self _⟩ N k hk x hkx
    (out' ++ progOutN body k body.length) (if body.length = 0 then true else false)
  rw [List.length_append] at r5
  have r6 := il_skipR1is body (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false])))) 0 N
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r6
  have r7 := il_crossR1i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r8 := il_unitsUi body (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (2 * N + 2) x.length ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hR1 (xVisE_val_lo x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_val_hi x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hR1 (xVisE_cur_lo x x.length i _ hi)⟩)
  have r9 := il_crossUUi (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if x.length = 0 then false else true) (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hR1 (xVisE_term_lo x x.length _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hR1 (xVisE_term_hi x x.length _))
  have r10 := il_walkIs body (cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (2 * N + 2 + 4 * x.length + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 4 * x.length + 2 + 2 * i
          = 2 * N + 2 + (4 * x.length + 2 + 2 * i) from by omega, ← jsT_zero N k]
      exact liftJ2 _ _ _ hR1 hR2'
        (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r11 := il_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * N + 2 + (4 * x.length + 2 + 2 * k))
    (T := cntT N (k + 1) ++ (xVis x x.length ++ (jT N k
      ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))))
    (by rw [← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hR2' (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right2 (cntT N (k + 1)) (xVis x x.length)
      (jT N k ++ encodeD ((out' ++ progOutN body k body.length) ++ [x.getD k false]))
      (2 * N + 2) (4 * x.length + 2) (2 * k) true true false true hR1 hR2'
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r11
  rw [show ilRoundCost body N x.length k out'.length
      = 2 * k + (2 + (ilSegN body N x.length k out'.length body.length + (1
          + ((4 * N + 4 * x.length
              + 2 * (out'.length + (progOutN body k body.length).length) + 12)
            + (2 * N + (2 + (4 * x.length + (2 + (2 * k + 4)))))))))
      from by simp only [ilRoundCost]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, run_add, r9, run_add, r10,
    show 2 * N + 2 + 4 * x.length + 2 + 2 * k
      = 2 * N + 2 + (4 * x.length + 2 + 2 * k) from by omega,
    r11, List.append_assoc, progOutN_full]

/-! ## The rounds, the finale, and the top theorem -/

/-- The `x`-free per-round output length. -/
def ilOutLen (body : List (Option Bool)) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ilOutLen body k + ((progOutN body k body.length).length + 1)

theorem initOutN_length (body : List (Option Bool)) (x : List Bool) (k : ℕ) :
    (initOutN body x k).length = ilOutLen body k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show initOutN body x (k + 1)
        = initOutN body x k ++ (progOut body k ++ [x.getD k false]) from rfl,
      List.length_append, List.length_append, ih, ← progOutN_full]
    rfl

def ilClockN (body : List (Option Bool)) (N X Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ilClockN body N X Lout k + ilRoundCost body N X k (Lout + ilOutLen body k)

/-- **The rounds invariant**, cursor at `min k |x|`. -/
theorem il_run_rounds (body : List (Option Bool)) (N : ℕ) (x out : List Bool) (k : ℕ)
    (hk : k ≤ N) (s : Bool) :
    run (initLoopMachine body) (ilClockN body N x.length out.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N 0 ++ (xVis x 0 ++ (jT N 0 ++ encodeD out))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT N k ++ (xVis x (min k x.length)
            ++ (jT N k ++ encodeD (out ++ initOutN body x k)))⟩ := by
  induction k with
  | zero => simp only [ilClockN]; rw [run_zero]; simp [initOutN]
  | succ k ih =>
    rcases Nat.lt_or_ge k x.length with hkx | hkx
    · have hrd := il_round_found body N k (by omega) x hkx (out ++ initOutN body x k)
        ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
      rw [List.length_append, initOutN_length, List.append_assoc,
        show initOutN body x k ++ (progOut body k ++ [x.getD k false])
          = initOutN body x (k + 1) from rfl] at hrd
      rw [show ilClockN body N x.length out.length (k + 1)
          = ilClockN body N x.length out.length k
              + ilRoundCost body N x.length k (out.length + ilOutLen body k) from rfl,
        run_add, ih (by omega), show min k x.length = k from by omega, hrd,
        show min (k + 1) x.length = k + 1 from by omega, if_neg (by omega)]
    · have hrd := il_round_past body N k (by omega) x hkx (out ++ initOutN body x k)
        ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
      rw [List.length_append, initOutN_length, List.append_assoc,
        show initOutN body x k ++ (progOut body k ++ [x.getD k false])
          = initOutN body x (k + 1) from rfl] at hrd
      rw [show ilClockN body N x.length out.length (k + 1)
          = ilClockN body N x.length out.length k
              + ilRoundCost body N x.length k (out.length + ilOutLen body k) from rfl,
        run_add, ih (by omega), show min k x.length = x.length from by omega, hrd,
        show min (k + 1) x.length = x.length from by omega, if_neg (by omega)]

def ilClock (body : List (Option Bool)) (N X Lout : ℕ) : ℕ :=
  ilClockN body N X Lout N + (2 * N + (2 + (2 * N + (2 + (4 * X + 2)))))

/-- **THE INIT-FAMILY ENGINE RUNS TO COMPLETION**: bound healed, every cursor healed, variable
saturated, and the output extended by `initOut body x N` — the body's denotation plus the input bit,
per round. -/
theorem initLoop_run (body : List (Option Bool)) (N : ℕ) (x out : List Bool) :
    run (initLoopMachine body) (ilClock body N x.length out.length)
      (init (initLoopMachine body) (unaryD N ++ (xVis x 0 ++ (jT N 0 ++ encodeD out))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 2 + 4 * x.length + 1,
          unaryD N ++ (xVis x 0 ++ (unaryD N ++ encodeD (out ++ initOut body x N)))⟩ := by
  rw [init_il]
  rw [show (unaryD N ++ (xVis x 0 ++ (jT N 0 ++ encodeD out)) : List Bool)
      = cntT N 0 ++ (xVis x 0 ++ (jT N 0 ++ encodeD out)) from by rw [cntT_zero]]
  simp only [ilClock]
  have hua : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have f1 := il_skipBs body (cntT N N ++ (xVis x (min N x.length)
      ++ (jT N N ++ encodeD (out ++ initOutN body x N)))) 0 N ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := il_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (xVis x (min N x.length)
      ++ (jT N N ++ encodeD (out ++ initOutN body x N))))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have f3 := il_healBs body N (xVis x (min N x.length)
      ++ (jT N N ++ encodeD (out ++ initOutN body x N))) ⟨0, Nat.succ_pos _⟩ false N
    (le_refl N)
  have f4 := il_doneHB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := hlT N N ++ (xVis x (min N x.length)
      ++ (jT N N ++ encodeD (out ++ initOutN body x N))))
    (hlE_cm_lo N _) (hlE_cm_hi N _)
  have f5 := il_healXs body (unaryD N) N x (min N x.length)
    (jT N N ++ encodeD (out ++ initOutN body x N)) hua (by omega) ⟨0, Nat.succ_pos _⟩
    false (min N x.length) (le_refl _)
  rw [xHl_zero, xHl_sat x (min N x.length) (min N x.length) (le_refl _)] at f5
  have f6 := il_healSkips body (unaryD N ++ (xVis x 0
      ++ (jT N N ++ encodeD (out ++ initOutN body x N))))
    (2 * N + 2 + 4 * min N x.length) (x.length - min N x.length) ⟨0, Nat.succ_pos _⟩
    (if min N x.length = 0 then false else true)
    (fun i hi => ⟨x.getD (min N x.length + i) false, by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i
            = 2 * N + 2 + (4 * (min N x.length + i)) from by omega]
        exact liftJ _ _ hua (xVisE_val_lo x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 1
            = 2 * N + 2 + (4 * (min N x.length + i) + 1) from by omega]
        exact liftJ _ _ hua (xVisE_val_hi x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 2
            = 2 * N + 2 + (4 * (min N x.length + i) + 2) from by omega]
        exact liftJ _ _ hua (xVisE_cur_lo x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 3
            = 2 * N + 2 + (4 * (min N x.length + i) + 3) from by omega]
        exact liftJ _ _ hua (xVisE_cur_hi_unvis x 0 _ _ (by omega) (by omega))⟩)
  rw [show 2 * N + 2 + 4 * min N x.length + 4 * (x.length - min N x.length)
      = 2 * N + 2 + 4 * x.length from by omega] at f6
  have f7 := il_two_healDone (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if x.length - min N x.length = 0 then (if min N x.length = 0 then false else true)
      else true)
    (p := 2 * N + 2 + 4 * x.length)
    (T := unaryD N ++ (xVis x 0 ++ (jT N N ++ encodeD (out ++ initOutN body x N))))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hua (xVisE_term_lo x 0 _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hua (xVisE_term_hi x 0 _))
  rw [run_add, il_run_rounds body N x out N (le_refl N) false, ite_self,
    show 2 * N + (2 + (2 * N + (2 + (4 * x.length + 2))))
      = 2 * N + (2 + (2 * N + (2 + (4 * min N x.length
          + (4 * (x.length - min N x.length) + 2))))) from by omega,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, run_add, f4, hlT_last,
    run_add, f5, run_add, f6, f7, jT_full,
    show initOut body x N = initOutN body x N from rfl]

/-- The machine **halts by itself** at its clock. -/
theorem initLoop_halted (body : List (Option Bool)) (N : ℕ) (x out : List Bool) :
    (initLoopMachine body).halt
      (run (initLoopMachine body) (ilClock body N x.length out.length)
        (init (initLoopMachine body)
          (unaryD N ++ (xVis x 0 ++ (jT N 0 ++ encodeD out))))).st = true := by
  rw [initLoop_run]; rfl

/-! ## Polynomial clock bounds -/

/-- The per-instruction cap. -/
def ilCap (N X LM : ℕ) : ℕ :=
  N * (4 * N + 4 * X + 2 * LM + 12 + 2 * N) + (4 * N + 4 * X + 2 * LM + 2 * N + 12)
    + (2 * N + 4 * X + 2 * N + 6) + (4 * N + 4 * X + 2 * LM + 13)

theorem ilInstrCost_le (body : List (Option Bool)) (N X k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (N + 1) ≤ LM) :
    ilInstrCost body N X k L n ≤ ilCap N X LM := by
  have hlen : (progOutN body k n).length ≤ body.length * (N + 1) :=
    le_trans (progOutN_length_le body k n) (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n none with
  | none =>
    have h1 := lp3SpRounds_le (4 * N + 4 * X + 2 * (L + (progOutN body k n).length) + 12)
      (4 * N + 4 * X + 2 * LM + 12) k N (by omega) (by omega)
    have h2 : k * (4 * N + 4 * X + 2 * LM + 12 + 2 * N)
        ≤ N * (4 * N + 4 * X + 2 * LM + 12 + 2 * N) := Nat.mul_le_mul_right _ (by omega)
    simp only [ilInstrCost, hp, iljCost, ilCap]
    omega
  | some b =>
    simp only [ilInstrCost, hp, ilCap]
    omega

theorem ilSegN_le (body : List (Option Bool)) (N X k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (N + 1) ≤ LM) :
    ilSegN body N X k L n ≤ n * ilCap N X LM := by
  induction n with
  | zero => simp [ilSegN]
  | succ n ih =>
    calc ilSegN body N X k L (n + 1) = ilSegN body N X k L n + ilInstrCost body N X k L n :=
        rfl
      _ ≤ n * ilCap N X LM + ilCap N X LM :=
          Nat.add_le_add (ih (by omega)) (ilInstrCost_le body N X k L n LM hk (by omega) hL)
      _ = (n + 1) * ilCap N X LM := by ring

theorem ilOutLen_le (body : List (Option Bool)) (N k : ℕ) (hk : k ≤ N) :
    ilOutLen body k ≤ k * (body.length * (N + 1) + 1) := by
  induction k with
  | zero => simp [ilOutLen]
  | succ k ih =>
    have hone : (progOutN body k body.length).length ≤ body.length * (N + 1) :=
      le_trans (progOutN_length_le body k body.length)
        (Nat.mul_le_mul_left _ (by omega))
    calc ilOutLen body (k + 1)
        = ilOutLen body k + ((progOutN body k body.length).length + 1) := rfl
      _ ≤ k * (body.length * (N + 1) + 1) + (body.length * (N + 1) + 1) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (k + 1) * (body.length * (N + 1) + 1) := by ring

theorem ilRoundCost_le (body : List (Option Bool)) (N X k L LM : ℕ) (hk : k < N)
    (hL : L + body.length * (N + 1) ≤ LM) :
    ilRoundCost body N X k L
      ≤ body.length * ilCap N X LM + (10 * N + 8 * X + 2 * LM + 23) := by
  have h := ilSegN_le body N X k L body.length LM hk (le_refl _) hL
  have hlen : (progOutN body k body.length).length ≤ body.length * (N + 1) :=
    le_trans (progOutN_length_le body k body.length) (Nat.mul_le_mul_left _ (by omega))
  simp only [ilRoundCost]
  omega

/-- **The init-engine clock is polynomial.** -/
theorem ilClock_le (body : List (Option Bool)) (N X Lout : ℕ) :
    ilClock body N X Lout
      ≤ N * (body.length * ilCap N X (Lout + N * (body.length * (N + 1) + 1)
            + body.length * (N + 1)) + (10 * N + 8 * X + 2 * (Lout
            + N * (body.length * (N + 1) + 1) + body.length * (N + 1)) + 23))
        + (4 * N + 4 * X + 6) := by
  have hrounds : ∀ k, k ≤ N → ilClockN body N X Lout k
      ≤ k * (body.length * ilCap N X (Lout + N * (body.length * (N + 1) + 1)
            + body.length * (N + 1)) + (10 * N + 8 * X + 2 * (Lout
            + N * (body.length * (N + 1) + 1) + body.length * (N + 1)) + 23)) := by
    intro k hk
    induction k with
    | zero => simp [ilClockN]
    | succ k ih =>
      have hLk : (Lout + ilOutLen body k) + body.length * (N + 1)
          ≤ Lout + N * (body.length * (N + 1) + 1) + body.length * (N + 1) := by
        have h1 : ilOutLen body k ≤ k * (body.length * (N + 1) + 1) :=
          ilOutLen_le body N k (by omega)
        have h2 : k * (body.length * (N + 1) + 1) ≤ N * (body.length * (N + 1) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      calc ilClockN body N X Lout (k + 1)
          = ilClockN body N X Lout k + ilRoundCost body N X k (Lout + ilOutLen body k) :=
            rfl
        _ ≤ k * (body.length * ilCap N X (Lout + N * (body.length * (N + 1) + 1)
                + body.length * (N + 1)) + (10 * N + 8 * X + 2 * (Lout
                + N * (body.length * (N + 1) + 1) + body.length * (N + 1)) + 23))
            + (body.length * ilCap N X (Lout + N * (body.length * (N + 1) + 1)
                + body.length * (N + 1)) + (10 * N + 8 * X + 2 * (Lout
                + N * (body.length * (N + 1) + 1) + body.length * (N + 1)) + 23)) :=
            Nat.add_le_add (ih (by omega))
              (ilRoundCost_le body N X k (Lout + ilOutLen body k) _ (by omega) hLk)
        _ = (k + 1) * (body.length * ilCap N X (Lout + N * (body.length * (N + 1) + 1)
                + body.length * (N + 1)) + (10 * N + 8 * X + 2 * (Lout
                + N * (body.length * (N + 1) + 1) + body.length * (N + 1)) + 23)) := by
            ring
  have h := hrounds N (le_refl N)
  simp only [ilClock]
  omega

/-! ## THE INIT FAMILY

`initFormula_members`: one fixed state unit, one fixed head unit, then the input-spliced cell units.
The cell-unit stream is one `initLoopMachine` run; the two fixed clauses are literal bit-programs for
the straight-line engine. -/

/-- The cell-unit body: `encodeNat 1 · encodeNat 0 · [splice p] · encodeNat 0 · [input bit]`. -/
def initCellBody : List (Option Bool) :=
  [some true, some false, some false, none, some false]

/-- **Round `p` emits exactly the `p`-th init cell fix.** -/
theorem initCell_round (p : ℕ) (s : Bool) :
    progOut initCellBody p ++ [s] = encodeClause' [(cellVar 0 p, s)] := by
  rw [encodeClause'_unit_cell]
  simp [initCellBody, progOut, instrOut, encodeNat, List.append_assoc]

/-- **The input-dependent part of the init family factors through the loop denotation.** -/
theorem initCell_split (x : List Bool) (N : ℕ) :
    initOut initCellBody x N
      = ((List.range N).map (fun p => encodeClause' [(cellVar 0 p, x.getD p false)])).flatten := by
  rw [initOut_eq_flatten]
  exact congrArg List.flatten
    (List.map_congr_left (fun p _ => initCell_round p (x.getD p false)))

/-- **THE INIT FAMILY EMITTER**: one run emits every input-spliced cell fix
`[(cellVar 0 p, x.getD p false)]`, `p = 0..N-1`, in order — bound healed, cursors healed. -/
theorem initCell_family_run (N : ℕ) (x out : List Bool) :
    run (initLoopMachine initCellBody) (ilClock initCellBody N x.length out.length)
      (init (initLoopMachine initCellBody)
        (unaryD N ++ (xVis x 0 ++ (jT N 0 ++ encodeD out))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 2 + 4 * x.length + 1,
          unaryD N ++ (xVis x 0 ++ (unaryD N ++ encodeD (out
            ++ ((List.range N).map (fun p =>
                encodeClause' [(cellVar 0 p, x.getD p false)])).flatten)))⟩ := by
  rw [initLoop_run, initCell_split]

/-- The fixed start-state unit clause as a straight-line program (for `progMachine`). -/
noncomputable def initStateProg (M : Machine) : List (Option Bool) :=
  (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]).map some

theorem initStateProg_out (M : Machine) (v : ℕ) :
    progOut (initStateProg M) v
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)] :=
  progOut_map_some _ v

/-- The fixed head unit clause as a straight-line program. -/
def initHeadProg : List (Option Bool) := (encodeClause' [(headVar 0 0, true)]).map some

theorem initHeadProg_out (v : ℕ) :
    progOut initHeadProg v = encodeClause' [(headVar 0 0, true)] :=
  progOut_map_some _ v

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop