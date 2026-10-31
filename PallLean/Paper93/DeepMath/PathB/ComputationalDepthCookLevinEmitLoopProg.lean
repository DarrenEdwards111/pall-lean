import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitProg

/-!
# Cook–Levin M2 emitter — the looped program emitter

The looped family emitter: fuse E4's counted-loop control and live-variable machinery with the E5 program
body.  `loopProgMachine body` runs

    for k in 0..N-1:  execute `body`,

where `body : List (Option Bool)` is a hard-wired instruction list executed against the **live loop
variable**: instruction `some b` appends the bit `b` to the doubled output; instruction `none` **splices
the current round index** `k` (`encodeNat k`) via the `jsT` marking discipline on the variable region,
healing it per instruction.  Each round ends with the E4 in-place increment (`jT_incr`), so the variable
region never grows; the loop is driven by the countdown-marking bound.

Layout: `cntT N k ++ (jT N k ++ encodeD out)` — bound, live variable, output.  **Top theorem**
(`loopProg_run`): from `unaryD N ++ (jT N 0 ++ encodeD out)` the machine halts by itself at the explicit
clock with tape **exactly** `unaryD N ++ (unaryD N ++ encodeD (out ++ loopOut body N))` — the per-round
program denotations `progOut body 0, …, progOut body (N-1)` (of `...EmitProg`) appended in order, the
bound healed, the variable at its saturated value `jT N N = unaryD N`.  Coherence: `body = [none]`
re-derives the E4-ii range emission (`loopOut [none] N = rangeEnc N`).

This is the loop-shaped families' engine: a family clause's per-iteration block stream (pinned by the
E3 template layouts) is a `body`; the two-source extension (a second, static splice region — the outer
loop's live variable at nesting time) follows this construction verbatim.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg

/-! ## The loop denotation -/

/-- The first `k` rounds' output: the body's denotation at each round index in order. -/
def loopOutN (body : List (Option Bool)) : ℕ → List Bool
  | 0 => []
  | k + 1 => loopOutN body k ++ progOut body k

/-- The whole loop's output. -/
def loopOut (body : List (Option Bool)) (N : ℕ) : List Bool := loopOutN body N

/-- The mapped form consumed by the template layouts. -/
theorem loopOut_eq_flatten (body : List (Option Bool)) (N : ℕ) :
    loopOut body N = ((List.range N).map (fun k => progOut body k)).flatten := by
  show loopOutN body N = _
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show loopOutN body (N + 1) = loopOutN body N ++ progOut body N from rfl, ih,
      List.range_succ, List.map_append, List.flatten_append]
    simp

/-- **Coherence with E4-ii**: the one-instruction splice body re-derives the range emission. -/
theorem loopOut_none_eq_rangeEnc (N : ℕ) : loopOut [none] N = rangeEnc N := by
  show loopOutN [none] N = rangeEnc N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show loopOutN [none] (N + 1) = loopOutN [none] N ++ progOut [none] N from rfl, ih,
      progOut_none, rangeEnc]

/-! ## The machine

Control: `Fin 45 × Fin (|body|+1) × Bool` — phase, instruction pointer, stored cell.  Phase groups:
`0/1` the loop find (skip the bound's marks; mark its next pair and enter the body with the pointer
reset; boundary ⇒ the finale), `2` the instruction dispatch, `3–12` the append track (skip the bound,
cross the variable region and the padding+output by two boundary-event scans, snoc the bit, advance),
`13–34` the splice track (per emitted `true`: skip the bound, splice-mark the variable's next pair, seek
out by the two-event scan, snoc; on the value boundary the closing `false`; then the heal walk and
advance), `35–41` the in-place increment, `42/43` heal the bound, `44` = halt. -/

def loopProgMachine (body : List (Option Bool)) : Machine where
  State := Fin 45 × Fin (body.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 44)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 3)
         else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((42, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val none with
         | some _ => ((3, s.2.1, s.2.2), none, 2)
         | none => ((13, s.2.1, s.2.2), none, 2))
       else ((35, s.2.1, s.2.2), none, 2))
    else if s.1 = 3 then ((4, s.2.1, b), none, 1)
    else if s.1 = 4 then
      (if s.2.2 then ((3, s.2.1, s.2.2), none, 1)
       else (if b then ((5, s.2.1, s.2.2), none, 1) else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if b = s.2.2 then ((5, s.2.1, s.2.2), none, 1) else ((7, s.2.1, s.2.2), none, 1))
    else if s.1 = 7 then ((8, s.2.1, b), none, 1)
    else if s.1 = 8 then
      (if b = s.2.2 then ((7, s.2.1, s.2.2), none, 1) else ((9, s.2.1, s.2.2), none, 0))
    else if s.1 = 9 then ((10, s.2.1, s.2.2), some ((body.getD s.2.1.val none).getD false), 1)
    else if s.1 = 10 then ((11, s.2.1, s.2.2), some ((body.getD s.2.1.val none).getD false), 1)
    else if s.1 = 11 then ((12, s.2.1, s.2.2), some false, 1)
    else if s.1 = 12 then
      (if h : s.2.1.val + 1 < body.length + 1 then
        ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((44, s.2.1, s.2.2), some true, 2))
    else if s.1 = 13 then ((14, s.2.1, b), none, 1)
    else if s.1 = 14 then
      (if s.2.2 then ((13, s.2.1, s.2.2), none, 1)
       else (if b then ((15, s.2.1, s.2.2), none, 1) else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 15 then ((16, s.2.1, b), none, 1)
    else if s.1 = 16 then
      (if s.2.2 then
        (if b then ((17, s.2.1, s.2.2), some false, 1) else ((15, s.2.1, s.2.2), none, 1))
       else (if b then ((25, s.2.1, s.2.2), none, 1) else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 17 then ((18, s.2.1, b), none, 1)
    else if s.1 = 18 then
      (if b = s.2.2 then ((17, s.2.1, s.2.2), none, 1) else ((19, s.2.1, s.2.2), none, 1))
    else if s.1 = 19 then ((20, s.2.1, b), none, 1)
    else if s.1 = 20 then
      (if b = s.2.2 then ((19, s.2.1, s.2.2), none, 1) else ((21, s.2.1, s.2.2), none, 0))
    else if s.1 = 21 then ((22, s.2.1, s.2.2), some true, 1)
    else if s.1 = 22 then ((23, s.2.1, s.2.2), some true, 1)
    else if s.1 = 23 then ((24, s.2.1, s.2.2), some false, 1)
    else if s.1 = 24 then ((13, s.2.1, s.2.2), some true, 3)
    else if s.1 = 25 then ((26, s.2.1, b), none, 1)
    else if s.1 = 26 then
      (if b = s.2.2 then ((25, s.2.1, s.2.2), none, 1) else ((27, s.2.1, s.2.2), none, 0))
    else if s.1 = 27 then ((28, s.2.1, s.2.2), some false, 1)
    else if s.1 = 28 then ((29, s.2.1, s.2.2), some false, 1)
    else if s.1 = 29 then ((30, s.2.1, s.2.2), some false, 1)
    else if s.1 = 30 then ((31, s.2.1, s.2.2), some true, 3)
    else if s.1 = 31 then ((32, s.2.1, b), none, 1)
    else if s.1 = 32 then
      (if s.2.2 then ((31, s.2.1, s.2.2), none, 1)
       else (if b then ((33, s.2.1, s.2.2), none, 1) else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 33 then ((34, s.2.1, b), none, 1)
    else if s.1 = 34 then
      (if s.2.2 then
        (if b then ((44, s.2.1, s.2.2), none, 2) else ((33, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((44, s.2.1, s.2.2), none, 2))
             else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 35 then ((36, s.2.1, b), none, 1)
    else if s.1 = 36 then
      (if s.2.2 then ((35, s.2.1, s.2.2), none, 1)
       else (if b then ((37, s.2.1, s.2.2), none, 1) else ((44, s.2.1, s.2.2), none, 2)))
    else if s.1 = 37 then
      (if b then ((38, s.2.1, b), none, 1) else ((39, s.2.1, s.2.2), some true, 1))
    else if s.1 = 38 then ((37, s.2.1, s.2.2), none, 1)
    else if s.1 = 39 then ((40, s.2.1, s.2.2), some true, 1)
    else if s.1 = 40 then ((41, s.2.1, s.2.2), some false, 1)
    else if s.1 = 41 then ((0, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 42 then ((43, s.2.1, b), none, 1)
    else if s.1 = 43 then
      (if s.2.2 then
        (if b then ((44, s.2.1, false), none, 2) else ((42, s.2.1, true), some true, 1))
       else (if b then ((44, s.2.1, false), none, 2) else ((44, s.2.1, false), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lp (body : List (Option Bool)) (t : List Bool) :
    init (loopProgMachine body) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

/-! ### Step and pair-step lemmas -/

section Steps
variable {body : List (Option Bool)} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

/-- Loop find: skip a marked bound pair. -/
theorem lp_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProgMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- Loop find: mark the bound's next pair, reset the pointer, enter the dispatch. -/
theorem lp_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- Loop find: the bound is exhausted — enter the finale. -/
theorem lp_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(42, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_dispatch_some {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val none = some b) :
    run (loopProgMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = some b := by
    rwa [List.getD_eq_getElem body none h] at hp
  simp [step, loopProgMachine, moveHead, h, hp']

theorem lp_dispatch_none (h : idx.val < body.length)
    (hp : body.getD idx.val none = none) :
    run (loopProgMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(13, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = none := by
    rwa [List.getD_eq_getElem body none h] at hp
  simp [step, loopProgMachine, moveHead, h, hp']

theorem lp_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProgMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(35, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProgMachine, moveHead, h]

/-- The four lo-true region-skip phase pairs (append / splice / heal / increment tracks). -/
theorem lp_skipR1a (h1 : T.getD p false = true) :
    run (loopProgMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProgMachine, moveHead]; rfl

theorem lp_crossR1a (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_skipR1j (h1 : T.getD p false = true) :
    run (loopProgMachine body) 2 ⟨(13, idx, s), p, T⟩ = ⟨(13, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProgMachine, moveHead]; rfl

theorem lp_crossR1j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(13, idx, s), p, T⟩ = ⟨(15, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_skipR1h (h1 : T.getD p false = true) :
    run (loopProgMachine body) 2 ⟨(31, idx, s), p, T⟩ = ⟨(31, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProgMachine, moveHead]; rfl

theorem lp_crossR1h (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(31, idx, s), p, T⟩ = ⟨(33, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_skipR1i (h1 : T.getD p false = true) :
    run (loopProgMachine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(35, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProgMachine, moveHead]; rfl

theorem lp_crossR1i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(37, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- The equal-pair scans (four phase pairs). -/
theorem lp_scanA1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProgMachine body) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_crossA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProgMachine, moveHead, h2']

theorem lp_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProgMachine body) 2 ⟨(7, idx, s), p, T⟩
      = ⟨(7, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_detectA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProgMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

/-- The append snoc: four writes of the instruction's bit (doubled) and the closing marker, advancing
the pointer. -/
theorem lp_four_append (h : idx.val + 1 < body.length + 1) :
    run (loopProgMachine body) 4 ⟨(9, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p ((body.getD idx.val none).getD false))
            (p + 1) ((body.getD idx.val none).getD false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e9 : step (loopProgMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, s), p + 1, writeAt T p ((body.getD idx.val none).getD false)⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  have e10 : ∀ p' T', step (loopProgMachine body) ⟨(10, idx, s), p', T'⟩
      = ⟨(11, idx, s), p' + 1, writeAt T' p' ((body.getD idx.val none).getD false)⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e11 : ∀ p' T', step (loopProgMachine body) ⟨(11, idx, s), p', T'⟩
      = ⟨(12, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e12 : ∀ p' T', step (loopProgMachine body) ⟨(12, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProgMachine, moveHead, h]
  rw [e9, e10, e11, e12]

/-- Splice find: skip an already splice-marked pair. -/
theorem lp_skipJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProgMachine body) 2 ⟨(15, idx, s), p, T⟩ = ⟨(15, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- Splice find: mark the variable's next data pair. -/
theorem lp_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(15, idx, s), p, T⟩
      = ⟨(17, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- Splice find: the value boundary — all data pairs marked. -/
theorem lp_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(15, idx, s), p, T⟩ = ⟨(25, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_scanJ1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProgMachine body) 2 ⟨(17, idx, s), p, T⟩
      = ⟨(17, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_crossJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProgMachine, moveHead, h2']

theorem lp_scanJ2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProgMachine body) 2 ⟨(19, idx, s), p, T⟩
      = ⟨(19, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_detectJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(21, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProgMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

/-- The splice snoc: a doubled `true`, then back to the find. -/
theorem lp_four_true :
    run (loopProgMachine body) 4 ⟨(21, idx, s), p, T⟩
      = ⟨(13, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e21 : step (loopProgMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  have e22 : ∀ p' T', step (loopProgMachine body) ⟨(22, idx, s), p', T'⟩
      = ⟨(23, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e23 : ∀ p' T', step (loopProgMachine body) ⟨(23, idx, s), p', T'⟩
      = ⟨(24, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e24 : ∀ p' T', step (loopProgMachine body) ⟨(24, idx, s), p', T'⟩
      = ⟨(13, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  rw [e21, e22, e23, e24]

theorem lp_scanD (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProgMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(25, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

theorem lp_detectD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(27, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProgMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

/-- The closing snoc: a doubled `false`, then to the heal. -/
theorem lp_four_false :
    run (loopProgMachine body) 4 ⟨(27, idx, s), p, T⟩
      = ⟨(31, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e27 : step (loopProgMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  have e28 : ∀ p' T', step (loopProgMachine body) ⟨(28, idx, s), p', T'⟩
      = ⟨(29, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e29 : ∀ p' T', step (loopProgMachine body) ⟨(29, idx, s), p', T'⟩
      = ⟨(30, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e30 : ∀ p' T', step (loopProgMachine body) ⟨(30, idx, s), p', T'⟩
      = ⟨(31, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  rw [e27, e28, e29, e30]

/-- The variable heal: restore a splice-marked pair. -/
theorem lp_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProgMachine body) 2 ⟨(33, idx, s), p, T⟩
      = ⟨(33, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- The heal completes at the value boundary: advance the pointer, back to the dispatch. -/
theorem lp_doneHeal (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(33, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2, h]

/-- The increment walk: skip a data pair of the variable. -/
theorem lp_walkI (h1 : T.getD p false = true) :
    run (loopProgMachine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(37, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProgMachine, moveHead, h1']
  rw [e0]
  simp only [step, loopProgMachine, moveHead]; rfl

/-- The increment's four marker-advancing writes, then reset into the next loop round. -/
theorem lp_four_incr (h1 : T.getD p false = false) :
    run (loopProgMachine body) 4 ⟨(37, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e37 : step (loopProgMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(39, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProgMachine, moveHead, h1']
  have e39 : ∀ p' T', step (loopProgMachine body) ⟨(39, idx, s), p', T'⟩
      = ⟨(40, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e40 : ∀ p' T', step (loopProgMachine body) ⟨(40, idx, s), p', T'⟩
      = ⟨(41, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  have e41 : ∀ p' T', step (loopProgMachine body) ⟨(41, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProgMachine, moveHead]; rfl
  rw [e37, e39, e40, e41]

/-- The finale: heal a marked bound pair. -/
theorem lp_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProgMachine body) 2 ⟨(42, idx, s), p, T⟩
      = ⟨(42, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(42, idx, s), p, T⟩
      = ⟨(43, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

/-- The finale completes: halt. -/
theorem lp_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProgMachine body) 2 ⟨(42, idx, s), p, T⟩ = ⟨(44, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProgMachine body) ⟨(42, idx, s), p, T⟩
      = ⟨(43, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProgMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProgMachine, moveHead, h2]

end Steps

/-! ### Scan run-invariants -/

theorem lp_skipBs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProgMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipB hk.1 hk.2]
    rfl

/-- The lo-`true` region-skip invariants (one per entering phase). -/
theorem lp_skipR1as (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProgMachine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipR1a (h k (by omega))]
    rfl

theorem lp_skipR1js (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProgMachine body) (2 * k) ⟨(13, idx, s), q, T⟩
      = ⟨(13, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipR1j (h k (by omega))]
    rfl

theorem lp_skipR1hs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProgMachine body) (2 * k) ⟨(31, idx, s), q, T⟩
      = ⟨(31, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipR1h (h k (by omega))]
    rfl

theorem lp_skipR1is (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProgMachine body) (2 * k) ⟨(35, idx, s), q, T⟩
      = ⟨(35, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipR1i (h k (by omega))]
    rfl

/-- The equal-pair scan invariants. -/
theorem lp_scanA1s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProgMachine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_scanA1 (h k (by omega))]
    rfl

theorem lp_scanA2s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProgMachine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_scanA2 (h k (by omega))]
    rfl

theorem lp_skipJs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProgMachine body) (2 * k) ⟨(15, idx, s), q, T⟩
      = ⟨(15, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_skipJ hk.1 hk.2]
    rfl

theorem lp_scanJ1s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProgMachine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_scanJ1 (h k (by omega))]
    rfl

theorem lp_scanJ2s (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProgMachine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_scanJ2 (h k (by omega))]
    rfl

theorem lp_scanDs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProgMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_scanD (h k (by omega))]
    rfl

/-- The increment's data walk. -/
theorem lp_walkIs (body : List (Option Bool)) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProgMachine body) (2 * k) ⟨(37, idx, s), q, T⟩
      = ⟨(37, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), lp_walkI (h k (by omega))]
    rfl

/-- The variable-heal invariant (evolving, past the bound prefix). -/
theorem lp_healJs (body : List (Option Bool)) (A : List Bool) (N k : ℕ) (E : List Bool)
    (ha : A.length = 2 * N + 2) (hk : k ≤ N) (idx : Fin (body.length + 1)) (s : Bool)
    (i : ℕ) (hi : i ≤ k) :
    run (loopProgMachine body) (2 * i) ⟨(33, idx, s), 2 * N + 2, A ++ (jhT N k 0 ++ E)⟩
      = ⟨(33, idx, if i = 0 then s else true), 2 * N + 2 + 2 * i, A ++ (jhT N k i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (A ++ (jhT N k i ++ E)).getD (2 * N + 2 + 2 * i) false = true := by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
      exact liftJ A _ ha (jhE_pair_lo N k i E (by omega))
    have h2 : (A ++ (jhT N k i ++ E)).getD (2 * N + 2 + 2 * i + 1) false = false := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ A _ ha (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (A ++ (jhT N k i ++ E)) (2 * N + 2 + 2 * i + 1) true
        = A ++ (jhT N k (i + 1) ++ E) := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
        writeAt_append_right A _ (2 * N + 2) (2 * i + 1) true ha
          (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      lp_healJ h1 h2, hw]
    rfl

/-- The bound-heal invariant (the finale). -/
theorem lp_healBs (body : List (Option Bool)) (v : ℕ) (E : List Bool)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (loopProgMachine body) (2 * i) ⟨(42, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(42, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      lp_healB (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The instruction lemmas -/

/-- **An append instruction** inside round `k`: dispatch, skip the bound, cross the variable region and
the padding+output by the two-event scan, snoc the doubled bit, advance the pointer. -/
theorem lp_instr_append (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val none = some b)
    (N k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProgMachine body) (4 * N + 2 * OUT.length + 11)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (jT N k ++ encodeD OUT)⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (jT N k ++ encodeD (OUT ++ [b]))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hq2 : (cntT N (k + 1)).length + (jT N k).length = 4 * N + 4 := by
    rw [hR1, jT_length N k (by omega)]; omega
  have a0 := lp_dispatch_some (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) h hp
  have a1 := lp_skipR1as body (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at a1
  have a2 := lp_crossR1a (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (jT N k ++ encodeD OUT))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have a3 := lp_scanA1s body (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) (2 * N + 2) k
    idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)).getD (2 * N + 2 + 2 * i) false
          = true := by
        rw [← jsT_zero N k]
        exact liftJ _ _ hR1 (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)).getD
          (2 * N + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
          ← jsT_zero N k]
        exact liftJ _ _ hR1 (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have a4 := lp_crossA1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) (2 * N + 2) false k)
    (p := 2 * N + 2 + 2 * k) (T := cntT N (k + 1) ++ (jT N k ++ encodeD OUT))
    (by rw [show 2 * N + 2 + 2 * k = 2 * N + 2 + (2 * k) from rfl, ← jsT_zero N k]
        exact liftJ _ _ hR1 (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega,
          ← jsT_zero N k]
        exact liftJ _ _ hR1 (jsE_m_hi N k 0 _ (by omega)))
  have a5 := lp_scanA2s body (cntT N (k + 1) ++ (jT N k ++ encodeD OUT))
    (2 * N + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 2 * N + 2 + (2 * k + 2 + 2 * i)
              from by omega, ← jsT_zero N k]
          exact liftJ _ _ hR1
            (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i + 1 = 2 * N + 2 + (2 * k + 2 + 2 * i + 1)
              from by omega, ← jsT_zero N k]
          exact liftJ _ _ hR1 (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega) (by omega)
            (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 4 * N + 4 + 2 * (i - (N - k))
            from by omega,
          show 4 * N + 4 + 2 * (i - (N - k)) + 1 = 4 * N + 4 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD2_data_eq (cntT N (k + 1)) (jT N k) OUT (4 * N + 4) (i - (N - k)) hq2
          (by omega))
  rw [show 2 * N + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 4 * N + 4 + 2 * OUT.length from by omega] at a5
  have a6 := lp_detectA (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) (2 * N + 2 + 2 * k + 2) false
      ((N - k) + OUT.length))
    (p := 4 * N + 4 + 2 * OUT.length)
    (preD2_mark_lo (cntT N (k + 1)) (jT N k) OUT (4 * N + 4) hq2)
    (preD2_mark_hi (cntT N (k + 1)) (jT N k) OUT (4 * N + 4) hq2)
  have a7 := lp_four_append (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) (by omega)
  rw [hp] at a7
  simp only [Option.getD_some] at a7
  rw [writes_snoc2 (cntT N (k + 1)) (jT N k) OUT (4 * N + 4) hq2 b] at a7
  rw [show 4 * N + 2 * OUT.length + 11
      = 1 + (2 * N + (2 + (2 * k + (2 + (2 * ((N - k) + OUT.length) + (2 + 4))))))
      from by omega,
    run_add, a0, run_add, a1, run_add, a2, run_add, a3, run_add, a4, run_add, a5,
    run_add, a6, a7]

/-! ### The splice instruction -/

/-- The splice sub-round clock. -/
def lpSpJRounds (N L : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => lpSpJRounds N L j + (4 * N + 2 * L + 2 * j + 10)

/-- One splice sub-round: skip the bound, splice-mark the variable's pair `j'`, seek out, emit a doubled
`true`. -/
theorem lp_spj_round (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k j' : ℕ) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProgMachine body) (4 * N + 2 * OUT.length + 2 * j' + 10)
      ⟨(13, idx, s), 0, cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))⟩
      = ⟨(13, idx, false), 0, cntT N (k + 1)
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate (j' + 1) true))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hq2 : (cntT N (k + 1)).length + (jsT N k (j' + 1)).length = 4 * N + 4 := by
    rw [hR1, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have j1 := lp_skipR1js body
    (cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at j1
  have j2 := lp_crossR1j (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have j3 := lp_skipJs body
    (cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2) j' idx false
    (fun i hi => ⟨liftJ _ _ hR1 (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hR1 (jsE_mark_hi N k j' _ i hi)⟩)
  have j4 := lp_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * N + 2 + 2 * j')
    (T := cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
    (liftJ _ _ hR1 (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * j' + 1) from by omega]
        exact liftJ _ _ hR1 (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1) ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))
      (2 * N + 2 + 2 * j' + 1) false
      = cntT N (k + 1) ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)) := by
    rw [show 2 * N + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * j' + 1) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (2 * j' + 1) false hR1
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at j4
  have j5 := lp_scanJ1s body
    (cntT N (k + 1) ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (jsT N k (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * j' + 2 + 2 * i = 2 * N + 2 + (2 * (j' + 1) + 2 * i)
            from by omega]
        exact liftJ _ _ hR1 (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i) (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (jsT N k (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true))).getD
          (2 * N + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * j' + 2 + 2 * i + 1 = 2 * N + 2 + (2 * (j' + 1) + 2 * i + 1)
            from by omega]
        exact liftJ _ _ hR1 (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1) (by omega)
          (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * j' + 2 + 2 * (k - j' - 1) = 2 * N + 2 + 2 * k from by omega] at j5
  have j6 := lp_crossJ1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))) (2 * N + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (by rw [show 2 * N + 2 + 2 * k = 2 * N + 2 + (2 * k) from rfl]
        exact liftJ _ _ hR1 (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hR1 (jsE_m_hi N k (j' + 1) _ (by omega)))
  have j7 := lp_scanJ2s body
    (cntT N (k + 1) ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
    (2 * N + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate j' true))).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 2 * N + 2 + (2 * k + 2 + 2 * i)
              from by omega]
          exact liftJ _ _ hR1 (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate j' true))).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i + 1 = 2 * N + 2 + (2 * k + 2 + 2 * i + 1)
              from by omega]
          exact liftJ _ _ hR1 (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 4 * N + 4 + 2 * (i - (N - k))
            from by omega,
          show 4 * N + 4 + 2 * (i - (N - k)) + 1 = 4 * N + 4 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD2_data_eq (cntT N (k + 1)) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (4 * N + 4) (i - (N - k)) hq2
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 4 * N + 4 + 2 * (OUT.length + j') from by omega] at j7
  have hm1 := preD2_mark_lo (cntT N (k + 1)) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4) hq2
  have hm2 := preD2_mark_hi (cntT N (k + 1)) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4) hq2
  rw [hlen] at hm1 hm2
  have j8 := lp_detectJ (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))) (2 * N + 2 + 2 * k + 2) false
      ((N - k) + (OUT.length + j')))
    (p := 4 * N + 4 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc2 (cntT N (k + 1)) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 4) hq2 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have j9 := lp_four_true (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 + 2 * (OUT.length + j'))
    (T := cntT N (k + 1) ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))
  rw [hsn] at j9
  rw [show 4 * N + 2 * OUT.length + 2 * j' + 10
      = 2 * N + (2 + (2 * j' + (2 + (2 * (k - j' - 1)
          + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4))))))) from by omega,
    run_add, j1, run_add, j2, run_add, j3, run_add, j4, run_add, j5, run_add, j6,
    run_add, j7, run_add, j8, j9]

/-- The splice sub-rounds invariant. -/
theorem lp_spj_rounds (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (N k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k) (s : Bool) :
    run (loopProgMachine body) (lpSpJRounds N OUT.length j)
      ⟨(13, idx, s), 0, cntT N (k + 1) ++ (jsT N k 0 ++ encodeD OUT)⟩
      = ⟨(13, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (jsT N k j ++ encodeD (OUT ++ List.replicate j true))⟩ := by
  induction j with
  | zero => simp only [lpSpJRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lpSpJRounds N OUT.length (j + 1)
        = lpSpJRounds N OUT.length j + (4 * N + 2 * OUT.length + 2 * j + 10) from rfl,
      run_add, ih (by omega), lp_spj_round body idx N k j (by omega) hk OUT _,
      if_neg (by omega)]

/-- The splice instruction's full clock. -/
def lpSpJCost (N k L : ℕ) : ℕ :=
  1 + (lpSpJRounds N L k + ((4 * N + 2 * L + 2 * k + 10) + (2 * N + 2 * k + 4)))

/-- **A splice instruction** inside round `k`: emit `encodeNat k` from the live variable by the marking
discipline, heal the variable, advance the pointer. -/
theorem lp_instr_spliceJ (body : List (Option Bool)) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val none = none)
    (N k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProgMachine body) (lpSpJCost N k OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (jT N k ++ encodeD OUT)⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (jT N k ++ encodeD (OUT ++ encodeNat k))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hq2 : (cntT N (k + 1)).length + (jsT N k k).length = 4 * N + 4 := by
    rw [hR1, jsT_length N k k (le_refl k) (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate k true).length = OUT.length + k := by
    rw [List.length_append, List.length_replicate]
  have d0 := lp_dispatch_none (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD OUT)) h hp
  have d1 := lp_spj_rounds body idx N k hk OUT k (le_refl k) s
  have d2 := lp_skipR1js body
    (cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))) 0 N idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d2
  have d3 := lp_crossR1j (body := body) (idx := idx)
    (s := if N = 0 then (if k = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d4 := lp_skipJs body
    (cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))
    (2 * N + 2) k idx false
    (fun i hi => ⟨liftJ _ _ hR1 (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hR1 (jsE_mark_hi N k k _ i hi)⟩)
  have d5 := lp_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))
    (by rw [show 2 * N + 2 + 2 * k = 2 * N + 2 + (2 * k) from rfl]
        exact liftJ _ _ hR1 (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hR1 (jsE_m_hi N k k _ (le_refl k)))
  have d6 := lp_scanDs body
    (cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))
    (2 * N + 2 + 2 * k + 2) ((N - k) + (OUT.length + k)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (jsT N k k
            ++ encodeD (OUT ++ List.replicate k true))).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 2 * N + 2 + (2 * k + 2 + 2 * i)
              from by omega]
          exact liftJ _ _ hR1 (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k) (by omega)
            (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (jsT N k k
            ++ encodeD (OUT ++ List.replicate k true))).getD
            (2 * N + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * k + 2 + 2 * i + 1 = 2 * N + 2 + (2 * k + 2 + 2 * i + 1)
              from by omega]
          exact liftJ _ _ hR1 (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1) (le_refl k) (by omega)
            (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * k + 2 + 2 * i = 4 * N + 4 + 2 * (i - (N - k))
            from by omega,
          show 4 * N + 4 + 2 * (i - (N - k)) + 1 = 4 * N + 4 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD2_data_eq (cntT N (k + 1)) (jsT N k k)
          (OUT ++ List.replicate k true) (4 * N + 4) (i - (N - k)) hq2
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + k))
      = 4 * N + 4 + 2 * (OUT.length + k) from by omega] at d6
  have hm1 := preD2_mark_lo (cntT N (k + 1)) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4) hq2
  have hm2 := preD2_mark_hi (cntT N (k + 1)) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4) hq2
  rw [hlen2] at hm1 hm2
  have d7 := lp_detectD (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (jsT N k k
      ++ encodeD (OUT ++ List.replicate k true))) (2 * N + 2 + 2 * k + 2) false
      ((N - k) + (OUT.length + k)))
    (p := 4 * N + 4 + 2 * (OUT.length + k)) hm1 hm2
  have hsn := writes_snoc2 (cntT N (k + 1)) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 4) hq2 false
  rw [hlen2, List.append_assoc,
    show (List.replicate k true ++ [false] : List Bool) = encodeNat k from rfl] at hsn
  have d8 := lp_four_false (body := body) (idx := idx) (s := false)
    (p := 4 * N + 4 + 2 * (OUT.length + k))
    (T := cntT N (k + 1) ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))
  rw [hsn] at d8
  have d9 := lp_skipR1hs body
    (cntT N (k + 1) ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d9
  have d10 := lp_crossR1h (body := body) (idx := idx)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d11 := lp_healJs body (cntT N (k + 1)) N k (encodeD (OUT ++ encodeNat k)) hR1
    (by omega) idx false k (le_refl k)
  have d12 := lp_doneHeal (body := body) (idx := idx)
    (s := if k = 0 then false else true) (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jhT N k k ++ encodeD (OUT ++ encodeNat k))) (by omega)
    (by rw [show 2 * N + 2 + 2 * k = 2 * N + 2 + (2 * k) from rfl]
        exact liftJ _ _ hR1 (jhE_m_lo N k _))
    (by rw [show 2 * N + 2 + 2 * k + 1 = 2 * N + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hR1 (jhE_m_hi N k _))
  rw [show lpSpJCost N k OUT.length
      = 1 + (lpSpJRounds N OUT.length k + (2 * N + (2 + (2 * k + (2
          + (2 * ((N - k) + (OUT.length + k)) + (2 + (4 + (2 * N + (2 + (2 * k + 2)))))))))))
      from by simp only [lpSpJCost]; omega,
    run_add, d0, ← jsT_zero, run_add, d1, run_add, d2, run_add, d3, run_add, d4,
    run_add, d5, run_add, d6, run_add, d7, run_add, d8, ← jhT_zero, run_add, d9,
    run_add, d10, run_add, d11, d12, jhT_last, jsT_zero]

/-! ## The instruction segment, the round, and the loop -/

/-- One instruction's clock inside round `k`. -/
def lpInstrCost (body : List (Option Bool)) (N k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n none with
  | some _ => 4 * N + 2 * (L + (progOutN body k n).length) + 11
  | none => lpSpJCost N k (L + (progOutN body k n).length)

/-- The cumulative segment clock. -/
def lpSegN (body : List (Option Bool)) (N k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lpSegN body N k L n + lpInstrCost body N k L n

/-- **The segment invariant**: `n` instructions of round `k` executed. -/
theorem lp_run_instrs (body : List (Option Bool)) (N k : ℕ) (hk : k < N)
    (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (loopProgMachine body) (lpSegN body N k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N (k + 1) ++ (jT N k ++ encodeD out')⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k n))⟩ := by
  induction n with
  | zero => simp only [lpSegN]; rw [run_zero]; simp [progOutN]
  | succ n ih =>
    rw [show lpSegN body N k out'.length (n + 1)
        = lpSegN body N k out'.length n + lpInstrCost body N k out'.length n from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n none with
    | none =>
      have hin := lp_instr_spliceJ body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N k hk (out' ++ progOutN body k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN body k n ++ encodeNat k = progOutN body k (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [lpInstrCost, hp]
      rw [hin]
      simp
    | some b =>
      have hin := lp_instr_append body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N k hk (out' ++ progOutN body k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show progOutN body k n ++ [b] = progOutN body k (n + 1) from by
          simp only [progOutN, hp]; rfl] at hin
      simp only [lpInstrCost, hp]
      rw [hin]
      simp

/-- The round clock: mark, segment, increment. -/
def lpRoundCost (body : List (Option Bool)) (N k L : ℕ) : ℕ :=
  (2 * k + 2) + (lpSegN body N k L body.length + (1 + (2 * N + 2 * k + 6)))

/-- **One loop round**: mark the bound's pair `k`, run the body (appends and splices of the live value
`k`), increment the variable in place. -/
theorem lp_round (body : List (Option Bool)) (N k : ℕ) (hk : k < N) (out' : List Bool)
    (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (loopProgMachine body) (lpRoundCost body N k out'.length)
      ⟨(0, ptrIn, s), 0, cntT N k ++ (jT N k ++ encodeD out')⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT N (k + 1) ++ (jT N (k + 1) ++ encodeD (out' ++ progOut body k))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have r1 := lp_skipBs body (cntT N k ++ (jT N k ++ encodeD out')) 0 k ptrIn s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := lp_markB (body := body) (idx := ptrIn) (s := if k = 0 then s else true)
    (p := 2 * k) (T := cntT N k ++ (jT N k ++ encodeD out'))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at r2
  have r3 := lp_run_instrs body N k hk out' body.length (le_refl _) true
  have r4 := lp_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k body.length)))
    (Nat.lt_irrefl _)
  have r5 := lp_skipR1is body
    (cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k body.length))) 0 N
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r5
  have r6 := lp_crossR1i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then (if body.length = 0 then true else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k body.length)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r7 := lp_walkIs body
    (cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k body.length)))
    (2 * N + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← jsT_zero N k]
      exact liftJ _ _ hR1 (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r8 := lp_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true) (p := 2 * N + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (jT N k ++ encodeD (out' ++ progOutN body k body.length)))
    (by rw [show 2 * N + 2 + 2 * k = 2 * N + 2 + (2 * k) from rfl, ← jsT_zero N k]
        exact liftJ _ _ hR1 (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right (cntT N (k + 1))
      (jT N k ++ encodeD (out' ++ progOutN body k body.length)) (2 * N + 2) (2 * k)
      true true false true hR1
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r8
  rw [show lpRoundCost body N k out'.length
      = 2 * k + (2 + (lpSegN body N k out'.length body.length + (1 + (2 * N + (2
          + (2 * k + 4)))))) from by simp only [lpRoundCost]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, r8, progOutN_full]

/-- The loop clock. -/
def lpClockN (body : List (Option Bool)) (N Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lpClockN body N Lout k
      + lpRoundCost body N k (Lout + (loopOutN body k).length)

/-- **The rounds invariant.** -/
theorem lp_run_rounds (body : List (Option Bool)) (N : ℕ) (out : List Bool) (k : ℕ)
    (hk : k ≤ N) (s : Bool) :
    run (loopProgMachine body) (lpClockN body N out.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N 0 ++ (jT N 0 ++ encodeD out)⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT N k ++ (jT N k ++ encodeD (out ++ loopOutN body k))⟩ := by
  induction k with
  | zero => simp only [lpClockN]; rw [run_zero]; simp [loopOutN]
  | succ k ih =>
    have hrd := lp_round body N k (by omega) (out ++ loopOutN body k)
      ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loopOutN body k ++ progOut body k = loopOutN body (k + 1) from rfl] at hrd
    rw [show lpClockN body N out.length (k + 1)
        = lpClockN body N out.length k
            + lpRoundCost body N k (out.length + (loopOutN body k).length) from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The full clock. -/
def lpClock (body : List (Option Bool)) (N Lout : ℕ) : ℕ :=
  lpClockN body N Lout N + (2 * N + (2 + (2 * N + 2)))

/-- **THE LOOPED PROGRAM EMITTER RUNS TO COMPLETION.**  From `unaryD N ++ (jT N 0 ++ encodeD out)` the
machine halts by itself at the explicit clock with tape **exactly**
`unaryD N ++ (unaryD N ++ encodeD (out ++ loopOut body N))` — the body's denotation at every round index
appended in order, the bound healed, the variable saturated (`jT N N = unaryD N`). -/
theorem loopProg_run (body : List (Option Bool)) (N : ℕ) (out : List Bool) :
    run (loopProgMachine body) (lpClock body N out.length)
      (init (loopProgMachine body) (unaryD N ++ (jT N 0 ++ encodeD out)))
      = ⟨(44, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 1,
          unaryD N ++ (unaryD N ++ encodeD (out ++ loopOut body N))⟩ := by
  rw [init_lp, ← cntT_zero]
  simp only [lpClock]
  have f1 := lp_skipBs body
    (cntT N N ++ (jT N N ++ encodeD (out ++ loopOutN body N))) 0 N
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := lp_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (jT N N ++ encodeD (out ++ loopOutN body N)))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have f3 := lp_healBs body N (jT N N ++ encodeD (out ++ loopOutN body N))
    ⟨0, Nat.succ_pos _⟩ false N (le_refl N)
  have f4 := lp_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := hlT N N ++ (jT N N ++ encodeD (out ++ loopOutN body N)))
    (hlE_cm_lo N _) (hlE_cm_hi N _)
  rw [run_add, lp_run_rounds body N out N (le_refl N) false, ite_self,
    show 2 * N + (2 + (2 * N + 2)) = 2 * N + (2 + (2 * N + 2)) from rfl,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last, jT_full,
    show loopOut body N = loopOutN body N from rfl, cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem loopProg_halted (body : List (Option Bool)) (N : ℕ) (out : List Bool) :
    (loopProgMachine body).halt
      (run (loopProgMachine body) (lpClock body N out.length)
        (init (loopProgMachine body) (unaryD N ++ (jT N 0 ++ encodeD out)))).st = true := by
  rw [loopProg_run]; rfl

/-- **The looped emitter's output.** -/
theorem loopProg_output (body : List (Option Bool)) (N : ℕ) (out : List Bool) :
    (run (loopProgMachine body) (lpClock body N out.length)
      (init (loopProgMachine body) (unaryD N ++ (jT N 0 ++ encodeD out)))).tp
      = unaryD N ++ (unaryD N ++ encodeD (out ++ loopOut body N)) := by
  rw [loopProg_run]

/-! ## Polynomial clock bounds -/

theorem lpSpJRounds_le (N L LM j : ℕ) (hL : L ≤ LM) (hj : j ≤ N) :
    lpSpJRounds N L j ≤ j * (6 * N + 2 * LM + 10) := by
  induction j with
  | zero => simp [lpSpJRounds]
  | succ j ih =>
    calc lpSpJRounds N L (j + 1)
        = lpSpJRounds N L j + (4 * N + 2 * L + 2 * j + 10) := rfl
      _ ≤ j * (6 * N + 2 * LM + 10) + (6 * N + 2 * LM + 10) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (j + 1) * (6 * N + 2 * LM + 10) := by ring

theorem lpSpJCost_le (N k L LM : ℕ) (hL : L ≤ LM) (hk : k ≤ N) :
    lpSpJCost N k L ≤ N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15) := by
  have h1 := lpSpJRounds_le N L LM k hL hk
  have h2 : k * (6 * N + 2 * LM + 10) ≤ N * (6 * N + 2 * LM + 10) :=
    Nat.mul_le_mul_right _ hk
  simp only [lpSpJCost]
  omega

theorem lpInstrCost_le (body : List (Option Bool)) (N k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (N + 1) ≤ LM) :
    lpInstrCost body N k L n
      ≤ N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15) + (4 * N + 2 * LM + 11) := by
  have hlen : (progOutN body k n).length ≤ body.length * (N + 1) :=
    le_trans (progOutN_length_le body k n)
      (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n none with
  | none =>
    simp only [lpInstrCost, hp]
    exact le_trans (lpSpJCost_le N k (L + (progOutN body k n).length) LM (by omega)
      (by omega)) (Nat.le_add_right _ _)
  | some b =>
    simp only [lpInstrCost, hp]
    omega

theorem lpSegN_le (body : List (Option Bool)) (N k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (N + 1) ≤ LM) :
    lpSegN body N k L n
      ≤ n * (N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15) + (4 * N + 2 * LM + 11)) := by
  induction n with
  | zero => simp [lpSegN]
  | succ n ih =>
    calc lpSegN body N k L (n + 1)
        = lpSegN body N k L n + lpInstrCost body N k L n := rfl
      _ ≤ n * (N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15) + (4 * N + 2 * LM + 11))
          + (N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15) + (4 * N + 2 * LM + 11)) :=
          Nat.add_le_add (ih (by omega)) (lpInstrCost_le body N k L n LM hk (by omega) hL)
      _ = (n + 1) * (N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15)
            + (4 * N + 2 * LM + 11)) := by ring

theorem loopOutN_length_le (body : List (Option Bool)) (N k : ℕ) (hk : k ≤ N) :
    (loopOutN body k).length ≤ k * (body.length * (N + 1)) := by
  induction k with
  | zero => simp [loopOutN]
  | succ k ih =>
    rw [show loopOutN body (k + 1) = loopOutN body k ++ progOut body k from rfl,
      List.length_append]
    have hone : (progOut body k).length ≤ body.length * (N + 1) := by
      rw [← progOutN_full]
      exact le_trans (progOutN_length_le body k body.length)
        (Nat.mul_le_mul_left _ (by omega))
    calc (loopOutN body k).length + (progOut body k).length
        ≤ k * (body.length * (N + 1)) + body.length * (N + 1) :=
          Nat.add_le_add (ih (by omega)) hone
      _ = (k + 1) * (body.length * (N + 1)) := by ring

theorem lpRoundCost_le (body : List (Option Bool)) (N k L LM : ℕ) (hk : k < N)
    (hL : L + body.length * (N + 1) ≤ LM) :
    lpRoundCost body N k L
      ≤ body.length * (N * (6 * N + 2 * LM + 10) + (10 * N + 2 * LM + 15)
          + (4 * N + 2 * LM + 11)) + (6 * N + 7) := by
  have h := lpSegN_le body N k L body.length LM hk (le_refl _) hL
  simp only [lpRoundCost]
  omega

/-- **The loop clock is polynomial**: `N` rounds times the segment cap, plus the finale. -/
theorem lpClock_le (body : List (Option Bool)) (N Lout : ℕ) :
    lpClock body N Lout
      ≤ N * (body.length * (N * (6 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 10)
            + (10 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 15)
            + (4 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 11)) + (6 * N + 7))
        + (4 * N + 4) := by
  have hrounds : ∀ k, k ≤ N → lpClockN body N Lout k
      ≤ k * (body.length * (N * (6 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 10)
            + (10 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 15)
            + (4 * N + 2 * (Lout + N * (body.length * (N + 1))
              + body.length * (N + 1)) + 11)) + (6 * N + 7)) := by
    intro k hk
    induction k with
    | zero => simp [lpClockN]
    | succ k ih =>
      have hLk : (Lout + (loopOutN body k).length) + body.length * (N + 1)
          ≤ Lout + N * (body.length * (N + 1)) + body.length * (N + 1) := by
        have h1 : (loopOutN body k).length ≤ k * (body.length * (N + 1)) :=
          loopOutN_length_le body N k (by omega)
        have h2 : k * (body.length * (N + 1)) ≤ N * (body.length * (N + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      calc lpClockN body N Lout (k + 1)
          = lpClockN body N Lout k
              + lpRoundCost body N k (Lout + (loopOutN body k).length) := rfl
        _ ≤ k * (body.length * (N * (6 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 10)
                + (10 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 15)
                + (4 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 11)) + (6 * N + 7))
            + (body.length * (N * (6 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 10)
                + (10 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 15)
                + (4 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 11)) + (6 * N + 7)) :=
            Nat.add_le_add (ih (by omega))
              (lpRoundCost_le body N k (Lout + (loopOutN body k).length) _ (by omega) hLk)
        _ = (k + 1) * (body.length * (N * (6 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 10)
                + (10 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 15)
                + (4 * N + 2 * (Lout + N * (body.length * (N + 1))
                  + body.length * (N + 1)) + 11)) + (6 * N + 7)) := by ring
  have h := hrounds N (le_refl N)
  simp only [lpClock]
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg