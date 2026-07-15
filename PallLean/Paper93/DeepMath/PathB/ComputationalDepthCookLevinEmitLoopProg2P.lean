import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitProgP

/-!
# Cook–Levin M2 emitter — the prefixed two-source loop engine

`loopProg2PMachine body` is `loopProg2Machine body` re-derived for the layout
`cntT G g ++ (cntT N k ++ (unaryD a ++ (jT N k ++ encodeD out)))` — the passive marked-counter
prefix in front, the `rep_run` hypothesis shape.  Every reset-entry track (the loop find, the three
instruction tracks with their snoc cycles and heal walks, the increment, the finale) gains one
leading skip of the prefix; every position shifts by `2G+2`; every fact climbs one lift level
(`liftJ → liftJ2 → liftJ3`, `preD3 → preD4`, `writes_snoc3 → writes_snoc4`,
`W4_append_right2 → W4_append_right3`).  The instruction set, denotation, and **all family body
factorizations** (`cellCopyBody`, `writeBody`, the dynamics windows, the one-hot bodies) are reused
unchanged from the unprefixed development — `loopProg2P_run` emits the same `loop2Out body a N`, the
prefix preserved verbatim, and `cellCopyP_family_run` demonstrates a real family under the prefix.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2P

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

/-! ## The machine

Control: `Fin 95 × Fin (|body|+1) × Bool`.  Phase groups: `0/1` skip the prefix, `2/3` the loop find,
`4` the three-way dispatch, `5–18` the append track, `19–48` the splice-J track, `49–78` the splice-A
track, `79–89` the increment, `90–93` the finale (prefix skip + bound heal), `94` = halt. -/

def loopProg2PMachine (body : List LInstr) : Machine where
  State := Fin 95 × Fin (body.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 94)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then ((0, s.2.1, s.2.2), none, 1)
       else (if b then ((2, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then ((3, s.2.1, b), none, 1)
    else if s.1 = 3 then
      (if s.2.2 then
        (if b then ((4, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 3)
         else ((2, s.2.1, s.2.2), none, 1))
       else (if b then ((90, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 4 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val .spliceJ with
         | .bit _ => ((5, s.2.1, s.2.2), none, 2)
         | .spliceA => ((49, s.2.1, s.2.2), none, 2)
         | .spliceJ => ((19, s.2.1, s.2.2), none, 2))
       else ((79, s.2.1, s.2.2), none, 2))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if s.2.2 then ((5, s.2.1, s.2.2), none, 1)
       else (if b then ((7, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 7 then ((8, s.2.1, b), none, 1)
    else if s.1 = 8 then
      (if s.2.2 then ((7, s.2.1, s.2.2), none, 1)
       else (if b then ((9, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 9 then ((10, s.2.1, b), none, 1)
    else if s.1 = 10 then
      (if b = s.2.2 then ((9, s.2.1, s.2.2), none, 1) else ((11, s.2.1, s.2.2), none, 1))
    else if s.1 = 11 then ((12, s.2.1, b), none, 1)
    else if s.1 = 12 then
      (if b = s.2.2 then ((11, s.2.1, s.2.2), none, 1) else ((13, s.2.1, s.2.2), none, 1))
    else if s.1 = 13 then ((14, s.2.1, b), none, 1)
    else if s.1 = 14 then
      (if b = s.2.2 then ((13, s.2.1, s.2.2), none, 1) else ((15, s.2.1, s.2.2), none, 0))
    else if s.1 = 15 then
      ((16, s.2.1, s.2.2), some (body.getD s.2.1.val .spliceJ).bitVal, 1)
    else if s.1 = 16 then
      ((17, s.2.1, s.2.2), some (body.getD s.2.1.val .spliceJ).bitVal, 1)
    else if s.1 = 17 then ((18, s.2.1, s.2.2), some false, 1)
    else if s.1 = 18 then
      (if h : s.2.1.val + 1 < body.length + 1 then
        ((4, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((94, s.2.1, s.2.2), some true, 2))
    else if s.1 = 19 then ((20, s.2.1, b), none, 1)
    else if s.1 = 20 then
      (if s.2.2 then ((19, s.2.1, s.2.2), none, 1)
       else (if b then ((21, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 21 then ((22, s.2.1, b), none, 1)
    else if s.1 = 22 then
      (if s.2.2 then ((21, s.2.1, s.2.2), none, 1)
       else (if b then ((23, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 23 then ((24, s.2.1, b), none, 1)
    else if s.1 = 24 then
      (if s.2.2 then ((23, s.2.1, s.2.2), none, 1)
       else (if b then ((25, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 25 then ((26, s.2.1, b), none, 1)
    else if s.1 = 26 then
      (if s.2.2 then
        (if b then ((27, s.2.1, s.2.2), some false, 1) else ((25, s.2.1, s.2.2), none, 1))
       else (if b then ((35, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 27 then ((28, s.2.1, b), none, 1)
    else if s.1 = 28 then
      (if b = s.2.2 then ((27, s.2.1, s.2.2), none, 1) else ((29, s.2.1, s.2.2), none, 1))
    else if s.1 = 29 then ((30, s.2.1, b), none, 1)
    else if s.1 = 30 then
      (if b = s.2.2 then ((29, s.2.1, s.2.2), none, 1) else ((31, s.2.1, s.2.2), none, 0))
    else if s.1 = 31 then ((32, s.2.1, s.2.2), some true, 1)
    else if s.1 = 32 then ((33, s.2.1, s.2.2), some true, 1)
    else if s.1 = 33 then ((34, s.2.1, s.2.2), some false, 1)
    else if s.1 = 34 then ((19, s.2.1, s.2.2), some true, 3)
    else if s.1 = 35 then ((36, s.2.1, b), none, 1)
    else if s.1 = 36 then
      (if b = s.2.2 then ((35, s.2.1, s.2.2), none, 1) else ((37, s.2.1, s.2.2), none, 0))
    else if s.1 = 37 then ((38, s.2.1, s.2.2), some false, 1)
    else if s.1 = 38 then ((39, s.2.1, s.2.2), some false, 1)
    else if s.1 = 39 then ((40, s.2.1, s.2.2), some false, 1)
    else if s.1 = 40 then ((41, s.2.1, s.2.2), some true, 3)
    else if s.1 = 41 then ((42, s.2.1, b), none, 1)
    else if s.1 = 42 then
      (if s.2.2 then ((41, s.2.1, s.2.2), none, 1)
       else (if b then ((43, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 43 then ((44, s.2.1, b), none, 1)
    else if s.1 = 44 then
      (if s.2.2 then ((43, s.2.1, s.2.2), none, 1)
       else (if b then ((45, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 45 then ((46, s.2.1, b), none, 1)
    else if s.1 = 46 then
      (if s.2.2 then ((45, s.2.1, s.2.2), none, 1)
       else (if b then ((47, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 47 then ((48, s.2.1, b), none, 1)
    else if s.1 = 48 then
      (if s.2.2 then
        (if b then ((94, s.2.1, s.2.2), none, 2) else ((47, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((4, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((94, s.2.1, s.2.2), none, 2))
             else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 49 then ((50, s.2.1, b), none, 1)
    else if s.1 = 50 then
      (if s.2.2 then ((49, s.2.1, s.2.2), none, 1)
       else (if b then ((51, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 51 then ((52, s.2.1, b), none, 1)
    else if s.1 = 52 then
      (if s.2.2 then ((51, s.2.1, s.2.2), none, 1)
       else (if b then ((53, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 53 then ((54, s.2.1, b), none, 1)
    else if s.1 = 54 then
      (if s.2.2 then
        (if b then ((55, s.2.1, s.2.2), some false, 1) else ((53, s.2.1, s.2.2), none, 1))
       else (if b then ((65, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 55 then ((56, s.2.1, b), none, 1)
    else if s.1 = 56 then
      (if b = s.2.2 then ((55, s.2.1, s.2.2), none, 1) else ((57, s.2.1, s.2.2), none, 1))
    else if s.1 = 57 then ((58, s.2.1, b), none, 1)
    else if s.1 = 58 then
      (if b = s.2.2 then ((57, s.2.1, s.2.2), none, 1) else ((59, s.2.1, s.2.2), none, 1))
    else if s.1 = 59 then ((60, s.2.1, b), none, 1)
    else if s.1 = 60 then
      (if b = s.2.2 then ((59, s.2.1, s.2.2), none, 1) else ((61, s.2.1, s.2.2), none, 0))
    else if s.1 = 61 then ((62, s.2.1, s.2.2), some true, 1)
    else if s.1 = 62 then ((63, s.2.1, s.2.2), some true, 1)
    else if s.1 = 63 then ((64, s.2.1, s.2.2), some false, 1)
    else if s.1 = 64 then ((49, s.2.1, s.2.2), some true, 3)
    else if s.1 = 65 then ((66, s.2.1, b), none, 1)
    else if s.1 = 66 then
      (if b = s.2.2 then ((65, s.2.1, s.2.2), none, 1) else ((67, s.2.1, s.2.2), none, 1))
    else if s.1 = 67 then ((68, s.2.1, b), none, 1)
    else if s.1 = 68 then
      (if b = s.2.2 then ((67, s.2.1, s.2.2), none, 1) else ((69, s.2.1, s.2.2), none, 0))
    else if s.1 = 69 then ((70, s.2.1, s.2.2), some false, 1)
    else if s.1 = 70 then ((71, s.2.1, s.2.2), some false, 1)
    else if s.1 = 71 then ((72, s.2.1, s.2.2), some false, 1)
    else if s.1 = 72 then ((73, s.2.1, s.2.2), some true, 3)
    else if s.1 = 73 then ((74, s.2.1, b), none, 1)
    else if s.1 = 74 then
      (if s.2.2 then ((73, s.2.1, s.2.2), none, 1)
       else (if b then ((75, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 75 then ((76, s.2.1, b), none, 1)
    else if s.1 = 76 then
      (if s.2.2 then ((75, s.2.1, s.2.2), none, 1)
       else (if b then ((77, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 77 then ((78, s.2.1, b), none, 1)
    else if s.1 = 78 then
      (if s.2.2 then
        (if b then ((94, s.2.1, s.2.2), none, 2) else ((77, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((4, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((94, s.2.1, s.2.2), none, 2))
             else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 79 then ((80, s.2.1, b), none, 1)
    else if s.1 = 80 then
      (if s.2.2 then ((79, s.2.1, s.2.2), none, 1)
       else (if b then ((81, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 81 then ((82, s.2.1, b), none, 1)
    else if s.1 = 82 then
      (if s.2.2 then ((81, s.2.1, s.2.2), none, 1)
       else (if b then ((83, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 83 then ((84, s.2.1, b), none, 1)
    else if s.1 = 84 then
      (if s.2.2 then ((83, s.2.1, s.2.2), none, 1)
       else (if b then ((85, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 85 then
      (if b then ((86, s.2.1, b), none, 1) else ((87, s.2.1, s.2.2), some true, 1))
    else if s.1 = 86 then ((85, s.2.1, s.2.2), none, 1)
    else if s.1 = 87 then ((88, s.2.1, s.2.2), some true, 1)
    else if s.1 = 88 then ((89, s.2.1, s.2.2), some false, 1)
    else if s.1 = 89 then ((0, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 90 then ((91, s.2.1, b), none, 1)
    else if s.1 = 91 then
      (if s.2.2 then ((90, s.2.1, s.2.2), none, 1)
       else (if b then ((92, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
    else if s.1 = 92 then ((93, s.2.1, b), none, 1)
    else if s.1 = 93 then
      (if s.2.2 then
        (if b then ((94, s.2.1, false), none, 2) else ((92, s.2.1, true), some true, 1))
       else (if b then ((94, s.2.1, false), none, 2) else ((94, s.2.1, false), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lp2p (body : List LInstr) (t : List Bool) :
    init (loopProg2PMachine body) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

section Steps
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem q2_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .bit b) :
    run (loopProg2PMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(5, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2PMachine, moveHead, h, hp']

theorem q2_dispatch_spliceA (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceA) :
    run (loopProg2PMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(49, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceA := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2PMachine, moveHead, h, hp']

theorem q2_dispatch_spliceJ (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceJ) :
    run (loopProg2PMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(19, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceJ := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2PMachine, moveHead, h, hp']

theorem q2_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProg2PMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(79, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProg2PMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps2
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem q2_skipWf (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(2, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWa (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(5, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1a (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(7, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1a (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWj (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(21, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1j (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(21, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR2j (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(23, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR2j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWhj (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWhj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(43, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1hj (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(43, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR2hj (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(45, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR2hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(47, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWA (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(49, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(51, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1A (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(51, idx, s), p, T⟩ = ⟨(51, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(51, idx, s), p, T⟩
      = ⟨(52, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1A (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(51, idx, s), p, T⟩ = ⟨(53, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(51, idx, s), p, T⟩
      = ⟨(52, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWhA (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(73, idx, s), p, T⟩ = ⟨(73, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWhA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(73, idx, s), p, T⟩ = ⟨(75, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1hA (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(75, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1hA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(77, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWi (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWi (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(81, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR1i (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(81, idx, s), p, T⟩ = ⟨(81, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR1i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(81, idx, s), p, T⟩ = ⟨(83, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipR2i (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(83, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossR2i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(85, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipWfin (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(90, idx, s), p, T⟩ = ⟨(90, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_crossWfin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(90, idx, s), p, T⟩ = ⟨(92, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanA1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(13, idx, s), p, T⟩
      = ⟨(13, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanJ1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanJ2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(29, idx, s), p, T⟩
      = ⟨(29, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanJD (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(35, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanS1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(55, idx, s), p, T⟩
      = ⟨(55, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanS2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanS3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(59, idx, s), p, T⟩
      = ⟨(59, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanD1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(65, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_scanD2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2PMachine body) 2 ⟨(67, idx, s), p, T⟩
      = ⟨(67, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_crossSA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_crossSJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_crossSS1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(57, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_crossSS2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(57, idx, s), p, T⟩ = ⟨(59, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_crossSD1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(67, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2']

theorem q2_detectA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(13, idx, s), p, T⟩ = ⟨(15, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q2_detectJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(29, idx, s), p, T⟩ = ⟨(31, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q2_detectJD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(37, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q2_detectS3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(61, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q2_detectD2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q2_skipBm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(2, idx, s), p, T⟩ = ⟨(2, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(2, idx, s), p, T⟩
      = ⟨(4, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(2, idx, s), p, T⟩
      = ⟨(90, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(25, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(27, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(35, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(53, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(53, idx, s), p, T⟩
      = ⟨(55, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(65, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2, h]

theorem q2_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(77, idx, s), p, T⟩
      = ⟨(77, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(77, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2, h]

theorem q2_four_TJ :
    run (loopProg2PMachine body) 4 ⟨(31, idx, s), p, T⟩
      = ⟨(19, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2PMachine body) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(33, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(33, idx, s), p', T'⟩
      = ⟨(34, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2PMachine body) ⟨(34, idx, s), p', T'⟩
      = ⟨(19, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q2_four_FJ :
    run (loopProg2PMachine body) 4 ⟨(37, idx, s), p, T⟩
      = ⟨(41, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2PMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(38, idx, s), p', T'⟩
      = ⟨(39, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(39, idx, s), p', T'⟩
      = ⟨(40, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2PMachine body) ⟨(40, idx, s), p', T'⟩
      = ⟨(41, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q2_four_TA :
    run (loopProg2PMachine body) 4 ⟨(61, idx, s), p, T⟩
      = ⟨(49, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2PMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(62, idx, s), p', T'⟩
      = ⟨(63, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(63, idx, s), p', T'⟩
      = ⟨(64, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2PMachine body) ⟨(64, idx, s), p', T'⟩
      = ⟨(49, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q2_four_FA :
    run (loopProg2PMachine body) 4 ⟨(69, idx, s), p, T⟩
      = ⟨(73, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2PMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(70, idx, s), p', T'⟩
      = ⟨(71, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(71, idx, s), p', T'⟩
      = ⟨(72, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2PMachine body) ⟨(72, idx, s), p', T'⟩
      = ⟨(73, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q2_four_bit (h : idx.val + 1 < body.length + 1) :
    run (loopProg2PMachine body) 4 ⟨(15, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spliceJ).bitVal)
            (p + 1) (body.getD idx.val .spliceJ).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2PMachine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, s), p + 1, writeAt T p (body.getD idx.val .spliceJ).bitVal⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(17, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spliceJ).bitVal⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(17, idx, s), p', T'⟩
      = ⟨(18, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2PMachine body) ⟨(18, idx, s), p', T'⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProg2PMachine, moveHead, h]
  rw [e1, e2, e3, e4]

theorem q2_walkI (h1 : T.getD p false = true) :
    run (loopProg2PMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2PMachine, moveHead, h1']
  rw [e0]
  simp only [step, loopProg2PMachine, moveHead]; rfl

theorem q2_four_incr (h1 : T.getD p false = false) :
    run (loopProg2PMachine body) 4 ⟨(85, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(87, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2PMachine, moveHead, h1']
  have e1 : ∀ p' T', step (loopProg2PMachine body) ⟨(87, idx, s), p', T'⟩
      = ⟨(88, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2PMachine body) ⟨(88, idx, s), p', T'⟩
      = ⟨(89, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2PMachine body) ⟨(89, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem q2_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2PMachine body) 2 ⟨(92, idx, s), p, T⟩
      = ⟨(92, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

theorem q2_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2PMachine body) 2 ⟨(92, idx, s), p, T⟩ = ⟨(94, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2PMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2PMachine, moveHead, h2]

end Steps2

/-! ### Scan run-invariants -/

theorem q2_skipWfs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWf (h k (by omega))]
    rfl

theorem q2_skipWas (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWa (h k (by omega))]
    rfl

theorem q2_skipR1as (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1a (h k (by omega))]
    rfl

theorem q2_skipWjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWj (h k (by omega))]
    rfl

theorem q2_skipR1js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1j (h k (by omega))]
    rfl

theorem q2_skipR2js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR2j (h k (by omega))]
    rfl

theorem q2_skipWhjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWhj (h k (by omega))]
    rfl

theorem q2_skipR1hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1hj (h k (by omega))]
    rfl

theorem q2_skipR2hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR2hj (h k (by omega))]
    rfl

theorem q2_skipWAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(49, idx, s), q, T⟩
      = ⟨(49, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWA (h k (by omega))]
    rfl

theorem q2_skipR1As (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(51, idx, s), q, T⟩
      = ⟨(51, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1A (h k (by omega))]
    rfl

theorem q2_skipWhAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(73, idx, s), q, T⟩
      = ⟨(73, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWhA (h k (by omega))]
    rfl

theorem q2_skipR1hAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(75, idx, s), q, T⟩
      = ⟨(75, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1hA (h k (by omega))]
    rfl

theorem q2_skipWis (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWi (h k (by omega))]
    rfl

theorem q2_skipR1is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(81, idx, s), q, T⟩
      = ⟨(81, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR1i (h k (by omega))]
    rfl

theorem q2_skipR2is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(83, idx, s), q, T⟩
      = ⟨(83, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipR2i (h k (by omega))]
    rfl

theorem q2_skipWfins (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(90, idx, s), q, T⟩
      = ⟨(90, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipWfin (h k (by omega))]
    rfl

theorem q2_scanA1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanA1 (h k (by omega))]
    rfl

theorem q2_scanA2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanA2 (h k (by omega))]
    rfl

theorem q2_scanA3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(13, idx, s), q, T⟩
      = ⟨(13, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanA3 (h k (by omega))]
    rfl

theorem q2_scanJ1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanJ1 (h k (by omega))]
    rfl

theorem q2_scanJ2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(29, idx, s), q, T⟩
      = ⟨(29, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanJ2 (h k (by omega))]
    rfl

theorem q2_scanJDs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(35, idx, s), q, T⟩
      = ⟨(35, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanJD (h k (by omega))]
    rfl

theorem q2_scanS1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanS1 (h k (by omega))]
    rfl

theorem q2_scanS2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(57, idx, s), q, T⟩
      = ⟨(57, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanS2 (h k (by omega))]
    rfl

theorem q2_scanS3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanS3 (h k (by omega))]
    rfl

theorem q2_scanD1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(65, idx, s), q, T⟩
      = ⟨(65, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanD1 (h k (by omega))]
    rfl

theorem q2_scanD2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2PMachine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_scanD2 (h k (by omega))]
    rfl

theorem q2_skipBms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2PMachine body) (2 * k) ⟨(2, idx, s), q, T⟩
      = ⟨(2, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipBm hk.1 hk.2]
    rfl

theorem q2_skipJms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2PMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipJm hk.1 hk.2]
    rfl

theorem q2_skipAms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2PMachine body) (2 * k) ⟨(53, idx, s), q, T⟩
      = ⟨(53, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_skipAm hk.1 hk.2]
    rfl

theorem q2_walkIs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2PMachine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q2_walkI (h k (by omega))]
    rfl

/-- The variable heal (evolving `jhT`, three prefixes: grand bound, engine bound, source). -/
theorem q2_healJs (body : List LInstr) (P Q R : List Bool) (G N a k : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2)
    (hk : k ≤ N) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (loopProg2PMachine body) (2 * i)
      ⟨(47, idx, s), 2 * G + 2 + 2 * N + 2 + 2 * a + 2, P ++ (Q ++ (R ++ (jhT N k 0 ++ E)))⟩
      = ⟨(47, idx, if i = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i,
          P ++ (Q ++ (R ++ (jhT N k i ++ E)))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (R ++ (jhT N k i ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
      exact liftJ3 P Q R _ hP hQ hR (jhE_pair_lo N k i E (by omega))
    have h2 : (P ++ (Q ++ (R ++ (jhT N k i ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 P Q R _ hP hQ hR (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (P ++ (Q ++ (R ++ (jhT N k i ++ E))))
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) true
        = P ++ (Q ++ (R ++ (jhT N k (i + 1) ++ E))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega,
        writeAt_append_right3 P Q R _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * i + 1) true
          hP hQ hR (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      q2_healJ h1 h2, hw]
    rfl

/-- The source heal (evolving `hlT`, two prefixes). -/
theorem q2_healAs (body : List LInstr) (P Q : List Bool) (G N a : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (idx : Fin (body.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ a) :
    run (loopProg2PMachine body) (2 * i)
      ⟨(77, idx, s), 2 * G + 2 + 2 * N + 2, P ++ (Q ++ (hlT a 0 ++ E))⟩
      = ⟨(77, idx, if i = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * i,
          P ++ (Q ++ (hlT a i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (hlT a i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i) false
        = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i) from by omega]
      exact liftJ2 P Q _ hP hQ (hlE_pair_lo a i E (by omega))
    have h2 : (P ++ (Q ++ (hlT a i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 P Q _ hP hQ (hlE_pair_hi a i E (by omega))
    have hw : writeAt (P ++ (Q ++ (hlT a i ++ E)))
        (2 * G + 2 + 2 * N + 2 + 2 * i + 1) true = P ++ (Q ++ (hlT a (i + 1) ++ E)) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 P Q _ (2 * G + 2) (2 * N + 2) (2 * i + 1) true hP hQ
          (by rw [List.length_append, hlT_length a i (by omega)]; omega),
        hlT_heal a i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      q2_healA h1 h2, hw]
    rfl

/-- The engine-bound heal (the finale; evolving `hlT`, one prefix). -/
theorem q2_healBs (body : List LInstr) (P : List Bool) (G N : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ)
    (hi : i ≤ N) :
    run (loopProg2PMachine body) (2 * i) ⟨(92, idx, s), 2 * G + 2, P ++ (hlT N 0 ++ E)⟩
      = ⟨(92, idx, if i = 0 then s else true), 2 * G + 2 + 2 * i, P ++ (hlT N i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (hlT N i ++ E)).getD (2 * G + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ P _ hP (hlE_pair_lo N i E (by omega))
    have h2 : (P ++ (hlT N i ++ E)).getD (2 * G + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ P _ hP (hlE_pair_hi N i E (by omega))
    have hw : writeAt (P ++ (hlT N i ++ E)) (2 * G + 2 + 2 * i + 1) true
        = P ++ (hlT N (i + 1) ++ E) := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
        writeAt_append_right P _ (2 * G + 2) (2 * i + 1) true hP
          (by rw [List.length_append, hlT_length N i (by omega)]; omega),
        hlT_heal N i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      q2_healB h1 h2, hw]
    rfl

/-! ## The instruction lemmas

Round-`k` layout: `cntT G g ++ (cntT N (k+1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))` — the grand
prefix at `[0, 2G+2)`, then the engine's regions, output at `2G+4N+2a+8`. -/

section Instr
variable {G g : ℕ}

/-- **An append instruction**, prefixed. -/
theorem q2_instr_bit (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spliceJ = .bit b)
    (hg : g ≤ G) (N a k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2PMachine body) (2 * G + 4 * N + 2 * a + 2 * OUT.length + 15)
      ⟨(4, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(4, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jT N k ++ encodeD (OUT ++ [b]))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (jT N k).length = 2 * G + 4 * N + 2 * a + 8 := by
    rw [hW, hQ1, hQa, jT_length N k (by omega)]; omega
  have b0 := q2_dispatch_bit (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))) h hp
  have b1 := q2_skipWas body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at b1
  have b2 := q2_crossWa (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have b3 := q2_skipR1as body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))) (2 * G + 2) N
    idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have b4 := q2_crossR1a (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have b5 := q2_scanA1s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
            from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1
          (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
            from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1
          (cntE_data a 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := q2_crossSA1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2) false a)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_hi a 0 _ (by omega)))
  have b7 := q2_scanA2s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) k idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQa
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega,
          ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQa
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b8 := q2_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2) false k)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_hi N k 0 _ (by omega)))
  have b9 := q2_scanA3s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1)
            ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1)
            ++ (unaryD a ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (jT N k) OUT
          (2 * G + 4 * N + 2 * a + 8) (i - (N - k)) hq4 (by omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 2 * G + 4 * N + 2 * a + 8 + 2 * OUT.length from by omega] at b9
  have b10 := q2_detectA3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * OUT.length)
    (preD4_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (jT N k) OUT
      (2 * G + 4 * N + 2 * a + 8) hq4)
    (preD4_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (jT N k) OUT
      (2 * G + 4 * N + 2 * a + 8) hq4)
  have b11 := q2_four_bit (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * OUT.length)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))) (by omega)
  rw [hp] at b11
  simp only [LInstr.bitVal] at b11
  rw [writes_snoc4 (cntT G g) (cntT N (k + 1)) (unaryD a) (jT N k) OUT
    (2 * G + 4 * N + 2 * a + 8) hq4 b] at b11
  rw [show 2 * G + 4 * N + 2 * a + 2 * OUT.length + 15
      = 1 + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * k + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4)))))))))) from by omega,
    run_add, b0, run_add, b1, run_add, b2, run_add, b3, run_add, b4, run_add, b5,
    run_add, b6, run_add, b7, run_add, b8, run_add, b9, run_add, b10, b11]

end Instr

/-! ### The splice-J instruction -/

section InstrJ
variable {G g : ℕ}

theorem q2_spj_round (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a k j' : ℕ) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2PMachine body) (2 * G + 4 * N + 2 * a + 2 * OUT.length + 2 * j' + 14)
      ⟨(19, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))⟩
      = ⟨(19, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (jsT N k (j' + 1)).length = 2 * G + 4 * N + 2 * a + 8 := by
    rw [hW, hQ1, hQa, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have j1 := q2_skipWjs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at j1
  have j2 := q2_crossWj (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have j3 := q2_skipR1js body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have j4 := q2_crossR1j (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have j5 := q2_skipR2js body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hQ1 (cntE_lo a 0 _ i (by omega) hi))
  have j6 := q2_crossR2j (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_hi a 0 _ (by omega)))
  have j7 := q2_skipJms body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_mark_hi N k j' _ i hi)⟩)
  have j8 := q2_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j')
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j'
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * j')) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * j' + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 1) false
      = cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 1
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * j' + 1))) from by omega,
      writeAt_append_right3 _ _ _ _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * j' + 1) false
        hW hQ1 hQa
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at j8
  have j9 := q2_scanJ1s body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * (j' + 1) + 2 * i))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i)
          (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * (j' + 1) + 2 * i + 1)))
            from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k from by omega] at j9
  have j10 := q2_crossSJ1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_hi N k (j' + 1) _ (by omega)))
  have j11 := q2_scanJ2s body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i))) from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i)
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * a + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + j') from by omega] at j11
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * a + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * a + 8) hq4
  rw [hlen] at hm1 hm2
  have j12 := q2_detectJ2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + (OUT.length + j')))
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * a + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have j13 := q2_four_TJ (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + j'))
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
  rw [hsn] at j13
  rw [show 2 * G + 4 * N + 2 * a + 2 * OUT.length + 2 * j' + 14
      = 2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * j' + (2 + (2 * (k - j' - 1)
          + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4))))))))))) from by omega,
    run_add, j1, run_add, j2, run_add, j3, run_add, j4, run_add, j5, run_add, j6,
    run_add, j7, run_add, j8, run_add, j9, run_add, j10, run_add, j11, run_add, j12, j13]

theorem q2_spj_rounds (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k) (s : Bool) :
    run (loopProg2PMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * OUT.length + 14) j)
      ⟨(19, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (jsT N k 0 ++ encodeD OUT)))⟩
      = ⟨(19, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k j ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * OUT.length + 14) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * OUT.length + 14) j
            + (2 * G + 4 * N + 2 * a + 2 * OUT.length + 14 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * a + 2 * OUT.length + 14 + 2 * j
        = 2 * G + 4 * N + 2 * a + 2 * OUT.length + 2 * j + 14 from by omega,
      run_add, ih (by omega), q2_spj_round body idx hg N a k j (by omega) hk OUT _,
      if_neg (by omega)]

end InstrJ

/-! ### The splice-J instruction, completed -/

section InstrJ2
variable {G g : ℕ}

def lp2pjCost (G N a k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * L + 14) k
    + ((2 * G + 4 * N + 2 * a + 2 * L + 2 * k + 14) + (2 * G + 2 * N + 2 * a + 2 * k + 8)))

/-- **A splice-J instruction**, prefixed: emit `encodeNat k`, heal the variable, advance. -/
theorem q2_instr_spliceJ (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spliceJ = .spliceJ)
    (hg : g ≤ G) (N a k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2PMachine body) (lp2pjCost G N a k OUT.length)
      ⟨(4, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(4, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jT N k ++ encodeD (OUT ++ encodeNat k))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (jsT N k k).length = 2 * G + 4 * N + 2 * a + 8 := by
    rw [hW, hQ1, hQa, jsT_length N k k (le_refl k) (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate k true).length = OUT.length + k := by
    rw [List.length_append, List.length_replicate]
  have d0 := q2_dispatch_spliceJ (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))) h hp
  have d1 := q2_spj_rounds body idx hg N a k hk OUT k (le_refl k) s
  have d2 := q2_skipWjs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))) 0 G idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d2
  have d3 := q2_crossWj (body := body) (idx := idx)
    (s := if G = 0 then (if k = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d4 := q2_skipR1js body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have d5 := q2_crossR1j (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have d6 := q2_skipR2js body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hQ1 (cntE_lo a 0 _ i (by omega) hi))
  have d7 := q2_crossR2j (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_hi a 0 _ (by omega)))
  have d8 := q2_skipJms body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_mark_hi N k k _ i hi)⟩)
  have d9 := q2_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_m_hi N k k _ (le_refl k)))
  have d10 := q2_scanJDs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + k)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i))) from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQa (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1)
            (le_refl k) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k k)
          (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * a + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + k))
      = 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + k) from by omega] at d10
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * a + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * a + 8) hq4
  rw [hlen2] at hm1 hm2
  have d11 := q2_detectJD (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + (OUT.length + k)))
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + k)) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * a + 8) hq4 false
  rw [hlen2, List.append_assoc,
    show (List.replicate k true ++ [false] : List Bool) = encodeNat k from rfl] at hsn
  have d12 := q2_four_FJ (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 8 + 2 * (OUT.length + k))
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
  rw [hsn] at d12
  have d13 := q2_skipWhjs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d13
  have d14 := q2_crossWhj (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d15 := q2_skipR1hjs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have d16 := q2_crossR1hj (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have d17 := q2_skipR2hjs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hQ1 (cntE_lo a 0 _ i (by omega) hi))
  have d18 := q2_crossR2hj (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a) (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hQ1 (cntE_cm_hi a 0 _ (by omega)))
  have d19 := q2_healJs body (cntT G g) (cntT N (k + 1)) (unaryD a) G N a k
    (encodeD (OUT ++ encodeNat k)) hW hQ1 hQa (by omega) idx false k (le_refl k)
  have d20 := q2_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k k ++ encodeD (OUT ++ encodeNat k))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jhE_m_lo N k _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQa (jhE_m_hi N k _))
  rw [show lp2pjCost G N a k OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * OUT.length + 14) k
          + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * k + (2
            + (2 * ((N - k) + (OUT.length + k)) + (2 + (4 + (2 * G + (2 + (2 * N + (2
            + (2 * a + (2 + (2 * k + 2)))))))))))))))))))
      from by simp only [lp2pjCost]; omega,
    run_add, d0, ← jsT_zero, run_add, d1, run_add, d2, run_add, d3, run_add, d4,
    run_add, d5, run_add, d6, run_add, d7, run_add, d8, run_add, d9, run_add, d10,
    run_add, d11, run_add, d12, ← jhT_zero, run_add, d13, run_add, d14, run_add, d15,
    run_add, d16, run_add, d17, run_add, d18, run_add, d19, d20, jhT_last, jsT_zero]

end InstrJ2

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2P