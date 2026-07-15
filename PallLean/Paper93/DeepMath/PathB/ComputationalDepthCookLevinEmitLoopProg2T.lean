import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearmP

/-!
# Cook–Levin M2 emitter — the two-source loop engine with a capacity-padded source

`loopProg2TMachine body` re-derives `loopProg2PMachine body` for the layout
`cntT G g ++ (cntT N k ++ (jT C t ++ (jT N k ++ encodeD out)))` — the **`t`-mirror layout**: the
static source region is a capacity-padded variable `jT C t` (fixed length `2C+2`, value `t`)
instead of an exact counter `unaryD t`.  This is the design that makes the live round index a
splice source under the grand loop: every region keeps a fixed address, the per-round body reads
the mirror as a temporarily marked/healed static source (the `jsT`/`jhT` machinery, localized
reuse), and the interstitial applies the already-proved in-place `jT_incr` to produce `jT C (t+1)`
for the next round.

Control is `loopProg2PMachine`'s `Fin 95` phase structure **verbatim** plus three pad-crossing
pairs (`95/96 → 25`, `97/98 → 47`, `99/100 → 85`): the boundary-event scans are content-blind — a
padded region's value marker raises the same `(false, true)` event the exact counter's end marker
did, and the padding pairs `(false, false)` are equal pairs the existing scans absorb — so only the
three low-lo skips that must *cross* the source region (the splice-J entry, the heal-J entry, the
increment entry) gain a pad walk.  The `.spliceA` instruction becomes the **mirror splice**: it
emits `encodeNat t` by find/mark/heal on `jsT C t`/`jhT C t` — the denotation is *literally*
`prog2Out body t k`, so every family body factorization is reused unchanged.  Crossing the source
region always costs `2C+4` regardless of `t`: the clocks stay round-uniform.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2T

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2P (init_lp2p)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4 writeAt_append_right4
  W4_append_right4 preD5_data_eq preD5_mark_lo preD5_mark_hi writes_snoc5)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

/-! ## The machine

Control: `Fin 101 × Fin (|body|+1) × Bool` — `loopProg2PMachine`'s phases `0–94` verbatim, plus the
three pad-crossing pairs `95/96 → 25` (find-J), `97/98 → 47` (heal-J), `99/100 → 85` (the
increment walk); the three region-3 crossings retarget to their pads. -/

def loopProg2TMachine (body : List LInstr) : Machine where
  State := Fin 101 × Fin (body.length + 1) × Bool
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
       else (if b then ((95, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((97, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((99, s.2.1, s.2.2), none, 1) else ((94, s.2.1, s.2.2), none, 2)))
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
    else if s.1 = 95 then ((96, s.2.1, b), none, 1)
    else if s.1 = 96 then
      (if s.2.2 then ((25, s.2.1, false), none, 0)
       else (if b then ((25, s.2.1, false), none, 0)
             else ((95, s.2.1, s.2.2), none, 1)))
    else if s.1 = 97 then ((98, s.2.1, b), none, 1)
    else if s.1 = 98 then
      (if s.2.2 then ((47, s.2.1, false), none, 0)
       else (if b then ((47, s.2.1, false), none, 0)
             else ((97, s.2.1, s.2.2), none, 1)))
    else if s.1 = 99 then ((100, s.2.1, b), none, 1)
    else if s.1 = 100 then
      (if s.2.2 then ((85, s.2.1, false), none, 0)
       else (if b then ((85, s.2.1, false), none, 0)
             else ((99, s.2.1, s.2.2), none, 1)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lt (body : List LInstr) (t : List Bool) :
    init (loopProg2TMachine body) t
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl


/-! ## The step layer — phases 0–94 verbatim from loopProg2P -/

section Steps
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qt_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .bit b) :
    run (loopProg2TMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(5, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2TMachine, moveHead, h, hp']

theorem qt_dispatch_spliceA (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceA) :
    run (loopProg2TMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(49, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceA := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2TMachine, moveHead, h, hp']

theorem qt_dispatch_spliceJ (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceJ) :
    run (loopProg2TMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(19, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceJ := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2TMachine, moveHead, h, hp']

theorem qt_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProg2TMachine body) 1 ⟨(4, idx, s), p, T⟩ = ⟨(79, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProg2TMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps2
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qt_skipWf (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(2, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWa (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(5, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1a (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(7, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1a (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWj (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(21, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1j (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(21, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR2j (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(23, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR2j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(95, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWhj (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWhj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(43, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1hj (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(43, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR2hj (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(45, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR2hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(97, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWA (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(49, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(51, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1A (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(51, idx, s), p, T⟩ = ⟨(51, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(51, idx, s), p, T⟩
      = ⟨(52, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1A (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(51, idx, s), p, T⟩ = ⟨(53, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(51, idx, s), p, T⟩
      = ⟨(52, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWhA (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(73, idx, s), p, T⟩ = ⟨(73, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWhA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(73, idx, s), p, T⟩ = ⟨(75, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(73, idx, s), p, T⟩
      = ⟨(74, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1hA (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(75, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1hA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(77, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWi (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWi (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(81, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR1i (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(81, idx, s), p, T⟩ = ⟨(81, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR1i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(81, idx, s), p, T⟩ = ⟨(83, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipR2i (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(83, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossR2i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(99, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipWfin (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(90, idx, s), p, T⟩ = ⟨(90, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_crossWfin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(90, idx, s), p, T⟩ = ⟨(92, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(90, idx, s), p, T⟩
      = ⟨(91, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanA1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(13, idx, s), p, T⟩
      = ⟨(13, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanJ1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanJ2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(29, idx, s), p, T⟩
      = ⟨(29, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanJD (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(35, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanS1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(55, idx, s), p, T⟩
      = ⟨(55, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanS2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanS3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(59, idx, s), p, T⟩
      = ⟨(59, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanD1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(65, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_scanD2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2TMachine body) 2 ⟨(67, idx, s), p, T⟩
      = ⟨(67, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_crossSA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_crossSJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_crossSS1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(57, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_crossSS2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(57, idx, s), p, T⟩ = ⟨(59, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_crossSD1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(67, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2']

theorem qt_detectA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(13, idx, s), p, T⟩ = ⟨(15, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qt_detectJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(29, idx, s), p, T⟩ = ⟨(31, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qt_detectJD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(37, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qt_detectS3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(61, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qt_detectD2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2TMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qt_skipBm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(2, idx, s), p, T⟩ = ⟨(2, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(2, idx, s), p, T⟩
      = ⟨(4, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(2, idx, s), p, T⟩
      = ⟨(90, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(25, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(27, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(35, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(53, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(53, idx, s), p, T⟩
      = ⟨(55, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(65, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2, h]

theorem qt_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(77, idx, s), p, T⟩
      = ⟨(77, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(77, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2, h]

theorem qt_four_TJ :
    run (loopProg2TMachine body) 4 ⟨(31, idx, s), p, T⟩
      = ⟨(19, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2TMachine body) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(33, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(33, idx, s), p', T'⟩
      = ⟨(34, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2TMachine body) ⟨(34, idx, s), p', T'⟩
      = ⟨(19, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qt_four_FJ :
    run (loopProg2TMachine body) 4 ⟨(37, idx, s), p, T⟩
      = ⟨(41, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2TMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(38, idx, s), p', T'⟩
      = ⟨(39, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(39, idx, s), p', T'⟩
      = ⟨(40, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2TMachine body) ⟨(40, idx, s), p', T'⟩
      = ⟨(41, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qt_four_TA :
    run (loopProg2TMachine body) 4 ⟨(61, idx, s), p, T⟩
      = ⟨(49, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2TMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(62, idx, s), p', T'⟩
      = ⟨(63, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(63, idx, s), p', T'⟩
      = ⟨(64, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2TMachine body) ⟨(64, idx, s), p', T'⟩
      = ⟨(49, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qt_four_FA :
    run (loopProg2TMachine body) 4 ⟨(69, idx, s), p, T⟩
      = ⟨(73, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2TMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(70, idx, s), p', T'⟩
      = ⟨(71, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(71, idx, s), p', T'⟩
      = ⟨(72, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2TMachine body) ⟨(72, idx, s), p', T'⟩
      = ⟨(73, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qt_four_bit (h : idx.val + 1 < body.length + 1) :
    run (loopProg2TMachine body) 4 ⟨(15, idx, s), p, T⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spliceJ).bitVal)
            (p + 1) (body.getD idx.val .spliceJ).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2TMachine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, s), p + 1, writeAt T p (body.getD idx.val .spliceJ).bitVal⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(17, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spliceJ).bitVal⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(17, idx, s), p', T'⟩
      = ⟨(18, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2TMachine body) ⟨(18, idx, s), p', T'⟩
      = ⟨(4, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProg2TMachine, moveHead, h]
  rw [e1, e2, e3, e4]

theorem qt_walkI (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2TMachine, moveHead, h1']
  rw [e0]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_four_incr (h1 : T.getD p false = false) :
    run (loopProg2TMachine body) 4 ⟨(85, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(87, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2TMachine, moveHead, h1']
  have e1 : ∀ p' T', step (loopProg2TMachine body) ⟨(87, idx, s), p', T'⟩
      = ⟨(88, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2TMachine body) ⟨(88, idx, s), p', T'⟩
      = ⟨(89, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2TMachine body) ⟨(89, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem qt_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(92, idx, s), p, T⟩
      = ⟨(92, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(92, idx, s), p, T⟩ = ⟨(94, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(92, idx, s), p, T⟩
      = ⟨(93, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

end Steps2

/-! ### Scan run-invariants -/

theorem qt_skipWfs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWf (h k (by omega))]
    rfl

theorem qt_skipWas (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWa (h k (by omega))]
    rfl

theorem qt_skipR1as (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1a (h k (by omega))]
    rfl

theorem qt_skipWjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWj (h k (by omega))]
    rfl

theorem qt_skipR1js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1j (h k (by omega))]
    rfl

theorem qt_skipR2js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR2j (h k (by omega))]
    rfl

theorem qt_skipWhjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWhj (h k (by omega))]
    rfl

theorem qt_skipR1hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1hj (h k (by omega))]
    rfl

theorem qt_skipR2hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR2hj (h k (by omega))]
    rfl

theorem qt_skipWAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(49, idx, s), q, T⟩
      = ⟨(49, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWA (h k (by omega))]
    rfl

theorem qt_skipR1As (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(51, idx, s), q, T⟩
      = ⟨(51, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1A (h k (by omega))]
    rfl

theorem qt_skipWhAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(73, idx, s), q, T⟩
      = ⟨(73, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWhA (h k (by omega))]
    rfl

theorem qt_skipR1hAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(75, idx, s), q, T⟩
      = ⟨(75, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1hA (h k (by omega))]
    rfl

theorem qt_skipWis (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWi (h k (by omega))]
    rfl

theorem qt_skipR1is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(81, idx, s), q, T⟩
      = ⟨(81, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR1i (h k (by omega))]
    rfl

theorem qt_skipR2is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(83, idx, s), q, T⟩
      = ⟨(83, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipR2i (h k (by omega))]
    rfl

theorem qt_skipWfins (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(90, idx, s), q, T⟩
      = ⟨(90, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipWfin (h k (by omega))]
    rfl

theorem qt_scanA1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanA1 (h k (by omega))]
    rfl

theorem qt_scanA2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanA2 (h k (by omega))]
    rfl

theorem qt_scanA3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(13, idx, s), q, T⟩
      = ⟨(13, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanA3 (h k (by omega))]
    rfl

theorem qt_scanJ1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanJ1 (h k (by omega))]
    rfl

theorem qt_scanJ2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(29, idx, s), q, T⟩
      = ⟨(29, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanJ2 (h k (by omega))]
    rfl

theorem qt_scanJDs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(35, idx, s), q, T⟩
      = ⟨(35, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanJD (h k (by omega))]
    rfl

theorem qt_scanS1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanS1 (h k (by omega))]
    rfl

theorem qt_scanS2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(57, idx, s), q, T⟩
      = ⟨(57, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanS2 (h k (by omega))]
    rfl

theorem qt_scanS3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanS3 (h k (by omega))]
    rfl

theorem qt_scanD1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(65, idx, s), q, T⟩
      = ⟨(65, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanD1 (h k (by omega))]
    rfl

theorem qt_scanD2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2TMachine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_scanD2 (h k (by omega))]
    rfl

theorem qt_skipBms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * k) ⟨(2, idx, s), q, T⟩
      = ⟨(2, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipBm hk.1 hk.2]
    rfl

theorem qt_skipJms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipJm hk.1 hk.2]
    rfl

theorem qt_skipAms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * k) ⟨(53, idx, s), q, T⟩
      = ⟨(53, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_skipAm hk.1 hk.2]
    rfl

theorem qt_walkIs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2TMachine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_walkI (h k (by omega))]
    rfl

/-- The variable heal (evolving `jhT`, three prefixes: grand bound, engine bound, source). -/
theorem qt_healJs (body : List LInstr) (P Q R : List Bool) (G N a k : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (hR : R.length = 2 * a + 2)
    (hk : k ≤ N) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (loopProg2TMachine body) (2 * i)
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
      qt_healJ h1 h2, hw]
    rfl


/-- The engine-bound heal (the finale; evolving `hlT`, one prefix). -/
theorem qt_healBs (body : List LInstr) (P : List Bool) (G N : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ)
    (hi : i ≤ N) :
    run (loopProg2TMachine body) (2 * i) ⟨(92, idx, s), 2 * G + 2, P ++ (hlT N 0 ++ E)⟩
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
      qt_healB h1 h2, hw]
    rfl

/-! ### The pad-crossing pairs -/

section StepsPad
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qt_padJ_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(95, idx, s), p, T⟩ = ⟨(95, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(95, idx, s), p, T⟩
      = ⟨(96, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_padJ_boundT (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(95, idx, s), p, T⟩ = ⟨(25, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(95, idx, s), p, T⟩
      = ⟨(96, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_padJ_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(95, idx, s), p, T⟩ = ⟨(25, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(95, idx, s), p, T⟩
      = ⟨(96, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_padHJ_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(97, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_padHJ_boundT (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(47, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_padHJ_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(47, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_padI_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2TMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(99, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

theorem qt_padI_boundT (h1 : T.getD p false = true) :
    run (loopProg2TMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2TMachine, moveHead]; rfl

theorem qt_padI_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2TMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2TMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2TMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2TMachine, moveHead, h2]

end StepsPad

theorem qt_padJs (body : List LInstr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * m) ⟨(95, idx, s), q, T⟩
      = ⟨(95, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_padJ_pad hm.1 hm.2]
    rfl

theorem qt_padHJs (body : List LInstr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * m) ⟨(97, idx, s), q, T⟩
      = ⟨(97, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_padHJ_pad hm.1 hm.2]
    rfl

theorem qt_padIs (body : List LInstr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2TMachine body) (2 * m) ⟨(99, idx, s), q, T⟩
      = ⟨(99, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qt_padI_pad hm.1 hm.2]
    rfl

/-- The mirror heal (evolving `jhT` in the source region, two prefixes). -/
theorem qt_healTs (body : List LInstr) (P Q : List Bool) (G N C t : ℕ) (E : List Bool)
    (hP : P.length = 2 * G + 2) (hQ : Q.length = 2 * N + 2) (ht : t ≤ C)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ t) :
    run (loopProg2TMachine body) (2 * i)
      ⟨(77, idx, s), 2 * G + 2 + 2 * N + 2, P ++ (Q ++ (jhT C t 0 ++ E))⟩
      = ⟨(77, idx, if i = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * i,
          P ++ (Q ++ (jhT C t i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (jhT C t i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i) false
        = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i) from by omega]
      exact liftJ2 P Q _ hP hQ (jhE_pair_lo C t i E (by omega))
    have h2 : (P ++ (Q ++ (jhT C t i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 P Q _ hP hQ (jhE_pair_hi C t i E (by omega))
    have hw : writeAt (P ++ (Q ++ (jhT C t i ++ E)))
        (2 * G + 2 + 2 * N + 2 + 2 * i + 1) true = P ++ (Q ++ (jhT C t (i + 1) ++ E)) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 P Q _ (2 * G + 2) (2 * N + 2) (2 * i + 1) true hP hQ
          (by rw [List.length_append, jhT_length C t i (by omega) (by omega)]; omega),
        jhT_heal C t i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qt_healA h1 h2, hw]
    rfl

/-! ### Combined pad-boundary dispatchers -/

section StepsPad2
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qt_padJ_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (loopProg2TMachine body) 2 ⟨(95, idx, s), p, T⟩ = ⟨(25, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qt_padJ_boundT h1
  · exact qt_padJ_boundM h1 h2

theorem qt_padHJ_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (loopProg2TMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(47, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qt_padHJ_boundT h1
  · exact qt_padHJ_boundM h1 h2

theorem qt_padI_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (loopProg2TMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qt_padI_boundT h1
  · exact qt_padI_boundM h1 h2

end StepsPad2

/-! ## The instruction lemmas

Round-`k` layout: `cntT G g ++ (cntT N (k+1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))` — the grand
prefix, the engine bound, the capacity-padded mirror (fixed length `2C+2`), the live variable,
output at `2G+4N+2C+8`. -/

section Instr
variable {G g : ℕ}

/-- **An append instruction** on the mirror layout: the boundary-event scans absorb the mirror's
value marker and padding at the same three events. -/
theorem qt_instr_bit (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spliceJ = .bit b)
    (hg : g ≤ G) (N C t k : ℕ) (ht : t ≤ C) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2TMachine body) (2 * G + 4 * N + 2 * C + 2 * OUT.length + 15)
      ⟨(4, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(4, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jT N k ++ encodeD (OUT ++ [b]))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jT C t).length = 2 * C + 2 := jT_length C t ht
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (jT C t).length
      + (jT N k).length = 2 * G + 4 * N + 2 * C + 8 := by
    rw [hW, hQ1, hQc, jT_length N k (by omega)]; omega
  have b0 := qt_dispatch_bit (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) h hp
  have b1 := qt_skipWas body
    (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at b1
  have b2 := qt_crossWa (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have b3 := qt_skipR1as body
    (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) (2 * G + 2) N
    idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have b4 := qt_crossR1a (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have b5 := qt_scanA1s body
    (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2) t idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
            from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1
          (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
            from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1
          (jsE_data C t 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := qt_crossSA1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2) false t)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t 0 _ (by omega)))
  have b7 := qt_scanA2s body
    (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) ((C - t) + k) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (C - t) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega,
            ← jsT_zero C t]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
            ← jsT_zero C t]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · have e1 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i) false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * (i - (C - t)))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i - (C - t))) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1) false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * (i - (C - t)) + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i - (C - t)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * ((C - t) + k)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k from by omega] at b7
  have b8 := qt_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2 + 2 * t + 2) false ((C - t) + k))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N k 0 _ (by omega)))
  have b9 := qt_scanA3s body
    (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1)
            ++ (jT C t ++ (jT N k ++ encodeD OUT)))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (jT C t) (jT N k) OUT
          (2 * G + 4 * N + 2 * C + 8) (i - (N - k)) hq4 (by omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 2 * G + 4 * N + 2 * C + 8 + 2 * OUT.length from by omega] at b9
  have b10 := qt_detectA3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * OUT.length)
    (preD4_mark_lo (cntT G g) (cntT N (k + 1)) (jT C t) (jT N k) OUT
      (2 * G + 4 * N + 2 * C + 8) hq4)
    (preD4_mark_hi (cntT G g) (cntT N (k + 1)) (jT C t) (jT N k) OUT
      (2 * G + 4 * N + 2 * C + 8) hq4)
  have b11 := qt_four_bit (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * OUT.length)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) (by omega)
  rw [hp] at b11
  simp only [LInstr.bitVal] at b11
  rw [writes_snoc4 (cntT G g) (cntT N (k + 1)) (jT C t) (jT N k) OUT
    (2 * G + 4 * N + 2 * C + 8) hq4 b] at b11
  rw [show 2 * G + 4 * N + 2 * C + 2 * OUT.length + 15
      = 1 + (2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * ((C - t) + k) + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4)))))))))) from by omega,
    run_add, b0, run_add, b1, run_add, b2, run_add, b3, run_add, b4, run_add, b5,
    run_add, b6, run_add, b7, run_add, b8, run_add, b9, run_add, b10, b11]

end Instr

/-! ### The splice-J instruction on the mirror layout -/

section InstrJ
variable {G g : ℕ}

/-- One splice-J sub-round: the source crossing pays the fixed `2C+4` (filled walk, marker cross,
pad walk, boundary) regardless of `t`. -/
theorem qt_spj_round (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N C t k j' : ℕ) (ht : t ≤ C) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2TMachine body) (2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * j' + 16)
      ⟨(19, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))⟩
      = ⟨(19, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (jT C t ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jT C t).length = 2 * C + 2 := jT_length C t ht
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (jT C t).length
      + (jsT N k (j' + 1)).length = 2 * G + 4 * N + 2 * C + 8 := by
    rw [hW, hQ1, hQc, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have j1 := qt_skipWjs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at j1
  have j2 := qt_crossWj (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have j3 := qt_skipR1js body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have j4 := qt_crossR1j (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have j5 := qt_skipR2js body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2) t idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have j6 := qt_crossR2j (body := body) (idx := idx) (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t 0 _ (by omega)))
  have j6b := qt_padJs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) (C - t) idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega) (by omega)
        (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * (C - t)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at j6b
  have j6c := qt_padJ_bound (body := body) (idx := idx)
    (s := if C - t = 0 then false else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (Or.inl (by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega]
      rcases Nat.eq_zero_or_pos j' with h0 | h0
      · subst h0
        exact liftJ3 _ _ _ _ hW hQ1 hQc
          (jsE_data N k 0 _ 0 (by omega) (by omega) (by omega))
      · exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_lo N k j' _ 0 h0)))
  have j7 := qt_skipJms body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_hi N k j' _ i hi)⟩)
  have j8 := qt_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j')
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j'
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * j')) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * j' + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 1) false
      = cntT G g ++ (cntT N (k + 1)
          ++ (jT C t ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 1
        = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * j' + 1))) from by omega,
      writeAt_append_right3 _ _ _ _ (2 * G + 2) (2 * N + 2) (2 * C + 2) (2 * j' + 1) false
        hW hQ1 hQc
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at j8
  have j9 := qt_scanJ1s body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * (j' + 1) + 2 * i)))
            from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i)
          (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * (j' + 1) + 2 * i + 1)))
            from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc
          (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1) (by omega) (by omega)
            (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k from by omega] at j9
  have j10 := qt_crossSJ1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N k (j' + 1) _ (by omega)))
  have j11 := qt_scanJ2s body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i)
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * C + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + j') from by omega] at j11
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * C + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * C + 8) hq4
  rw [hlen] at hm1 hm2
  have j12 := qt_detectJ2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) false ((N - k) + (OUT.length + j')))
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (2 * G + 4 * N + 2 * C + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have j13 := qt_four_TJ (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + j'))
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
  rw [hsn] at j13
  rw [show 2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * j' + 16
      = 2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * (C - t) + (2 + (2 * j' + (2
          + (2 * (k - j' - 1) + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4)))))))))))))
      from by omega,
    run_add, j1, run_add, j2, run_add, j3, run_add, j4, run_add, j5, run_add, j6,
    run_add, j6b, run_add, j6c, run_add, j7, run_add, j8, run_add, j9, run_add, j10,
    run_add, j11, run_add, j12, j13]

theorem qt_spj_rounds (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N C t k : ℕ) (ht : t ≤ C) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k)
    (s : Bool) :
    run (loopProg2TMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 16) j)
      ⟨(19, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (jT C t ++ (jsT N k 0 ++ encodeD OUT)))⟩
      = ⟨(19, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (jT C t ++ (jsT N k j ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 16) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 16) j
            + (2 * G + 4 * N + 2 * C + 2 * OUT.length + 16 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * C + 2 * OUT.length + 16 + 2 * j
        = 2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * j + 16 from by omega,
      run_add, ih (by omega), qt_spj_round body idx hg N C t k j ht (by omega) hk OUT _,
      if_neg (by omega)]

end InstrJ

/-! ### The splice-J instruction, completed -/

section InstrJ2
variable {G g : ℕ}

def lptjCost (G N C k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * L + 16) k
    + ((2 * G + 4 * N + 2 * C + 2 * L + 2 * k + 16) + (2 * G + 2 * N + 2 * C + 2 * k + 10)))

/-- **A splice-J instruction** on the mirror layout: emit `encodeNat k`, heal the variable,
advance. -/
theorem qt_instr_spliceJ (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spliceJ = .spliceJ)
    (hg : g ≤ G) (N C t k : ℕ) (ht : t ≤ C) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2TMachine body) (lptjCost G N C k OUT.length)
      ⟨(4, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(4, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jT N k ++ encodeD (OUT ++ encodeNat k))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jT C t).length = 2 * C + 2 := jT_length C t ht
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (jT C t).length
      + (jsT N k k).length = 2 * G + 4 * N + 2 * C + 8 := by
    rw [hW, hQ1, hQc, jsT_length N k k (le_refl k) (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate k true).length = OUT.length + k := by
    rw [List.length_append, List.length_replicate]
  have d0 := qt_dispatch_spliceJ (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) h hp
  have d1 := qt_spj_rounds body idx hg N C t k ht hk OUT k (le_refl k) s
  have d2 := qt_skipWjs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))) 0 G idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d2
  have d3 := qt_crossWj (body := body) (idx := idx)
    (s := if G = 0 then (if k = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d4 := qt_skipR1js body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have d5 := qt_crossR1j (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have d6 := qt_skipR2js body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2) t idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have d7 := qt_crossR2j (body := body) (idx := idx) (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t 0 _ (by omega)))
  have d7b := qt_padJs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) (C - t) idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega) (by omega)
        (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * (C - t)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at d7b
  have d7c := qt_padJ_bound (body := body) (idx := idx)
    (s := if C - t = 0 then false else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          refine Or.inr ⟨?_, ?_⟩
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N 0 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 1
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 1)) from by omega]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N 0 0 _ (by omega))
        · refine Or.inl ?_
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_lo N k k _ 0 h0))
  have d8 := qt_skipJms body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_mark_hi N k k _ i hi)⟩)
  have d9 := qt_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N k k _ (le_refl k)))
  have d10 := qt_scanJDs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) ((N - k) + (OUT.length + k)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1)
            (le_refl k) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k k)
          (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * C + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + k))
      = 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + k) from by omega] at d10
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * C + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * C + 8) hq4
  rw [hlen2] at hm1 hm2
  have d11 := qt_detectJD (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) false ((N - k) + (OUT.length + k)))
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + k)) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (jT C t) (jsT N k k)
    (OUT ++ List.replicate k true) (2 * G + 4 * N + 2 * C + 8) hq4 false
  rw [hlen2, List.append_assoc,
    show (List.replicate k true ++ [false] : List Bool) = encodeNat k from rfl] at hsn
  have d12 := qt_four_FJ (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + k))
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
  rw [hsn] at d12
  have d13 := qt_skipWhjs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at d13
  have d14 := qt_crossWhj (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have d15 := qt_skipR1hjs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have d16 := qt_crossR1hj (body := body) (idx := idx)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have d17 := qt_skipR2hjs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (2 * G + 2 + 2 * N + 2) t idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have d18 := qt_crossR2hj (body := body) (idx := idx)
    (s := if t = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t 0 _ (by omega)))
  have d18b := qt_padHJs body (cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) (C - t) idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega) (by omega)
        (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * (C - t)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at d18b
  have d18c := qt_padHJ_bound (body := body) (idx := idx)
    (s := if C - t = 0 then false else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          refine Or.inr ⟨?_, ?_⟩
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jhE_m_lo N 0 _)
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 1
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 1)) from by omega]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jhE_m_hi N 0 _)
        · refine Or.inl ?_
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jhE_pair_lo N k 0 _ h0))
  have d19 := qt_healJs body (cntT G g) (cntT N (k + 1)) (jT C t) G N C k
    (encodeD (OUT ++ encodeNat k)) hW hQ1 hQc (by omega) idx false k (le_refl k)
  have d20 := qt_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jT C t ++ (jhT N k k ++ encodeD (OUT ++ encodeNat k))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jhE_m_lo N k _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jhE_m_hi N k _))
  rw [show lptjCost G N C k OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 16) k
          + (2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * (C - t) + (2 + (2 * k + (2
            + (2 * ((N - k) + (OUT.length + k)) + (2 + (4 + (2 * G + (2 + (2 * N + (2
            + (2 * t + (2 + (2 * (C - t) + (2 + (2 * k + 2)))))))))))))))))))))))
      from by simp only [lptjCost]; omega,
    run_add, d0, ← jsT_zero N k, run_add, d1, run_add, d2, run_add, d3, run_add, d4,
    run_add, d5, run_add, d6, run_add, d7, run_add, d7b, run_add, d7c, run_add, d8,
    run_add, d9, run_add, d10, run_add, d11, run_add, d12, ← jhT_zero N k, run_add, d13,
    run_add, d14, run_add, d15, run_add, d16, run_add, d17, run_add, d18, run_add, d18b,
    run_add, d18c, run_add, d19, d20, jhT_last, jsT_zero N k]

end InstrJ2

/-! ### The mirror splice: the `.spliceA` instruction reads the padded `t`-source -/

section InstrA
variable {G g : ℕ}

/-- One mirror-splice sub-round: mark the mirror's pair `i` (`jsT` machinery), seek out through the
mirror's padding, the variable, and the output, emit a doubled `true`. -/
theorem qt_spa_round (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N C t k i : ℕ) (ht : t ≤ C) (hi : i < t) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2TMachine body) (2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * i + 14)
      ⟨(49, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))⟩
      = ⟨(49, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (jsT C t (i + 1) ++ (jT N k
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jsT C t (i + 1)).length = 2 * C + 2 := jsT_length C t (i + 1) (by omega) ht
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (jsT C t (i + 1)).length
      + (jT N k).length = 2 * G + 4 * N + 2 * C + 8 := by
    rw [hW, hQ1, hQc, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s1 := qt_skipWAs body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) 0 G idx s
    (fun i' hi' => by simpa using cntE_lo G g _ i' hg hi')
  simp only [Nat.zero_add] at s1
  have s2 := qt_crossWA (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have s3 := qt_skipR1As body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * G + 2) N idx false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * i' = 2 * G + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i' (by omega) hi'))
  have s4 := qt_crossR1A (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have s5 := qt_skipAms body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * G + 2 + 2 * N + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i' = 2 * G + 2 + (2 * N + 2 + 2 * i')
          from by omega]
      exact liftJ2 _ _ _ hW hQ1 (jsE_mark_lo C t i _ i' hi'), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i' + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i' + 1))
          from by omega]
      exact liftJ2 _ _ _ hW hQ1 (jsE_mark_hi C t i _ i' hi')⟩)
  have s6 := qt_markA (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * i)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega]
        exact liftJ2 _ _ _ hW hQ1
          (jsE_data C t i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hQ1
          (jsE_data C t i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
      = cntT G g ++ (cntT N (k + 1)
          ++ (jsT C t (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
        from by omega,
      writeAt_append_right2 _ _ _ (2 * G + 2) (2 * N + 2) (2 * i + 1) false hW hQ1
        (by rw [List.length_append, jsT_length C t i (by omega) ht]; omega),
      jsT_mark C t i _ hi (by omega)]
  rw [hw] at s6
  have s7 := qt_scanS1s body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * i + 2) (t - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * (i + 1) + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_data C t (i + 1) _ (2 * (i + 1) + 2 * i')
          (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * (i + 1) + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_data C t (i + 1) _ (2 * (i + 1) + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * (t - i - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * t from by omega] at s7
  have s8 := qt_crossSS1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * i + 2) true (t - i - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t (i + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t (i + 1) _ (by omega)))
  have s9 := qt_scanS2s body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) ((C - t) + k) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (C - t) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i') false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i'
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i')) from by omega]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t (i + 1) _ (2 * t + 2 + 2 * i') (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i' + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i' + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i' + 1)) from by omega]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t (i + 1) _ (2 * t + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i') false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i'
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * (i' - (C - t)))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i' - (C - t))) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i' + 1) false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i' + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * (i' - (C - t)) + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i' - (C - t)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * ((C - t) + k)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k from by omega] at s9
  have s10 := qt_crossSS2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * t + 2) false ((C - t) + k))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N k 0 _ (by omega)))
  have s11 := qt_scanS3s body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i') false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i'
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i')))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i') (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i' + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i' + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i'
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i' - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * C + 8 + 2 * (i' - (N - k)) + 1
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (jsT C t (i + 1)) (jT N k)
          (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * C + 8) (i' - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + i))
      = 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + i) from by omega] at s11
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (jsT C t (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * C + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (jsT C t (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * C + 8) hq4
  rw [hlen] at hm1 hm2
  have s12 := qt_detectS3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jsT C t (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) false ((N - k) + (OUT.length + i)))
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (jsT C t (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * C + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := qt_four_TA (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + i))
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
  rw [hsn] at s13
  rw [show 2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * i + 14
      = 2 * G + (2 + (2 * N + (2 + (2 * i + (2 + (2 * (t - i - 1) + (2
          + (2 * ((C - t) + k) + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4)))))))))))
      from by omega,
    run_add, s1, run_add, s2, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem qt_spa_rounds (body : List LInstr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N C t k : ℕ) (ht : t ≤ C) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ t)
    (s : Bool) :
    run (loopProg2TMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 14) j)
      ⟨(49, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (jsT C t 0 ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(49, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (jsT C t j ++ (jT N k ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 14) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 14) j
            + (2 * G + 4 * N + 2 * C + 2 * OUT.length + 14 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * C + 2 * OUT.length + 14 + 2 * j
        = 2 * G + 4 * N + 2 * C + 2 * OUT.length + 2 * j + 14 from by omega,
      run_add, ih (by omega), qt_spa_round body idx hg N C t k j ht (by omega) hk OUT _,
      if_neg (by omega)]

end InstrA

/-! ### The mirror splice, completed -/

section InstrA2
variable {G g : ℕ}

def lptaCost (G N C t L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * L + 14) t
    + ((2 * G + 4 * N + 2 * C + 2 * L + 2 * t + 14) + (2 * G + 2 * N + 2 * t + 6)))

/-- **The mirror splice**: emit `encodeNat t` from the capacity-padded `t`-source, heal it,
advance. -/
theorem qt_instr_spliceT (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spliceJ = .spliceA)
    (hg : g ≤ G) (N C t k : ℕ) (ht : t ≤ C) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2TMachine body) (lptaCost G N C t OUT.length)
      ⟨(4, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(4, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jT N k ++ encodeD (OUT ++ encodeNat t))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jsT C t t).length = 2 * C + 2 := jsT_length C t t (le_refl t) ht
  have hq4 : (cntT G g).length + (cntT N (k + 1)).length + (jsT C t t).length
      + (jT N k).length = 2 * G + 4 * N + 2 * C + 8 := by
    rw [hW, hQ1, hQc, jT_length N k (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate t true).length = OUT.length + t := by
    rw [List.length_append, List.length_replicate]
  have g0 := qt_dispatch_spliceA (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD OUT)))) h hp
  have g1 := qt_spa_rounds body idx hg N C t k ht hk OUT t (le_refl t) s
  have g2 := qt_skipWAs body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))) 0 G idx
    (if t = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g2
  have g3 := qt_crossWA (body := body) (idx := idx)
    (s := if G = 0 then (if t = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g4 := qt_skipR1As body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g5 := qt_crossR1A (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g6 := qt_skipAms body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (2 * G + 2 + 2 * N + 2) t idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega]
      exact liftJ2 _ _ _ hW hQ1 (jsE_mark_lo C t t _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 _ _ _ hW hQ1 (jsE_mark_hi C t t _ i hi)⟩)
  have g7 := qt_doneA (body := body) (idx := idx) (s := if t = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t t _ (le_refl t)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t t _ (le_refl t)))
  have g8 := qt_scanD1s body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) ((C - t) + k) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (C - t) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t t _ (2 * t + 2 + 2 * i) (le_refl t)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t t _ (2 * t + 2 + 2 * i + 1) (le_refl t)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i) false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * (i - (C - t)))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i - (C - t))) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1) false = true := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * (i - (C - t)) + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ (2 * (i - (C - t)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * ((C - t) + k)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k from by omega] at g8
  have g9 := qt_crossSD1 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
      ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * t + 2) false ((C - t) + k))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
      ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N k 0 _ (by omega)))
  have g10 := qt_scanD2s body (cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) ((N - k) + (OUT.length + t)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
            ++ (jT N k ++ encodeD (OUT ++ List.replicate t true))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * C + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT G g) (cntT N (k + 1)) (jsT C t t) (jT N k)
          (OUT ++ List.replicate t true) (2 * G + 4 * N + 2 * C + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + t))
      = 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + t) from by omega] at g10
  have hm1 := preD4_mark_lo (cntT G g) (cntT N (k + 1)) (jsT C t t) (jT N k)
    (OUT ++ List.replicate t true) (2 * G + 4 * N + 2 * C + 8) hq4
  have hm2 := preD4_mark_hi (cntT G g) (cntT N (k + 1)) (jsT C t t) (jT N k)
    (OUT ++ List.replicate t true) (2 * G + 4 * N + 2 * C + 8) hq4
  rw [hlen2] at hm1 hm2
  have g11 := qt_detectD2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (jsT C t t
      ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
      (2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k + 2) false ((N - k) + (OUT.length + t)))
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + t)) hm1 hm2
  have hsn := writes_snoc4 (cntT G g) (cntT N (k + 1)) (jsT C t t) (jT N k)
    (OUT ++ List.replicate t true) (2 * G + 4 * N + 2 * C + 8) hq4 false
  rw [hlen2, List.append_assoc,
    show (List.replicate t true ++ [false] : List Bool) = encodeNat t from rfl] at hsn
  have g12 := qt_four_FA (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * C + 8 + 2 * (OUT.length + t))
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jsT C t t ++ (jT N k ++ encodeD (OUT ++ List.replicate t true)))))
  rw [hsn] at g12
  have g13 := qt_skipWhAs body (cntT G g ++ (cntT N (k + 1)
      ++ (jhT C t 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat t))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g13
  have g14 := qt_crossWhA (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N (k + 1)
      ++ (jhT C t 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat t)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g15 := qt_skipR1hAs body (cntT G g ++ (cntT N (k + 1)
      ++ (jhT C t 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat t))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g16 := qt_crossR1hA (body := body) (idx := idx)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jhT C t 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat t)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g17 := qt_healTs body (cntT G g) (cntT N (k + 1)) G N C t
    (jT N k ++ encodeD (OUT ++ encodeNat t)) hW hQ1 ht idx false t (le_refl t)
  have g18 := qt_doneHealA (body := body) (idx := idx)
    (s := if t = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1)
      ++ (jhT C t t ++ (jT N k ++ encodeD (OUT ++ encodeNat t))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jhE_m_lo C t _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hQ1 (jhE_m_hi C t _))
  rw [show lptaCost G N C t OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * C + 2 * OUT.length + 14) t
          + (2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * ((C - t) + k) + (2
            + (2 * ((N - k) + (OUT.length + t)) + (2 + (4 + (2 * G + (2 + (2 * N + (2
            + (2 * t + 2)))))))))))))))))
      from by simp only [lptaCost]; omega,
    run_add, g0, ← jsT_zero C t, run_add, g1, run_add, g2, run_add, g3, run_add, g4,
    run_add, g5, run_add, g6, run_add, g7, run_add, g8, run_add, g9, run_add, g10,
    run_add, g11, run_add, g12, ← jhT_zero C t, run_add, g13, run_add, g14, run_add, g15,
    run_add, g16, run_add, g17, g18, jhT_last, jsT_zero C t]

end InstrA2

/-! ## The instruction segment, the round, and the loop

The denotation is **literally** `prog2Out body t k` — the mirror splice emits `encodeNat t` exactly
as the exact-counter splice did, so every family body factorization reuses unchanged. -/

def ltInstrCost (body : List LInstr) (G N C t k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n .spliceJ with
  | .bit _ => 2 * G + 4 * N + 2 * C + 2 * (L + (prog2OutN body t k n).length) + 15
  | .spliceA => lptaCost G N C t (L + (prog2OutN body t k n).length)
  | .spliceJ => lptjCost G N C k (L + (prog2OutN body t k n).length)

def ltSegN (body : List LInstr) (G N C t k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ltSegN body G N C t k L n + ltInstrCost body G N C t k L n

/-- **The segment invariant** on the mirror layout. -/
theorem qt_run_instrs (body : List LInstr) (G g : ℕ) (hg : g ≤ G) (N C t k : ℕ)
    (ht : t ≤ C) (hk : k < N) (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (loopProg2TMachine body) (ltSegN body G N C t k out'.length n)
      ⟨(4, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (jT C t ++ (jT N k ++ encodeD out')))⟩
      = ⟨(4, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (jT C t
            ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k n))))⟩ := by
  induction n with
  | zero => simp only [ltSegN]; rw [run_zero]; simp [prog2OutN]
  | succ n ih =>
    rw [show ltSegN body G N C t k out'.length (n + 1)
        = ltSegN body G N C t k out'.length n + ltInstrCost body G N C t k out'.length n
        from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n .spliceJ with
    | bit b =>
      have hin := qt_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N C t k ht hk
        (out' ++ prog2OutN body t k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body t k n ++ [b] = prog2OutN body t k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [ltInstrCost, hp]
      rw [hin]
      simp
    | spliceA =>
      have hin := qt_instr_spliceT body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N C t k ht hk
        (out' ++ prog2OutN body t k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body t k n ++ encodeNat t = prog2OutN body t k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [ltInstrCost, hp]
      rw [hin]
      simp
    | spliceJ =>
      have hin := qt_instr_spliceJ body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N C t k ht hk
        (out' ++ prog2OutN body t k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body t k n ++ encodeNat k = prog2OutN body t k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [ltInstrCost, hp]
      rw [hin]
      simp

def ltRoundCost (body : List LInstr) (G N C t k L : ℕ) : ℕ :=
  (2 * G + 2 * k + 4) + (ltSegN body G N C t k L body.length
    + (2 * G + 2 * N + 2 * C + 2 * k + 13))

/-- **One loop round** on the mirror layout: the increment walk crosses the mirror's padding. -/
theorem qt_round (body : List LInstr) (G g : ℕ) (hg : g ≤ G) (N C t k : ℕ) (ht : t ≤ C)
    (hk : k < N) (out' : List Bool) (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (loopProg2TMachine body) (ltRoundCost body G N C t k out'.length)
      ⟨(0, ptrIn, s), 0, cntT G g ++ (cntT N k ++ (jT C t ++ (jT N k ++ encodeD out')))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N (k + 1)
            ++ encodeD (out' ++ prog2Out body t k))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hQ1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQc : (jT C t).length = 2 * C + 2 := jT_length C t ht
  have r0 := qt_skipWfs body (cntT G g ++ (cntT N k ++ (jT C t
      ++ (jT N k ++ encodeD out')))) 0 G ptrIn s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at r0
  have r0' := qt_crossWf (body := body) (idx := ptrIn) (s := if G = 0 then s else true)
    (p := 2 * G) (T := cntT G g ++ (cntT N k ++ (jT C t ++ (jT N k ++ encodeD out'))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r1 := qt_skipBms body (cntT G g ++ (cntT N k ++ (jT C t
      ++ (jT N k ++ encodeD out')))) (2 * G + 2) k ptrIn false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo N k _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi N k _ i hi)⟩)
  have r2 := qt_markB (body := body) (idx := ptrIn) (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * k)
    (T := cntT G g ++ (cntT N k ++ (jT C t ++ (jT N k ++ encodeD out'))))
    (by rw [show 2 * G + 2 + 2 * k = 2 * G + 2 + (2 * k) from rfl]
        exact liftJ _ _ hW (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * k + 1 = 2 * G + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hW (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G g ++ (cntT N k ++ (jT C t ++ (jT N k ++ encodeD out'))))
      (2 * G + 2 + 2 * k + 1) false
      = cntT G g ++ (cntT N (k + 1) ++ (jT C t ++ (jT N k ++ encodeD out'))) := by
    rw [show 2 * G + 2 + 2 * k + 1 = 2 * G + 2 + (2 * k + 1) from by omega,
      writeAt_append_right _ _ (2 * G + 2) (2 * k + 1) false hW
        (by rw [List.length_append, cntT_length N k (by omega)]; omega),
      cntT_mark N k _ hk]
  rw [hwm] at r2
  have r3 := qt_run_instrs body G g hg N C t k ht hk out' body.length (le_refl _) true
  have r4 := qt_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (Nat.lt_irrefl _)
  have r5 := qt_skipWis body (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length))))) 0 G
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at r5
  have r6 := qt_crossWi (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if G = 0 then (if body.length = 0 then true else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r7 := qt_skipR1is body (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length))))) (2 * G + 2) N
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have r8 := qt_crossR1i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have r9 := qt_skipR2is body (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (2 * G + 2 + 2 * N + 2) t ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1
        (jsE_data C t 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r10 := qt_crossR2i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if t = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * t)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t = 2 * G + 2 + (2 * N + 2 + 2 * t)
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_lo C t 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 1 = 2 * G + 2 + (2 * N + 2 + (2 * t + 1))
          from by omega, ← jsT_zero C t]
        exact liftJ2 _ _ _ hW hQ1 (jsE_m_hi C t 0 _ (by omega)))
  have r10b := qt_padIs body (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (2 * G + 2 + 2 * N + 2 + 2 * t + 2) (C - t) ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i)) from by omega, ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i) (by omega) (by omega)
        (by omega) (by omega)), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * t + 2 + 2 * i + 1)) from by omega,
        ← jsT_zero C t]
      exact liftJ2 _ _ _ hW hQ1 (jsE_pad C t 0 _ (2 * t + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega) (by omega))⟩)
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * t + 2 + 2 * (C - t)
      = 2 * G + 2 + 2 * N + 2 + 2 * C + 2 from by omega] at r10b
  have r10c := qt_padI_bound (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if C - t = 0 then false else false)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * C + 2)
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          refine Or.inr ⟨?_, ?_⟩
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega, ← jsT_zero N 0]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N 0 0 _ (by omega))
          · rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 1
                = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 1)) from by omega, ← jsT_zero N 0]
            exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_hi N 0 0 _ (by omega))
        · refine Or.inl ?_
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2
              = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 0)) from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hW hQ1 hQc
            (jsE_data N k 0 _ 0 (by omega) (by omega) (by omega)))
  have r11 := qt_walkIs body (cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (2 * G + 2 + 2 * N + 2 + 2 * C + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * i)) from by omega, ← jsT_zero N k]
      exact liftJ3 _ _ _ _ hW hQ1 hQc
        (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r12 := qt_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)))
    (T := cntT G g ++ (cntT N (k + 1) ++ (jT C t
      ++ (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)))))
    (by rw [← jsT_zero N k]
        exact liftJ3 _ _ _ _ hW hQ1 hQc (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right3 (cntT G g) (cntT N (k + 1)) (jT C t)
      (jT N k ++ encodeD (out' ++ prog2OutN body t k body.length)) (2 * G + 2) (2 * N + 2)
      (2 * C + 2) (2 * k) true true false true hW hQ1 hQc
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r12
  rw [show ltRoundCost body G N C t k out'.length
      = 2 * G + (2 + (2 * k + (2 + (ltSegN body G N C t k out'.length body.length + (1
          + (2 * G + (2 + (2 * N + (2 + (2 * t + (2 + (2 * (C - t) + (2
              + (2 * k + 4))))))))))))))
      from by simp only [ltRoundCost]; omega,
    run_add, r0, run_add, r0', run_add, r1, run_add, r2, run_add, r3, run_add, r4,
    run_add, r5, run_add, r6, run_add, r7, run_add, r8, run_add, r9, run_add, r10,
    run_add, r10b, run_add, r10c, run_add, r11,
    show 2 * G + 2 + 2 * N + 2 + 2 * C + 2 + 2 * k
      = 2 * G + 2 + (2 * N + 2 + (2 * C + 2 + 2 * k)) from by omega,
    r12, prog2Out]

def ltClockN (body : List LInstr) (G N C t Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ltClockN body G N C t Lout k
      + ltRoundCost body G N C t k (Lout + (loop2OutN body t k).length)

/-- **The rounds invariant** on the mirror layout. -/
theorem qt_run_rounds (body : List LInstr) (G g : ℕ) (hg : g ≤ G) (N C t : ℕ) (ht : t ≤ C)
    (out : List Bool) (k : ℕ) (hk : k ≤ N) (s : Bool) :
    run (loopProg2TMachine body) (ltClockN body G N C t out.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G g ++ (cntT N 0
        ++ (jT C t ++ (jT N 0 ++ encodeD out)))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT G g ++ (cntT N k ++ (jT C t
            ++ (jT N k ++ encodeD (out ++ loop2OutN body t k))))⟩ := by
  induction k with
  | zero => simp only [ltClockN]; rw [run_zero]; simp [loop2OutN]
  | succ k ih =>
    have hrd := qt_round body G g hg N C t k ht (by omega) (out ++ loop2OutN body t k)
      ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loop2OutN body t k ++ prog2Out body t k = loop2OutN body t (k + 1)
        from rfl] at hrd
    rw [show ltClockN body G N C t out.length (k + 1)
        = ltClockN body G N C t out.length k
            + ltRoundCost body G N C t k (out.length + (loop2OutN body t k).length)
        from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

def ltClock (body : List LInstr) (G N C t Lout : ℕ) : ℕ :=
  ltClockN body G N C t Lout N
    + (2 * G + (2 + (2 * N + (2 + (2 * G + (2 + (2 * N + 2)))))))

/-- **THE MIRROR-LAYOUT LOOP ENGINE RUNS TO COMPLETION** — grand prefix AND `t`-mirror preserved
verbatim: the interstitial can now `jT_incr` the mirror and hand the next round its own layout. -/
theorem loopProg2T_run (body : List LInstr) (G g : ℕ) (hg : g ≤ G) (N C t : ℕ) (ht : t ≤ C)
    (out : List Bool) :
    run (loopProg2TMachine body) (ltClock body G N C t out.length)
      (init (loopProg2TMachine body)
        (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N 0 ++ encodeD out)))))
      = ⟨(94, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * N + 1,
          cntT G g ++ (unaryD N ++ (jT C t
            ++ (unaryD N ++ encodeD (out ++ loop2Out body t N))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  rw [init_lt]
  rw [show (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N 0 ++ encodeD out))) : List Bool)
      = cntT G g ++ (cntT N 0 ++ (jT C t ++ (jT N 0 ++ encodeD out))) from by
    rw [cntT_zero]]
  simp only [ltClock]
  have f0 := qt_skipWfs body (cntT G g ++ (cntT N N ++ (jT C t
      ++ (jT N N ++ encodeD (out ++ loop2OutN body t N))))) 0 G ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0
  have f0' := qt_crossWf (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N N ++ (jT C t ++ (jT N N
      ++ encodeD (out ++ loop2OutN body t N)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := qt_skipBms body (cntT G g ++ (cntT N N ++ (jT C t
      ++ (jT N N ++ encodeD (out ++ loop2OutN body t N))))) (2 * G + 2) N
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo N N _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi N N _ i hi)⟩)
  have f2 := qt_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N N ++ (jT C t ++ (jT N N
      ++ encodeD (out ++ loop2OutN body t N)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N N _ (le_refl N)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N N _ (le_refl N)))
  have f3 := qt_skipWfins body (cntT G g ++ (hlT N 0 ++ (jT C t
      ++ (jT N N ++ encodeD (out ++ loop2OutN body t N))))) 0 G ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f3
  have f3' := qt_crossWfin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (hlT N 0 ++ (jT C t ++ (jT N N
      ++ encodeD (out ++ loop2OutN body t N)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f4 := qt_healBs body (cntT G g) G N
    (jT C t ++ (jT N N ++ encodeD (out ++ loop2OutN body t N))) hW
    ⟨0, Nat.succ_pos _⟩ false N (le_refl N)
  have f5 := qt_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (hlT N N ++ (jT C t ++ (jT N N
      ++ encodeD (out ++ loop2OutN body t N)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (hlE_cm_lo N _))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (hlE_cm_hi N _))
  rw [run_add, qt_run_rounds body G g hg N C t ht out N (le_refl N) false, ite_self,
    run_add, f0, run_add, f0', run_add, f1, run_add, f2, ← hlT_zero, run_add, f3,
    run_add, f3', run_add, f4, f5, hlT_last,
    show jT N N = unaryD N from jT_full N,
    show loop2Out body t N = loop2OutN body t N from rfl]

/-- The machine **halts by itself** at its clock. -/
theorem loopProg2T_halted (body : List LInstr) (G g : ℕ) (hg : g ≤ G) (N C t : ℕ)
    (ht : t ≤ C) (out : List Bool) :
    (loopProg2TMachine body).halt
      (run (loopProg2TMachine body) (ltClock body G N C t out.length)
        (init (loopProg2TMachine body)
          (cntT G g ++ (unaryD N ++ (jT C t ++ (jT N 0 ++ encodeD out)))))).st = true := by
  rw [loopProg2T_run body G g hg N C t ht out]; rfl

/-! ## Polynomial clock bounds -/

/-- The per-instruction cap. -/
def ltCap (G N C LM : ℕ) : ℕ :=
  C * (2 * G + 4 * N + 2 * C + 2 * LM + 14 + 2 * C)
    + N * (2 * G + 4 * N + 2 * C + 2 * LM + 16 + 2 * N)
    + (2 * G + 4 * N + 2 * C + 2 * LM + 2 * C + 15) + (2 * G + 2 * N + 2 * C + 7)
    + (2 * G + 4 * N + 2 * C + 2 * LM + 2 * N + 17) + (2 * G + 2 * N + 2 * C + 2 * N + 11)
    + (2 * G + 4 * N + 2 * C + 2 * LM + 15)

theorem ltInstrCost_le (body : List LInstr) (G N C t k L n LM : ℕ) (ht : t ≤ C)
    (hk : k < N) (hn : n ≤ body.length) (hL : L + body.length * (t + N + 1) ≤ LM) :
    ltInstrCost body G N C t k L n ≤ ltCap G N C LM := by
  have hlen : (prog2OutN body t k n).length ≤ body.length * (t + N + 1) :=
    le_trans (prog2OutN_length_le body t k n) (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n .spliceJ with
  | bit b =>
    simp only [ltInstrCost, hp, ltCap]
    omega
  | spliceA =>
    have h1 := lp3SpRounds_le (2 * G + 4 * N + 2 * C
        + 2 * (L + (prog2OutN body t k n).length) + 14)
      (2 * G + 4 * N + 2 * C + 2 * LM + 14) t C (by omega) ht
    have h2 : t * (2 * G + 4 * N + 2 * C + 2 * LM + 14 + 2 * C)
        ≤ C * (2 * G + 4 * N + 2 * C + 2 * LM + 14 + 2 * C) :=
      Nat.mul_le_mul_right _ ht
    simp only [ltInstrCost, hp, lptaCost, ltCap]
    omega
  | spliceJ =>
    have h1 := lp3SpRounds_le (2 * G + 4 * N + 2 * C
        + 2 * (L + (prog2OutN body t k n).length) + 16)
      (2 * G + 4 * N + 2 * C + 2 * LM + 16) k N (by omega) (by omega)
    have h2 : k * (2 * G + 4 * N + 2 * C + 2 * LM + 16 + 2 * N)
        ≤ N * (2 * G + 4 * N + 2 * C + 2 * LM + 16 + 2 * N) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [ltInstrCost, hp, lptjCost, ltCap]
    omega

theorem ltSegN_le (body : List LInstr) (G N C t k L n LM : ℕ) (ht : t ≤ C) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (t + N + 1) ≤ LM) :
    ltSegN body G N C t k L n ≤ n * ltCap G N C LM := by
  induction n with
  | zero => simp [ltSegN]
  | succ n ih =>
    calc ltSegN body G N C t k L (n + 1)
        = ltSegN body G N C t k L n + ltInstrCost body G N C t k L n := rfl
      _ ≤ n * ltCap G N C LM + ltCap G N C LM :=
          Nat.add_le_add (ih (by omega))
            (ltInstrCost_le body G N C t k L n LM ht hk (by omega) hL)
      _ = (n + 1) * ltCap G N C LM := by ring

theorem ltRoundCost_le (body : List LInstr) (G N C t k L LM : ℕ) (ht : t ≤ C) (hk : k < N)
    (hL : L + body.length * (t + N + 1) ≤ LM) :
    ltRoundCost body G N C t k L
      ≤ body.length * ltCap G N C LM + (4 * G + 6 * N + 2 * C + 17) := by
  have h := ltSegN_le body G N C t k L body.length LM ht hk (le_refl _) hL
  simp only [ltRoundCost]
  omega

/-- **The mirror-layout clock is polynomial.** -/
theorem ltClock_le (body : List LInstr) (G N C t Lout : ℕ) (ht : t ≤ C) :
    ltClock body G N C t Lout
      ≤ N * (body.length * ltCap G N C (Lout + N * (body.length * (t + N + 1))
            + body.length * (t + N + 1)) + (4 * G + 6 * N + 2 * C + 17))
        + (4 * G + 4 * N + 8) := by
  have hrounds : ∀ k, k ≤ N → ltClockN body G N C t Lout k
      ≤ k * (body.length * ltCap G N C (Lout + N * (body.length * (t + N + 1))
            + body.length * (t + N + 1)) + (4 * G + 6 * N + 2 * C + 17)) := by
    intro k hk
    induction k with
    | zero => simp [ltClockN]
    | succ k ih =>
      have hLk : (Lout + (loop2OutN body t k).length) + body.length * (t + N + 1)
          ≤ Lout + N * (body.length * (t + N + 1)) + body.length * (t + N + 1) := by
        have h1 : (loop2OutN body t k).length ≤ k * (body.length * (t + N + 1)) :=
          loop2OutN_length_le body N t k (by omega)
        have h2 : k * (body.length * (t + N + 1)) ≤ N * (body.length * (t + N + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      calc ltClockN body G N C t Lout (k + 1)
          = ltClockN body G N C t Lout k
              + ltRoundCost body G N C t k (Lout + (loop2OutN body t k).length) := rfl
        _ ≤ k * (body.length * ltCap G N C (Lout + N * (body.length * (t + N + 1))
                + body.length * (t + N + 1)) + (4 * G + 6 * N + 2 * C + 17))
            + (body.length * ltCap G N C (Lout + N * (body.length * (t + N + 1))
                + body.length * (t + N + 1)) + (4 * G + 6 * N + 2 * C + 17)) :=
            Nat.add_le_add (ih (by omega))
              (ltRoundCost_le body G N C t k (Lout + (loop2OutN body t k).length) _ ht
                (by omega) hLk)
        _ = (k + 1) * (body.length * ltCap G N C (Lout + N * (body.length * (t + N + 1))
                + body.length * (t + N + 1)) + (4 * G + 6 * N + 2 * C + 17)) := by ring
  have h := hrounds N (le_refl N)
  simp only [ltClock]
  omega

/-! ## THE LIVE-`t` FAMILY DEMONSTRATION -/

/-- **The tape-copy family at the LIVE round index**: the engine reads `t` from the capacity-padded
mirror and emits the whole time-`t` family — grand prefix and mirror preserved verbatim, ready for
the interstitial's in-place `jT_incr`. -/
theorem cellCopyT_family_run (G g : ℕ) (hg : g ≤ G) (C t : ℕ) (ht : t ≤ C) (P : ℕ)
    (out : List Bool) :
    run (loopProg2TMachine cellCopyBody) (ltClock cellCopyBody G (P + 1) C t out.length)
      (init (loopProg2TMachine cellCopyBody)
        (cntT G g ++ (unaryD (P + 1) ++ (jT C t ++ (jT (P + 1) 0 ++ encodeD out)))))
      = ⟨(94, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * (P + 1) + 1,
          cntT G g ++ (unaryD (P + 1) ++ (jT C t ++ (unaryD (P + 1) ++ encodeD (out
            ++ ((List.range (P + 1)).map (fun p =>
                encodeClause' [(headVar t p, true), (cellVar (t + 1) p, false),
                  (cellVar t p, true)]
                  ++ encodeClause' [(headVar t p, true), (cellVar (t + 1) p, true),
                       (cellVar t p, false)])).flatten))))⟩ := by
  have h := loopProg2T_run cellCopyBody G g hg (P + 1) C t ht out
  rwa [cellCopy_split] at h
end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2T
