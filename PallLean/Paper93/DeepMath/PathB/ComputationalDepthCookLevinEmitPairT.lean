import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMajorant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRearmT

/-!
# Cook–Levin M2 emitter — the triangle engine (control layer)

`pairTMachine` is the amoPair-triangle engine's control: `loopProg3PMachine`'s phases `0–116`
verbatim, plus ten second-level prefix-skip pairs (`117–136`, the `addTPP` chaining — the engine
runs under TWO loop counters: the grand round and the row loop) and fifteen pad-crossing pairs
(`137–166`, one per low-lo hand-off that crosses a padded region into a find/heal/walk — the
layout pads the bound, both sources, and the live variable; see `TRIANGLE_PLAN.md`).  The
boundary-event scans absorb padding as equal pairs, so the bit track and every splice seek keep
their phases; the loop find and the finale heal are content-blind on the padded bound.  This file
lands the machine, its full step layer, the six-region lift layer, the `jhT` heal walks, the
four instruction lemmas (`qp_instr_bit`, `qp_instr_spAo`, `qp_instr_spCo`, `qp_instr_spJo`) with
their `j`-independent clocks, the segment invariant (`qp_run_instrs`), and the loop round
(`qp_round`: find-mark on the padded bound, the body, the in-place increment across the three
pads), the rounds invariant (`qp_run_rounds`), and the loop completion (`pairT_run`,
`pairT_halted`: the engine drives the live variable to the bound's value and the content-blind
finale heals the padded bound in place); the row interstitial and the triangle composite follow
in the continuation bricks.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P (liftJ4 writeAt_append_right4
  W4_append_right4 preD5_data_eq preD5_mark_lo preD5_mark_hi writes_snoc5)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

set_option maxRecDepth 8192 in
def pairTMachine (body : List L3Instr) : Machine where
  State := Fin 167 × Fin (body.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (97, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 96)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 3)
         else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((115, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val .spJo with
         | .bit _ => ((99, s.2.1, s.2.2), none, 2)
         | .spAo => ((101, s.2.1, s.2.2), none, 2)
         | .spCo => ((105, s.2.1, s.2.2), none, 2)
         | .spJo => ((109, s.2.1, s.2.2), none, 2))
       else ((113, s.2.1, s.2.2), none, 2))
    else if s.1 = 3 then ((4, s.2.1, b), none, 1)
    else if s.1 = 4 then
      (if s.2.2 then ((3, s.2.1, s.2.2), none, 1)
       else (if b then ((5, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if b = s.2.2 then ((5, s.2.1, s.2.2), none, 1) else ((7, s.2.1, s.2.2), none, 1))
    else if s.1 = 7 then ((8, s.2.1, b), none, 1)
    else if s.1 = 8 then
      (if b = s.2.2 then ((7, s.2.1, s.2.2), none, 1) else ((9, s.2.1, s.2.2), none, 1))
    else if s.1 = 9 then ((10, s.2.1, b), none, 1)
    else if s.1 = 10 then
      (if b = s.2.2 then ((9, s.2.1, s.2.2), none, 1) else ((11, s.2.1, s.2.2), none, 1))
    else if s.1 = 11 then ((12, s.2.1, b), none, 1)
    else if s.1 = 12 then
      (if b = s.2.2 then ((11, s.2.1, s.2.2), none, 1) else ((13, s.2.1, s.2.2), none, 0))
    else if s.1 = 13 then
      ((14, s.2.1, s.2.2), some (body.getD s.2.1.val .spJo).bitVal, 1)
    else if s.1 = 14 then
      ((15, s.2.1, s.2.2), some (body.getD s.2.1.val .spJo).bitVal, 1)
    else if s.1 = 15 then ((16, s.2.1, s.2.2), some false, 1)
    else if s.1 = 16 then
      (if h : s.2.1.val + 1 < body.length + 1 then
        ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((96, s.2.1, s.2.2), some true, 2))
    else if s.1 = 17 then ((18, s.2.1, b), none, 1)
    else if s.1 = 18 then
      (if s.2.2 then ((17, s.2.1, s.2.2), none, 1)
       else (if b then ((137, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 19 then ((20, s.2.1, b), none, 1)
    else if s.1 = 20 then
      (if s.2.2 then
        (if b then ((21, s.2.1, s.2.2), some false, 1) else ((19, s.2.1, s.2.2), none, 1))
       else (if b then ((103, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 21 then ((22, s.2.1, b), none, 1)
    else if s.1 = 22 then
      (if b = s.2.2 then ((21, s.2.1, s.2.2), none, 1) else ((23, s.2.1, s.2.2), none, 1))
    else if s.1 = 23 then ((24, s.2.1, b), none, 1)
    else if s.1 = 24 then
      (if b = s.2.2 then ((23, s.2.1, s.2.2), none, 1) else ((25, s.2.1, s.2.2), none, 1))
    else if s.1 = 25 then ((26, s.2.1, b), none, 1)
    else if s.1 = 26 then
      (if b = s.2.2 then ((25, s.2.1, s.2.2), none, 1) else ((27, s.2.1, s.2.2), none, 1))
    else if s.1 = 27 then ((28, s.2.1, b), none, 1)
    else if s.1 = 28 then
      (if b = s.2.2 then ((27, s.2.1, s.2.2), none, 1) else ((29, s.2.1, s.2.2), none, 0))
    else if s.1 = 29 then ((30, s.2.1, s.2.2), some true, 1)
    else if s.1 = 30 then ((31, s.2.1, s.2.2), some true, 1)
    else if s.1 = 31 then ((32, s.2.1, s.2.2), some false, 1)
    else if s.1 = 32 then ((101, s.2.1, s.2.2), some true, 3)
    else if s.1 = 33 then ((34, s.2.1, b), none, 1)
    else if s.1 = 34 then
      (if s.2.2 then ((33, s.2.1, s.2.2), none, 1)
       else (if b then ((139, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 35 then ((36, s.2.1, b), none, 1)
    else if s.1 = 36 then
      (if s.2.2 then
        (if b then ((96, s.2.1, s.2.2), none, 2) else ((35, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((96, s.2.1, s.2.2), none, 2))
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 37 then ((38, s.2.1, b), none, 1)
    else if s.1 = 38 then
      (if s.2.2 then ((37, s.2.1, s.2.2), none, 1)
       else (if b then ((141, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 39 then ((40, s.2.1, b), none, 1)
    else if s.1 = 40 then
      (if s.2.2 then ((39, s.2.1, s.2.2), none, 1)
       else (if b then ((143, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 41 then ((42, s.2.1, b), none, 1)
    else if s.1 = 42 then
      (if s.2.2 then
        (if b then ((43, s.2.1, s.2.2), some false, 1) else ((41, s.2.1, s.2.2), none, 1))
       else (if b then ((107, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 43 then ((44, s.2.1, b), none, 1)
    else if s.1 = 44 then
      (if b = s.2.2 then ((43, s.2.1, s.2.2), none, 1) else ((45, s.2.1, s.2.2), none, 1))
    else if s.1 = 45 then ((46, s.2.1, b), none, 1)
    else if s.1 = 46 then
      (if b = s.2.2 then ((45, s.2.1, s.2.2), none, 1) else ((47, s.2.1, s.2.2), none, 1))
    else if s.1 = 47 then ((48, s.2.1, b), none, 1)
    else if s.1 = 48 then
      (if b = s.2.2 then ((47, s.2.1, s.2.2), none, 1) else ((49, s.2.1, s.2.2), none, 0))
    else if s.1 = 49 then ((50, s.2.1, s.2.2), some true, 1)
    else if s.1 = 50 then ((51, s.2.1, s.2.2), some true, 1)
    else if s.1 = 51 then ((52, s.2.1, s.2.2), some false, 1)
    else if s.1 = 52 then ((105, s.2.1, s.2.2), some true, 3)
    else if s.1 = 53 then ((54, s.2.1, b), none, 1)
    else if s.1 = 54 then
      (if s.2.2 then ((53, s.2.1, s.2.2), none, 1)
       else (if b then ((145, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 55 then ((56, s.2.1, b), none, 1)
    else if s.1 = 56 then
      (if s.2.2 then ((55, s.2.1, s.2.2), none, 1)
       else (if b then ((147, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 57 then ((58, s.2.1, b), none, 1)
    else if s.1 = 58 then
      (if s.2.2 then
        (if b then ((96, s.2.1, s.2.2), none, 2) else ((57, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((96, s.2.1, s.2.2), none, 2))
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 59 then ((60, s.2.1, b), none, 1)
    else if s.1 = 60 then
      (if s.2.2 then ((59, s.2.1, s.2.2), none, 1)
       else (if b then ((149, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 61 then ((62, s.2.1, b), none, 1)
    else if s.1 = 62 then
      (if s.2.2 then ((61, s.2.1, s.2.2), none, 1)
       else (if b then ((151, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 63 then ((64, s.2.1, b), none, 1)
    else if s.1 = 64 then
      (if s.2.2 then ((63, s.2.1, s.2.2), none, 1)
       else (if b then ((153, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 65 then ((66, s.2.1, b), none, 1)
    else if s.1 = 66 then
      (if s.2.2 then
        (if b then ((67, s.2.1, s.2.2), some false, 1) else ((65, s.2.1, s.2.2), none, 1))
       else (if b then ((111, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 67 then ((68, s.2.1, b), none, 1)
    else if s.1 = 68 then
      (if b = s.2.2 then ((67, s.2.1, s.2.2), none, 1) else ((69, s.2.1, s.2.2), none, 1))
    else if s.1 = 69 then ((70, s.2.1, b), none, 1)
    else if s.1 = 70 then
      (if b = s.2.2 then ((69, s.2.1, s.2.2), none, 1) else ((71, s.2.1, s.2.2), none, 0))
    else if s.1 = 71 then ((72, s.2.1, s.2.2), some true, 1)
    else if s.1 = 72 then ((73, s.2.1, s.2.2), some true, 1)
    else if s.1 = 73 then ((74, s.2.1, s.2.2), some false, 1)
    else if s.1 = 74 then ((109, s.2.1, s.2.2), some true, 3)
    else if s.1 = 75 then ((76, s.2.1, b), none, 1)
    else if s.1 = 76 then
      (if s.2.2 then ((75, s.2.1, s.2.2), none, 1)
       else (if b then ((155, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 77 then ((78, s.2.1, b), none, 1)
    else if s.1 = 78 then
      (if s.2.2 then ((77, s.2.1, s.2.2), none, 1)
       else (if b then ((157, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 79 then ((80, s.2.1, b), none, 1)
    else if s.1 = 80 then
      (if s.2.2 then ((79, s.2.1, s.2.2), none, 1)
       else (if b then ((159, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 81 then ((82, s.2.1, b), none, 1)
    else if s.1 = 82 then
      (if s.2.2 then
        (if b then ((96, s.2.1, s.2.2), none, 2) else ((81, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((96, s.2.1, s.2.2), none, 2))
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 83 then ((84, s.2.1, b), none, 1)
    else if s.1 = 84 then
      (if s.2.2 then ((83, s.2.1, s.2.2), none, 1)
       else (if b then ((161, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 85 then ((86, s.2.1, b), none, 1)
    else if s.1 = 86 then
      (if s.2.2 then ((85, s.2.1, s.2.2), none, 1)
       else (if b then ((163, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 87 then ((88, s.2.1, b), none, 1)
    else if s.1 = 88 then
      (if s.2.2 then ((87, s.2.1, s.2.2), none, 1)
       else (if b then ((165, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 89 then
      (if b then ((90, s.2.1, b), none, 1) else ((91, s.2.1, s.2.2), some true, 1))
    else if s.1 = 90 then ((89, s.2.1, s.2.2), none, 1)
    else if s.1 = 91 then ((92, s.2.1, s.2.2), some true, 1)
    else if s.1 = 92 then ((93, s.2.1, s.2.2), some false, 1)
    else if s.1 = 93 then ((97, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 94 then ((95, s.2.1, b), none, 1)
    else if s.1 = 95 then
      (if s.2.2 then
        (if b then ((96, s.2.1, false), none, 2) else ((94, s.2.1, true), some true, 1))
       else (if b then ((96, s.2.1, false), none, 2) else ((96, s.2.1, false), none, 2)))
    else if s.1 = 97 then ((98, s.2.1, b), none, 1)
    else if s.1 = 98 then
      (if s.2.2 then ((97, s.2.1, s.2.2), none, 1)
       else (if b then ((117, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 99 then ((100, s.2.1, b), none, 1)
    else if s.1 = 100 then
      (if s.2.2 then ((99, s.2.1, s.2.2), none, 1)
       else (if b then ((119, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 101 then ((102, s.2.1, b), none, 1)
    else if s.1 = 102 then
      (if s.2.2 then ((101, s.2.1, s.2.2), none, 1)
       else (if b then ((121, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 103 then ((104, s.2.1, b), none, 1)
    else if s.1 = 104 then
      (if s.2.2 then ((103, s.2.1, s.2.2), none, 1)
       else (if b then ((123, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 105 then ((106, s.2.1, b), none, 1)
    else if s.1 = 106 then
      (if s.2.2 then ((105, s.2.1, s.2.2), none, 1)
       else (if b then ((125, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 107 then ((108, s.2.1, b), none, 1)
    else if s.1 = 108 then
      (if s.2.2 then ((107, s.2.1, s.2.2), none, 1)
       else (if b then ((127, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 109 then ((110, s.2.1, b), none, 1)
    else if s.1 = 110 then
      (if s.2.2 then ((109, s.2.1, s.2.2), none, 1)
       else (if b then ((129, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 111 then ((112, s.2.1, b), none, 1)
    else if s.1 = 112 then
      (if s.2.2 then ((111, s.2.1, s.2.2), none, 1)
       else (if b then ((131, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 113 then ((114, s.2.1, b), none, 1)
    else if s.1 = 114 then
      (if s.2.2 then ((113, s.2.1, s.2.2), none, 1)
       else (if b then ((133, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 115 then ((116, s.2.1, b), none, 1)
    else if s.1 = 116 then
      (if s.2.2 then ((115, s.2.1, s.2.2), none, 1)
       else (if b then ((135, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 117 then ((118, s.2.1, b), none, 1)
    else if s.1 = 118 then
      (if s.2.2 then ((117, s.2.1, s.2.2), none, 1)
       else (if b then ((0, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 119 then ((120, s.2.1, b), none, 1)
    else if s.1 = 120 then
      (if s.2.2 then ((119, s.2.1, s.2.2), none, 1)
       else (if b then ((3, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 121 then ((122, s.2.1, b), none, 1)
    else if s.1 = 122 then
      (if s.2.2 then ((121, s.2.1, s.2.2), none, 1)
       else (if b then ((17, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 123 then ((124, s.2.1, b), none, 1)
    else if s.1 = 124 then
      (if s.2.2 then ((123, s.2.1, s.2.2), none, 1)
       else (if b then ((33, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 125 then ((126, s.2.1, b), none, 1)
    else if s.1 = 126 then
      (if s.2.2 then ((125, s.2.1, s.2.2), none, 1)
       else (if b then ((37, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 127 then ((128, s.2.1, b), none, 1)
    else if s.1 = 128 then
      (if s.2.2 then ((127, s.2.1, s.2.2), none, 1)
       else (if b then ((53, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 129 then ((130, s.2.1, b), none, 1)
    else if s.1 = 130 then
      (if s.2.2 then ((129, s.2.1, s.2.2), none, 1)
       else (if b then ((59, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 131 then ((132, s.2.1, b), none, 1)
    else if s.1 = 132 then
      (if s.2.2 then ((131, s.2.1, s.2.2), none, 1)
       else (if b then ((75, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 133 then ((134, s.2.1, b), none, 1)
    else if s.1 = 134 then
      (if s.2.2 then ((133, s.2.1, s.2.2), none, 1)
       else (if b then ((83, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 135 then ((136, s.2.1, b), none, 1)
    else if s.1 = 136 then
      (if s.2.2 then ((135, s.2.1, s.2.2), none, 1)
       else (if b then ((94, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 137 then ((138, s.2.1, b), none, 1)
    else if s.1 = 138 then
      (if s.2.2 then ((19, s.2.1, false), none, 0)
       else (if b then ((19, s.2.1, false), none, 0)
             else ((137, s.2.1, s.2.2), none, 1)))
    else if s.1 = 139 then ((140, s.2.1, b), none, 1)
    else if s.1 = 140 then
      (if s.2.2 then ((35, s.2.1, false), none, 0)
       else (if b then ((35, s.2.1, false), none, 0)
             else ((139, s.2.1, s.2.2), none, 1)))
    else if s.1 = 141 then ((142, s.2.1, b), none, 1)
    else if s.1 = 142 then
      (if s.2.2 then ((39, s.2.1, false), none, 0)
       else (if b then ((39, s.2.1, false), none, 0)
             else ((141, s.2.1, s.2.2), none, 1)))
    else if s.1 = 143 then ((144, s.2.1, b), none, 1)
    else if s.1 = 144 then
      (if s.2.2 then ((41, s.2.1, false), none, 0)
       else (if b then ((41, s.2.1, false), none, 0)
             else ((143, s.2.1, s.2.2), none, 1)))
    else if s.1 = 145 then ((146, s.2.1, b), none, 1)
    else if s.1 = 146 then
      (if s.2.2 then ((55, s.2.1, false), none, 0)
       else (if b then ((55, s.2.1, false), none, 0)
             else ((145, s.2.1, s.2.2), none, 1)))
    else if s.1 = 147 then ((148, s.2.1, b), none, 1)
    else if s.1 = 148 then
      (if s.2.2 then ((57, s.2.1, false), none, 0)
       else (if b then ((57, s.2.1, false), none, 0)
             else ((147, s.2.1, s.2.2), none, 1)))
    else if s.1 = 149 then ((150, s.2.1, b), none, 1)
    else if s.1 = 150 then
      (if s.2.2 then ((61, s.2.1, false), none, 0)
       else (if b then ((61, s.2.1, false), none, 0)
             else ((149, s.2.1, s.2.2), none, 1)))
    else if s.1 = 151 then ((152, s.2.1, b), none, 1)
    else if s.1 = 152 then
      (if s.2.2 then ((63, s.2.1, false), none, 0)
       else (if b then ((63, s.2.1, false), none, 0)
             else ((151, s.2.1, s.2.2), none, 1)))
    else if s.1 = 153 then ((154, s.2.1, b), none, 1)
    else if s.1 = 154 then
      (if s.2.2 then ((65, s.2.1, false), none, 0)
       else (if b then ((65, s.2.1, false), none, 0)
             else ((153, s.2.1, s.2.2), none, 1)))
    else if s.1 = 155 then ((156, s.2.1, b), none, 1)
    else if s.1 = 156 then
      (if s.2.2 then ((77, s.2.1, false), none, 0)
       else (if b then ((77, s.2.1, false), none, 0)
             else ((155, s.2.1, s.2.2), none, 1)))
    else if s.1 = 157 then ((158, s.2.1, b), none, 1)
    else if s.1 = 158 then
      (if s.2.2 then ((79, s.2.1, false), none, 0)
       else (if b then ((79, s.2.1, false), none, 0)
             else ((157, s.2.1, s.2.2), none, 1)))
    else if s.1 = 159 then ((160, s.2.1, b), none, 1)
    else if s.1 = 160 then
      (if s.2.2 then ((81, s.2.1, false), none, 0)
       else (if b then ((81, s.2.1, false), none, 0)
             else ((159, s.2.1, s.2.2), none, 1)))
    else if s.1 = 161 then ((162, s.2.1, b), none, 1)
    else if s.1 = 162 then
      (if s.2.2 then ((85, s.2.1, false), none, 0)
       else (if b then ((85, s.2.1, false), none, 0)
             else ((161, s.2.1, s.2.2), none, 1)))
    else if s.1 = 163 then ((164, s.2.1, b), none, 1)
    else if s.1 = 164 then
      (if s.2.2 then ((87, s.2.1, false), none, 0)
       else (if b then ((87, s.2.1, false), none, 0)
             else ((163, s.2.1, s.2.2), none, 1)))
    else if s.1 = 165 then ((166, s.2.1, b), none, 1)
    else if s.1 = 166 then
      (if s.2.2 then ((89, s.2.1, false), none, 0)
       else (if b then ((89, s.2.1, false), none, 0)
             else ((165, s.2.1, s.2.2), none, 1)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false


theorem init_pt (body : List L3Instr) (t : List Bool) :
    init (pairTMachine body) t
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl


/-! ## The step layer — phases 0–96 verbatim from the unprefixed machine -/

section Steps
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qp_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .bit b) :
    run (pairTMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(99, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, pairTMachine, moveHead, h, hp']

theorem qp_dispatch_spAo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spAo) :
    run (pairTMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(101, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spAo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, pairTMachine, moveHead, h, hp']

theorem qp_dispatch_spCo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spCo) :
    run (pairTMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(105, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spCo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, pairTMachine, moveHead, h, hp']

theorem qp_dispatch_spJo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spJo) :
    run (pairTMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(109, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spJo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, pairTMachine, moveHead, h, hp']

theorem qp_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (pairTMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(113, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, pairTMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps3
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qp_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(115, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipB1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossB1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipA1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(17, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(137, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphA1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(33, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(139, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipC1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(37, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(141, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipC2 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(39, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(143, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphC1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(53, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(145, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphC2 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(55, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(147, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipJr1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(59, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossJr1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(149, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipJr2 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(61, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossJr2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(151, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipJr3 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(63, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossJr3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(153, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphJ1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(75, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(155, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphJ2 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(77, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(157, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skiphJ3 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crosshJ3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(159, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipi1 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(83, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossi1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(161, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipi2 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossi2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(163, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipi3 (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(87, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossi3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(165, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanB2 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanB3 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(7, idx, s), p, T⟩
      = ⟨(7, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanB4 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanB5 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(21, idx, s), p, T⟩
      = ⟨(21, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanA4 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(25, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanA5 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanC3 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(43, idx, s), p, T⟩
      = ⟨(43, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanC4 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(45, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanC5 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanJ4 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(67, idx, s), p, T⟩
      = ⟨(67, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_scanJ5 (h : T.getD p false = T.getD (p + 1) false) :
    run (pairTMachine body) 2 ⟨(69, idx, s), p, T⟩
      = ⟨(69, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_crossSB2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSB3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSB4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSA4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(27, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSC3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSC4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(47, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_crossSJ4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2']

theorem qp_detectB5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qp_detectA5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qp_detectC5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(49, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qp_detectJ5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(71, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, pairTMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem qp_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(19, idx, s), p, T⟩
      = ⟨(21, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(103, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipCm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_markC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(41, idx, s), p, T⟩
      = ⟨(43, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneC (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(107, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(65, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(67, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(111, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(35, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2, h]

theorem qp_healC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneHealC (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2, h]

theorem qp_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(81, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2, h]

theorem qp_four_TA :
    run (pairTMachine body) 4 ⟨(29, idx, s), p, T⟩
      = ⟨(101, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (pairTMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (pairTMachine body) ⟨(30, idx, s), p', T'⟩
      = ⟨(31, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (pairTMachine body) ⟨(31, idx, s), p', T'⟩
      = ⟨(32, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (pairTMachine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(101, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qp_four_TC :
    run (pairTMachine body) 4 ⟨(49, idx, s), p, T⟩
      = ⟨(105, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (pairTMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (pairTMachine body) ⟨(50, idx, s), p', T'⟩
      = ⟨(51, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (pairTMachine body) ⟨(51, idx, s), p', T'⟩
      = ⟨(52, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (pairTMachine body) ⟨(52, idx, s), p', T'⟩
      = ⟨(105, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem qp_four_TJ :
    run (pairTMachine body) 4 ⟨(71, idx, s), p, T⟩
      = ⟨(109, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (pairTMachine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (pairTMachine body) ⟨(72, idx, s), p', T'⟩
      = ⟨(73, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (pairTMachine body) ⟨(73, idx, s), p', T'⟩
      = ⟨(74, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (pairTMachine body) ⟨(74, idx, s), p', T'⟩
      = ⟨(109, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

/-- The append snoc: the instruction's bit doubled plus the closing marker; advance. -/
theorem qp_four_bit (h : idx.val + 1 < body.length + 1) :
    run (pairTMachine body) 4 ⟨(13, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spJo).bitVal)
            (p + 1) (body.getD idx.val .spJo).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (pairTMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, s), p + 1, writeAt T p (body.getD idx.val .spJo).bitVal⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (pairTMachine body) ⟨(14, idx, s), p', T'⟩
      = ⟨(15, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spJo).bitVal⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (pairTMachine body) ⟨(15, idx, s), p', T'⟩
      = ⟨(16, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (pairTMachine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, pairTMachine, moveHead, h]
  rw [e1, e2, e3, e4]

theorem qp_walkI (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(89, idx, s), p, T⟩ = ⟨(89, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(89, idx, s), p, T⟩
      = ⟨(90, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, pairTMachine, moveHead, h1']
  rw [e0]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_four_incr (h1 : T.getD p false = false) :
    run (pairTMachine body) 4 ⟨(89, idx, s), p, T⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e89 : step (pairTMachine body) ⟨(89, idx, s), p, T⟩
      = ⟨(91, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, pairTMachine, moveHead, h1']
  have e91 : ∀ p' T', step (pairTMachine body) ⟨(91, idx, s), p', T'⟩
      = ⟨(92, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e92 : ∀ p' T', step (pairTMachine body) ⟨(92, idx, s), p', T'⟩
      = ⟨(93, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  have e93 : ∀ p' T', step (pairTMachine body) ⟨(93, idx, s), p', T'⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, pairTMachine, moveHead]; rfl
  rw [e89, e91, e92, e93]

theorem qp_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(94, idx, s), p, T⟩
      = ⟨(94, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(94, idx, s), p, T⟩ = ⟨(96, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

end Steps3

/-! ### Scan run-invariants -/

theorem qp_skipBs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipB hk.1 hk.2]
    rfl

theorem qp_skipB1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipB1 (h k (by omega))]
    rfl

theorem qp_skipA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipA1 (h k (by omega))]
    rfl

theorem qp_skiphA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(33, idx, s), q, T⟩
      = ⟨(33, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphA1 (h k (by omega))]
    rfl

theorem qp_skipC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(37, idx, s), q, T⟩
      = ⟨(37, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipC1 (h k (by omega))]
    rfl

theorem qp_skipC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(39, idx, s), q, T⟩
      = ⟨(39, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipC2 (h k (by omega))]
    rfl

theorem qp_skiphC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(53, idx, s), q, T⟩
      = ⟨(53, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphC1 (h k (by omega))]
    rfl

theorem qp_skiphC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphC2 (h k (by omega))]
    rfl

theorem qp_skipJr1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipJr1 (h k (by omega))]
    rfl

theorem qp_skipJr2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(61, idx, s), q, T⟩
      = ⟨(61, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipJr2 (h k (by omega))]
    rfl

theorem qp_skipJr3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(63, idx, s), q, T⟩
      = ⟨(63, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipJr3 (h k (by omega))]
    rfl

theorem qp_skiphJ1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(75, idx, s), q, T⟩
      = ⟨(75, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphJ1 (h k (by omega))]
    rfl

theorem qp_skiphJ2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(77, idx, s), q, T⟩
      = ⟨(77, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphJ2 (h k (by omega))]
    rfl

theorem qp_skiphJ3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skiphJ3 (h k (by omega))]
    rfl

theorem qp_skipi1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(83, idx, s), q, T⟩
      = ⟨(83, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipi1 (h k (by omega))]
    rfl

theorem qp_skipi2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipi2 (h k (by omega))]
    rfl

theorem qp_skipi3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(87, idx, s), q, T⟩
      = ⟨(87, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipi3 (h k (by omega))]
    rfl

theorem qp_scanB2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanB2 (h k (by omega))]
    rfl

theorem qp_scanB3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanB3 (h k (by omega))]
    rfl

theorem qp_scanB4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanB4 (h k (by omega))]
    rfl

theorem qp_scanB5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanB5 (h k (by omega))]
    rfl

theorem qp_scanA2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanA2 (h k (by omega))]
    rfl

theorem qp_scanA3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanA3 (h k (by omega))]
    rfl

theorem qp_scanA4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanA4 (h k (by omega))]
    rfl

theorem qp_scanA5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanA5 (h k (by omega))]
    rfl

theorem qp_scanC3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanC3 (h k (by omega))]
    rfl

theorem qp_scanC4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanC4 (h k (by omega))]
    rfl

theorem qp_scanC5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(47, idx, s), q, T⟩
      = ⟨(47, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanC5 (h k (by omega))]
    rfl

theorem qp_scanJ4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanJ4 (h k (by omega))]
    rfl

theorem qp_scanJ5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (pairTMachine body) (2 * k) ⟨(69, idx, s), q, T⟩
      = ⟨(69, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_scanJ5 (h k (by omega))]
    rfl

theorem qp_skipAms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipAm hk.1 hk.2]
    rfl

theorem qp_skipCms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipCm hk.1 hk.2]
    rfl

theorem qp_skipJms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * k) ⟨(65, idx, s), q, T⟩
      = ⟨(65, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipJm hk.1 hk.2]
    rfl

theorem qp_walkIs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(89, idx, s), q, T⟩
      = ⟨(89, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_walkI (h k (by omega))]
    rfl


/-! ### The ten prefix-skip pairs -/

section StepsW
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qp_skipWf (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(97, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(117, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWb (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(99, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWb (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(119, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWsa (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(101, idx, s), p, T⟩ = ⟨(101, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(101, idx, s), p, T⟩
      = ⟨(102, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWsa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(101, idx, s), p, T⟩ = ⟨(121, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(101, idx, s), p, T⟩
      = ⟨(102, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWha (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(103, idx, s), p, T⟩ = ⟨(103, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(103, idx, s), p, T⟩
      = ⟨(104, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWha (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(103, idx, s), p, T⟩ = ⟨(123, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(103, idx, s), p, T⟩
      = ⟨(104, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWsc (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(105, idx, s), p, T⟩ = ⟨(105, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(105, idx, s), p, T⟩
      = ⟨(106, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWsc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(105, idx, s), p, T⟩ = ⟨(125, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(105, idx, s), p, T⟩
      = ⟨(106, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWhc (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(107, idx, s), p, T⟩ = ⟨(107, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(107, idx, s), p, T⟩
      = ⟨(108, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWhc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(107, idx, s), p, T⟩ = ⟨(127, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(107, idx, s), p, T⟩
      = ⟨(108, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWsj (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(109, idx, s), p, T⟩ = ⟨(109, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(109, idx, s), p, T⟩
      = ⟨(110, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWsj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(109, idx, s), p, T⟩ = ⟨(129, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(109, idx, s), p, T⟩
      = ⟨(110, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWhj (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(111, idx, s), p, T⟩ = ⟨(111, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(111, idx, s), p, T⟩
      = ⟨(112, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWhj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(111, idx, s), p, T⟩ = ⟨(131, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(111, idx, s), p, T⟩
      = ⟨(112, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWi (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(113, idx, s), p, T⟩ = ⟨(113, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(113, idx, s), p, T⟩
      = ⟨(114, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWi (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(113, idx, s), p, T⟩ = ⟨(133, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(113, idx, s), p, T⟩
      = ⟨(114, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipWfin (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(115, idx, s), p, T⟩ = ⟨(115, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(115, idx, s), p, T⟩
      = ⟨(116, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossWfin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(115, idx, s), p, T⟩ = ⟨(135, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(115, idx, s), p, T⟩
      = ⟨(116, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

end StepsW

/-! ### Prefix-skip scan invariants -/

theorem qp_skipWfs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(97, idx, s), q, T⟩
      = ⟨(97, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWf (h k (by omega))]
    rfl

theorem qp_skipWbs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(99, idx, s), q, T⟩
      = ⟨(99, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWb (h k (by omega))]
    rfl

theorem qp_skipWsas (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(101, idx, s), q, T⟩
      = ⟨(101, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWsa (h k (by omega))]
    rfl

theorem qp_skipWhas (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(103, idx, s), q, T⟩
      = ⟨(103, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWha (h k (by omega))]
    rfl

theorem qp_skipWscs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(105, idx, s), q, T⟩
      = ⟨(105, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWsc (h k (by omega))]
    rfl

theorem qp_skipWhcs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(107, idx, s), q, T⟩
      = ⟨(107, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWhc (h k (by omega))]
    rfl

theorem qp_skipWsjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(109, idx, s), q, T⟩
      = ⟨(109, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWsj (h k (by omega))]
    rfl

theorem qp_skipWhjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(111, idx, s), q, T⟩
      = ⟨(111, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWhj (h k (by omega))]
    rfl

theorem qp_skipWis (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(113, idx, s), q, T⟩
      = ⟨(113, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWi (h k (by omega))]
    rfl

theorem qp_skipWfins (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(115, idx, s), q, T⟩
      = ⟨(115, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipWfin (h k (by omega))]
    rfl

/-! ### The prefixed heal walks -/

/-- The first-source heal (evolving `hlT`, two prefixes: grand bound, engine bound). -/
theorem qp_healAs (body : List L3Instr) (W P : List Bool) (G N a : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2) (idx : Fin (body.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ a) :
    run (pairTMachine body) (2 * i)
      ⟨(35, idx, s), 2 * G + 2 + 2 * N + 2, W ++ (P ++ (hlT a 0 ++ E))⟩
      = ⟨(35, idx, if i = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * i,
          W ++ (P ++ (hlT a i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (W ++ (P ++ (hlT a i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i) false
        = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i) from by omega]
      exact liftJ2 W P _ hW hP (hlE_pair_lo a i E (by omega))
    have h2 : (W ++ (P ++ (hlT a i ++ E))).getD (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 W P _ hW hP (hlE_pair_hi a i E (by omega))
    have hw : writeAt (W ++ (P ++ (hlT a i ++ E))) (2 * G + 2 + 2 * N + 2 + 2 * i + 1) true
        = W ++ (P ++ (hlT a (i + 1) ++ E)) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 W P _ (2 * G + 2) (2 * N + 2) (2 * i + 1) true hW hP
          (by rw [List.length_append, hlT_length a i (by omega)]; omega),
        hlT_heal a i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healA h1 h2, hw]
    rfl

/-- The second-source heal (evolving `hlT`, three prefixes). -/
theorem qp_healCs (body : List L3Instr) (W P Q : List Bool) (G N a c : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2) (hQ : Q.length = 2 * a + 2)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ c) :
    run (pairTMachine body) (2 * i)
      ⟨(57, idx, s), 2 * G + 2 + 2 * N + 2 + 2 * a + 2, W ++ (P ++ (Q ++ (hlT c 0 ++ E)))⟩
      = ⟨(57, idx, if i = 0 then s else true), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i,
          W ++ (P ++ (Q ++ (hlT c i ++ E)))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (W ++ (P ++ (Q ++ (hlT c i ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
      exact liftJ3 W P Q _ hW hP hQ (hlE_pair_lo c i E (by omega))
    have h2 : (W ++ (P ++ (Q ++ (hlT c i ++ E)))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 W P Q _ hW hP hQ (hlE_pair_hi c i E (by omega))
    have hw : writeAt (W ++ (P ++ (Q ++ (hlT c i ++ E))))
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) true
        = W ++ (P ++ (Q ++ (hlT c (i + 1) ++ E))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega,
        writeAt_append_right3 W P Q _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * i + 1) true
          hW hP hQ (by rw [List.length_append, hlT_length c i (by omega)]; omega),
        hlT_heal c i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healC h1 h2, hw]
    rfl

/-- The variable heal (evolving `jhT`, four prefixes). -/
theorem qp_healJs (body : List L3Instr) (W P Q R : List Bool) (G N a c k : ℕ)
    (E : List Bool) (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2)
    (hQ : Q.length = 2 * a + 2) (hR : R.length = 2 * c + 2) (hk : k ≤ N)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (pairTMachine body) (2 * i)
      ⟨(81, idx, s), 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2,
        W ++ (P ++ (Q ++ (R ++ (jhT N k 0 ++ E))))⟩
      = ⟨(81, idx, if i = 0 then s else true),
          2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i,
          W ++ (P ++ (Q ++ (R ++ (jhT N k i ++ E))))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (W ++ (P ++ (Q ++ (R ++ (jhT N k i ++ E))))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i))) from by omega]
      exact liftJ4 W P Q R _ hW hP hQ hR (jhE_pair_lo N k i E (by omega))
    have h2 : (W ++ (P ++ (Q ++ (R ++ (jhT N k i ++ E))))).getD
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1)))) from by omega]
      exact liftJ4 W P Q R _ hW hP hQ hR (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (W ++ (P ++ (Q ++ (R ++ (jhT N k i ++ E)))))
        (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) true
        = W ++ (P ++ (Q ++ (R ++ (jhT N k (i + 1) ++ E)))) := by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1)))) from by omega,
        writeAt_append_right4 W P Q R _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * c + 2)
          (2 * i + 1) true hW hP hQ hR
          (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healJ h1 h2, hw]
    rfl

/-- The bound heal (the finale, one prefix). -/
theorem qp_healBs (body : List L3Instr) (W : List Bool) (G v : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ)
    (hi : i ≤ v) :
    run (pairTMachine body) (2 * i) ⟨(94, idx, s), 2 * G + 2, W ++ (hlT v 0 ++ E)⟩
      = ⟨(94, idx, if i = 0 then s else true), 2 * G + 2 + 2 * i, W ++ (hlT v i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (W ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ W _ hW (hlE_pair_lo v i E (by omega))
    have h2 : (W ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ W _ hW (hlE_pair_hi v i E (by omega))
    have hw : writeAt (W ++ (hlT v i ++ E)) (2 * G + 2 + 2 * i + 1) true
        = W ++ (hlT v (i + 1) ++ E) := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
        writeAt_append_right W _ (2 * G + 2) (2 * i + 1) true hW
          (by rw [List.length_append, hlT_length v i (by omega)]; omega),
        hlT_heal v i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healB h1 h2, hw]
    rfl


/-! ### The second-level prefix pairs and the pad-crossing pairs -/

section StepsPT
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem qp_skipW2f (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(117, idx, s), p, T⟩ = ⟨(117, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(117, idx, s), p, T⟩
      = ⟨(118, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2f (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(117, idx, s), p, T⟩ = ⟨(0, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(117, idx, s), p, T⟩
      = ⟨(118, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2b (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(119, idx, s), p, T⟩ = ⟨(119, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(119, idx, s), p, T⟩
      = ⟨(120, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2b (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(119, idx, s), p, T⟩ = ⟨(3, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(119, idx, s), p, T⟩
      = ⟨(120, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2sa (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(121, idx, s), p, T⟩ = ⟨(121, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(121, idx, s), p, T⟩
      = ⟨(122, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2sa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(121, idx, s), p, T⟩ = ⟨(17, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(121, idx, s), p, T⟩
      = ⟨(122, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2ha (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(123, idx, s), p, T⟩ = ⟨(123, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(123, idx, s), p, T⟩
      = ⟨(124, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2ha (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(123, idx, s), p, T⟩ = ⟨(33, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(123, idx, s), p, T⟩
      = ⟨(124, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2sc (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(125, idx, s), p, T⟩ = ⟨(125, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(125, idx, s), p, T⟩
      = ⟨(126, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2sc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(125, idx, s), p, T⟩ = ⟨(37, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(125, idx, s), p, T⟩
      = ⟨(126, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2hc (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(127, idx, s), p, T⟩ = ⟨(127, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(127, idx, s), p, T⟩
      = ⟨(128, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2hc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(127, idx, s), p, T⟩ = ⟨(53, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(127, idx, s), p, T⟩
      = ⟨(128, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2sj (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(129, idx, s), p, T⟩ = ⟨(129, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(129, idx, s), p, T⟩
      = ⟨(130, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2sj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(129, idx, s), p, T⟩ = ⟨(59, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(129, idx, s), p, T⟩
      = ⟨(130, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2hj (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(131, idx, s), p, T⟩ = ⟨(131, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(131, idx, s), p, T⟩
      = ⟨(132, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(131, idx, s), p, T⟩ = ⟨(75, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(131, idx, s), p, T⟩
      = ⟨(132, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2i (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(133, idx, s), p, T⟩ = ⟨(133, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(133, idx, s), p, T⟩
      = ⟨(134, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(133, idx, s), p, T⟩ = ⟨(83, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(133, idx, s), p, T⟩
      = ⟨(134, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_skipW2fin (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(135, idx, s), p, T⟩ = ⟨(135, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(135, idx, s), p, T⟩
      = ⟨(136, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_crossW2fin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(135, idx, s), p, T⟩ = ⟨(94, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(135, idx, s), p, T⟩
      = ⟨(136, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPA1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(137, idx, s), p, T⟩ = ⟨(137, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(137, idx, s), p, T⟩
      = ⟨(138, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPA1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(137, idx, s), p, T⟩ = ⟨(19, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(137, idx, s), p, T⟩
      = ⟨(138, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPA1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(137, idx, s), p, T⟩ = ⟨(19, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(137, idx, s), p, T⟩
      = ⟨(138, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPA1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(137, idx, s), p, T⟩ = ⟨(19, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPA1_boundT h1
  · exact qp_padPA1_boundM h1 h2

theorem qp_padPhA1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(139, idx, s), p, T⟩ = ⟨(139, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(139, idx, s), p, T⟩
      = ⟨(140, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhA1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(139, idx, s), p, T⟩ = ⟨(35, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(139, idx, s), p, T⟩
      = ⟨(140, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhA1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(139, idx, s), p, T⟩ = ⟨(35, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(139, idx, s), p, T⟩
      = ⟨(140, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhA1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(139, idx, s), p, T⟩ = ⟨(35, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhA1_boundT h1
  · exact qp_padPhA1_boundM h1 h2

theorem qp_padPC1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(141, idx, s), p, T⟩ = ⟨(141, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(141, idx, s), p, T⟩
      = ⟨(142, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPC1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(141, idx, s), p, T⟩ = ⟨(39, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(141, idx, s), p, T⟩
      = ⟨(142, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPC1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(141, idx, s), p, T⟩ = ⟨(39, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(141, idx, s), p, T⟩
      = ⟨(142, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPC1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(141, idx, s), p, T⟩ = ⟨(39, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPC1_boundT h1
  · exact qp_padPC1_boundM h1 h2

theorem qp_padPC2_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(143, idx, s), p, T⟩ = ⟨(143, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(143, idx, s), p, T⟩
      = ⟨(144, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPC2_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(143, idx, s), p, T⟩ = ⟨(41, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(143, idx, s), p, T⟩
      = ⟨(144, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPC2_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(143, idx, s), p, T⟩ = ⟨(41, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(143, idx, s), p, T⟩
      = ⟨(144, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPC2_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(143, idx, s), p, T⟩ = ⟨(41, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPC2_boundT h1
  · exact qp_padPC2_boundM h1 h2

theorem qp_padPhC1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(145, idx, s), p, T⟩ = ⟨(145, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(145, idx, s), p, T⟩
      = ⟨(146, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhC1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(145, idx, s), p, T⟩ = ⟨(55, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(145, idx, s), p, T⟩
      = ⟨(146, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhC1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(145, idx, s), p, T⟩ = ⟨(55, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(145, idx, s), p, T⟩
      = ⟨(146, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhC1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(145, idx, s), p, T⟩ = ⟨(55, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhC1_boundT h1
  · exact qp_padPhC1_boundM h1 h2

theorem qp_padPhC2_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(147, idx, s), p, T⟩ = ⟨(147, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(147, idx, s), p, T⟩
      = ⟨(148, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhC2_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(147, idx, s), p, T⟩ = ⟨(57, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(147, idx, s), p, T⟩
      = ⟨(148, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhC2_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(147, idx, s), p, T⟩ = ⟨(57, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(147, idx, s), p, T⟩
      = ⟨(148, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhC2_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(147, idx, s), p, T⟩ = ⟨(57, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhC2_boundT h1
  · exact qp_padPhC2_boundM h1 h2

theorem qp_padPJ1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(149, idx, s), p, T⟩ = ⟨(149, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(149, idx, s), p, T⟩
      = ⟨(150, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(149, idx, s), p, T⟩ = ⟨(61, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(149, idx, s), p, T⟩
      = ⟨(150, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPJ1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(149, idx, s), p, T⟩ = ⟨(61, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(149, idx, s), p, T⟩
      = ⟨(150, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(149, idx, s), p, T⟩ = ⟨(61, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPJ1_boundT h1
  · exact qp_padPJ1_boundM h1 h2

theorem qp_padPJ2_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(151, idx, s), p, T⟩ = ⟨(151, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(151, idx, s), p, T⟩
      = ⟨(152, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ2_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(151, idx, s), p, T⟩ = ⟨(63, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(151, idx, s), p, T⟩
      = ⟨(152, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPJ2_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(151, idx, s), p, T⟩ = ⟨(63, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(151, idx, s), p, T⟩
      = ⟨(152, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ2_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(151, idx, s), p, T⟩ = ⟨(63, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPJ2_boundT h1
  · exact qp_padPJ2_boundM h1 h2

theorem qp_padPJ3_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(153, idx, s), p, T⟩ = ⟨(153, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(153, idx, s), p, T⟩
      = ⟨(154, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ3_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(153, idx, s), p, T⟩ = ⟨(65, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(153, idx, s), p, T⟩
      = ⟨(154, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPJ3_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(153, idx, s), p, T⟩ = ⟨(65, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(153, idx, s), p, T⟩
      = ⟨(154, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPJ3_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(153, idx, s), p, T⟩ = ⟨(65, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPJ3_boundT h1
  · exact qp_padPJ3_boundM h1 h2

theorem qp_padPhJ1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(155, idx, s), p, T⟩ = ⟨(155, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(155, idx, s), p, T⟩
      = ⟨(156, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(155, idx, s), p, T⟩ = ⟨(77, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(155, idx, s), p, T⟩
      = ⟨(156, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhJ1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(155, idx, s), p, T⟩ = ⟨(77, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(155, idx, s), p, T⟩
      = ⟨(156, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(155, idx, s), p, T⟩ = ⟨(77, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhJ1_boundT h1
  · exact qp_padPhJ1_boundM h1 h2

theorem qp_padPhJ2_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(157, idx, s), p, T⟩ = ⟨(157, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(157, idx, s), p, T⟩
      = ⟨(158, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ2_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(157, idx, s), p, T⟩ = ⟨(79, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(157, idx, s), p, T⟩
      = ⟨(158, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhJ2_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(157, idx, s), p, T⟩ = ⟨(79, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(157, idx, s), p, T⟩
      = ⟨(158, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ2_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(157, idx, s), p, T⟩ = ⟨(79, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhJ2_boundT h1
  · exact qp_padPhJ2_boundM h1 h2

theorem qp_padPhJ3_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(159, idx, s), p, T⟩ = ⟨(159, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(159, idx, s), p, T⟩
      = ⟨(160, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ3_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(159, idx, s), p, T⟩ = ⟨(81, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(159, idx, s), p, T⟩
      = ⟨(160, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPhJ3_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(159, idx, s), p, T⟩ = ⟨(81, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(159, idx, s), p, T⟩
      = ⟨(160, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPhJ3_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(159, idx, s), p, T⟩ = ⟨(81, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPhJ3_boundT h1
  · exact qp_padPhJ3_boundM h1 h2

theorem qp_padPI1_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(161, idx, s), p, T⟩ = ⟨(161, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(161, idx, s), p, T⟩
      = ⟨(162, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI1_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(161, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(161, idx, s), p, T⟩
      = ⟨(162, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPI1_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(161, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(161, idx, s), p, T⟩
      = ⟨(162, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI1_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(161, idx, s), p, T⟩ = ⟨(85, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPI1_boundT h1
  · exact qp_padPI1_boundM h1 h2

theorem qp_padPI2_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(163, idx, s), p, T⟩ = ⟨(163, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(163, idx, s), p, T⟩
      = ⟨(164, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI2_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(163, idx, s), p, T⟩ = ⟨(87, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(163, idx, s), p, T⟩
      = ⟨(164, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPI2_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(163, idx, s), p, T⟩ = ⟨(87, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(163, idx, s), p, T⟩
      = ⟨(164, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI2_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(163, idx, s), p, T⟩ = ⟨(87, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPI2_boundT h1
  · exact qp_padPI2_boundM h1 h2

theorem qp_padPI3_pad (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run (pairTMachine body) 2 ⟨(165, idx, s), p, T⟩ = ⟨(165, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(165, idx, s), p, T⟩
      = ⟨(166, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI3_boundT (h1 : T.getD p false = true) :
    run (pairTMachine body) 2 ⟨(165, idx, s), p, T⟩ = ⟨(89, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(165, idx, s), p, T⟩
      = ⟨(166, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, pairTMachine, moveHead]; rfl

theorem qp_padPI3_boundM (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (pairTMachine body) 2 ⟨(165, idx, s), p, T⟩ = ⟨(89, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (pairTMachine body) ⟨(165, idx, s), p, T⟩
      = ⟨(166, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, pairTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, pairTMachine, moveHead, h2]

theorem qp_padPI3_bound
    (h : T.getD p false = true ∨ (T.getD p false = false ∧ T.getD (p + 1) false = true)) :
    run (pairTMachine body) 2 ⟨(165, idx, s), p, T⟩ = ⟨(89, idx, false), p, T⟩ := by
  rcases h with h1 | ⟨h1, h2⟩
  · exact qp_padPI3_boundT h1
  · exact qp_padPI3_boundM h1 h2

end StepsPT

theorem qp_skipW2fs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(117, idx, s), q, T⟩
      = ⟨(117, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2f (h k (by omega))]
    rfl

theorem qp_skipW2bs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(119, idx, s), q, T⟩
      = ⟨(119, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2b (h k (by omega))]
    rfl

theorem qp_skipW2sas (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(121, idx, s), q, T⟩
      = ⟨(121, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2sa (h k (by omega))]
    rfl

theorem qp_skipW2has (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(123, idx, s), q, T⟩
      = ⟨(123, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2ha (h k (by omega))]
    rfl

theorem qp_skipW2scs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(125, idx, s), q, T⟩
      = ⟨(125, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2sc (h k (by omega))]
    rfl

theorem qp_skipW2hcs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(127, idx, s), q, T⟩
      = ⟨(127, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2hc (h k (by omega))]
    rfl

theorem qp_skipW2sjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(129, idx, s), q, T⟩
      = ⟨(129, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2sj (h k (by omega))]
    rfl

theorem qp_skipW2hjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(131, idx, s), q, T⟩
      = ⟨(131, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2hj (h k (by omega))]
    rfl

theorem qp_skipW2is (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(133, idx, s), q, T⟩
      = ⟨(133, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2i (h k (by omega))]
    rfl

theorem qp_skipW2fins (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (pairTMachine body) (2 * k) ⟨(135, idx, s), q, T⟩
      = ⟨(135, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_skipW2fin (h k (by omega))]
    rfl

theorem qp_padPA1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(137, idx, s), q, T⟩
      = ⟨(137, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPA1_pad hm.1 hm.2]
    rfl

theorem qp_padPhA1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(139, idx, s), q, T⟩
      = ⟨(139, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhA1_pad hm.1 hm.2]
    rfl

theorem qp_padPC1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(141, idx, s), q, T⟩
      = ⟨(141, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPC1_pad hm.1 hm.2]
    rfl

theorem qp_padPC2s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(143, idx, s), q, T⟩
      = ⟨(143, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPC2_pad hm.1 hm.2]
    rfl

theorem qp_padPhC1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(145, idx, s), q, T⟩
      = ⟨(145, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhC1_pad hm.1 hm.2]
    rfl

theorem qp_padPhC2s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(147, idx, s), q, T⟩
      = ⟨(147, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhC2_pad hm.1 hm.2]
    rfl

theorem qp_padPJ1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(149, idx, s), q, T⟩
      = ⟨(149, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPJ1_pad hm.1 hm.2]
    rfl

theorem qp_padPJ2s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(151, idx, s), q, T⟩
      = ⟨(151, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPJ2_pad hm.1 hm.2]
    rfl

theorem qp_padPJ3s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(153, idx, s), q, T⟩
      = ⟨(153, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPJ3_pad hm.1 hm.2]
    rfl

theorem qp_padPhJ1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(155, idx, s), q, T⟩
      = ⟨(155, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhJ1_pad hm.1 hm.2]
    rfl

theorem qp_padPhJ2s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(157, idx, s), q, T⟩
      = ⟨(157, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhJ2_pad hm.1 hm.2]
    rfl

theorem qp_padPhJ3s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(159, idx, s), q, T⟩
      = ⟨(159, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPhJ3_pad hm.1 hm.2]
    rfl

theorem qp_padPI1s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(161, idx, s), q, T⟩
      = ⟨(161, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPI1_pad hm.1 hm.2]
    rfl

theorem qp_padPI2s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(163, idx, s), q, T⟩
      = ⟨(163, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPI2_pad hm.1 hm.2]
    rfl

theorem qp_padPI3s (body : List L3Instr) (T : List Bool) (q m : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run (pairTMachine body) (2 * m) ⟨(165, idx, s), q, T⟩
      = ⟨(165, idx, if m = 0 then s else false), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h m (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), qp_padPI3_pad hm.1 hm.2]
    rfl


/-! ## The six-region lift layer -/

theorem liftJ5 (A B C D E X : List Bool) {qa qb qc qd qe p : ℕ} (ha : A.length = qa)
    (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd) (he : E.length = qe)
    {w : Bool} (h : X.getD p false = w) :
    (A ++ (B ++ (C ++ (D ++ (E ++ X))))).getD (qa + (qb + (qc + (qd + (qe + p))))) false
      = w := by
  exact liftJ A _ ha (liftJ4 B C D E X hb hc hd he h)

theorem writeAt_append_right5 (A B C D E X : List Bool) (qa qb qc qd qe p : ℕ) (w : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd)
    (he : E.length = qe) (hp : p < X.length) :
    writeAt (A ++ (B ++ (C ++ (D ++ (E ++ X))))) (qa + (qb + (qc + (qd + (qe + p))))) w
      = A ++ (B ++ (C ++ (D ++ (E ++ writeAt X p w)))) := by
  rw [writeAt_append_right A _ qa (qb + (qc + (qd + (qe + p)))) w ha
      (by simp only [List.length_append]; omega),
    writeAt_append_right4 B C D E X qb qc qd qe p w hb hc hd he hp]

theorem preD6_data_eq (A B C D E F out : List Bool) (q i : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length + F.length = q)
    (h : i < out.length) :
    (A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD out)))))).getD (q + 2 * i) false
      = (A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD out)))))).getD (q + 2 * i + 1) false := by
  have := preD_data_eq (A ++ (B ++ (C ++ (D ++ (E ++ F))))) out q i
    (by simp only [List.length_append]; omega) h
  simpa [List.append_assoc] using this

theorem preD6_mark_lo (A B C D E F out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length + F.length = q) :
    (A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD out)))))).getD (q + 2 * out.length) false
      = false := by
  have := preD_mark_lo (A ++ (B ++ (C ++ (D ++ (E ++ F))))) out q
    (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem preD6_mark_hi (A B C D E F out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length + F.length = q) :
    (A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD out)))))).getD
      (q + 2 * out.length + 1) false = true := by
  have := preD_mark_hi (A ++ (B ++ (C ++ (D ++ (E ++ F))))) out q
    (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem writes_snoc6 (A B C D E F out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length + F.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD out))))))
        (q + 2 * out.length) b) (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false)
        (q + 2 * out.length + 3) true
      = A ++ (B ++ (C ++ (D ++ (E ++ (F ++ encodeD (out ++ [b])))))) := by
  have h := writes_snoc (A ++ (B ++ (C ++ (D ++ (E ++ F))))) out q
    (by simp only [List.length_append]; omega) b
  simpa [List.append_assoc] using h

theorem W4_append_right5 (A B C D E X : List Bool) (qa qb qc qd qe p : ℕ)
    (b1 b2 b3 b4 : Bool) (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc)
    (hd : D.length = qd) (he : E.length = qe) (hp : p + 3 < X.length) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ (D ++ (E ++ X)))))
        (qa + (qb + (qc + (qd + (qe + p))))) b1)
        (qa + (qb + (qc + (qd + (qe + p)))) + 1) b2)
        (qa + (qb + (qc + (qd + (qe + p)))) + 2) b3)
        (qa + (qb + (qc + (qd + (qe + p)))) + 3) b4
      = A ++ (B ++ (C ++ (D ++ (E ++ writeAt (writeAt (writeAt (writeAt X p b1)
          (p + 1) b2) (p + 2) b3) (p + 3) b4)))) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  have hl2 : (writeAt (writeAt X p b1) (p + 1) b2).length = X.length := by
    rw [writeAt_of_lt b2 (by omega), List.length_set, hl1]
  have hl3 : (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3).length
      = X.length := by
    rw [writeAt_of_lt b3 (by omega), List.length_set, hl2]
  rw [writeAt_append_right5 A B C D E X qa qb qc qd qe p b1 ha hb hc hd he (by omega),
    show qa + (qb + (qc + (qd + (qe + p)))) + 1
      = qa + (qb + (qc + (qd + (qe + (p + 1))))) from by omega,
    writeAt_append_right5 A B C D E _ qa qb qc qd qe (p + 1) b2 ha hb hc hd he
      (by rw [hl1]; omega),
    show qa + (qb + (qc + (qd + (qe + p)))) + 2
      = qa + (qb + (qc + (qd + (qe + (p + 2))))) from by omega,
    writeAt_append_right5 A B C D E _ qa qb qc qd qe (p + 2) b3 ha hb hc hd he
      (by rw [hl2]; omega),
    show qa + (qb + (qc + (qd + (qe + p)))) + 3
      = qa + (qb + (qc + (qd + (qe + (p + 3))))) from by omega,
    writeAt_append_right5 A B C D E _ qa qb qc qd qe (p + 3) b4 ha hb hc hd he
      (by rw [hl3]; omega)]

/-! ## The `jhT` heal walks on the six-region layout -/

/-- Source-1 heal (phase 35, evolving `jhT`, three prefixes). -/
theorem qp_healT1s (body : List L3Instr) (W1 W2 R : List Bool) (G1 G2 CB C1 t : ℕ)
    (E : List Bool) (h1 : W1.length = 2 * G1 + 2) (h2 : W2.length = 2 * G2 + 2)
    (hR : R.length = 2 * CB + 2) (ht : t ≤ C1) (idx : Fin (body.length + 1)) (s : Bool)
    (i : ℕ) (hi : i ≤ t) :
    run (pairTMachine body) (2 * i)
      ⟨(35, idx, s), 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2,
        W1 ++ (W2 ++ (R ++ (jhT C1 t 0 ++ E)))⟩
      = ⟨(35, idx, if i = 0 then s else true), 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i,
          W1 ++ (W2 ++ (R ++ (jhT C1 t i ++ E)))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e1 : (W1 ++ (W2 ++ (R ++ (jhT C1 t i ++ E)))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i) false = true := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega]
      exact liftJ3 W1 W2 R _ h1 h2 hR (jhE_pair_lo C1 t i E (by omega))
    have e2 : (W1 ++ (W2 ++ (R ++ (jhT C1 t i ++ E)))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 W1 W2 R _ h1 h2 hR (jhE_pair_hi C1 t i E (by omega))
    have hw : writeAt (W1 ++ (W2 ++ (R ++ (jhT C1 t i ++ E))))
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1) true
        = W1 ++ (W2 ++ (R ++ (jhT C1 t (i + 1) ++ E))) := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 1))) from by omega,
        writeAt_append_right3 W1 W2 R _ (2 * G1 + 2) (2 * G2 + 2) (2 * CB + 2)
          (2 * i + 1) true h1 h2 hR
          (by rw [List.length_append, jhT_length C1 t i (by omega) (by omega)]; omega),
        jhT_heal C1 t i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healA e1 e2, hw]
    rfl

/-- Source-2 heal (phase 57, four prefixes). -/
theorem qp_healT2s (body : List L3Instr) (W1 W2 R S : List Bool) (G1 G2 CB C1 C2 j2 : ℕ)
    (E : List Bool) (h1 : W1.length = 2 * G1 + 2) (h2 : W2.length = 2 * G2 + 2)
    (hR : R.length = 2 * CB + 2) (hS : S.length = 2 * C1 + 2) (hj2 : j2 ≤ C2)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ j2) :
    run (pairTMachine body) (2 * i)
      ⟨(57, idx, s), 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2,
        W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 0 ++ E))))⟩
      = ⟨(57, idx, if i = 0 then s else true),
          2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i,
          W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 i ++ E))))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e1 : (W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 i ++ E))))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i) false = true := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega]
      exact liftJ4 W1 W2 R S _ h1 h2 hR hS (jhE_pair_lo C2 j2 i E (by omega))
    have e2 : (W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 i ++ E))))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i + 1))))
          from by omega]
      exact liftJ4 W1 W2 R S _ h1 h2 hR hS (jhE_pair_hi C2 j2 i E (by omega))
    have hw : writeAt (W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 i ++ E)))))
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1) true
        = W1 ++ (W2 ++ (R ++ (S ++ (jhT C2 j2 (i + 1) ++ E)))) := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i + 1))))
          from by omega,
        writeAt_append_right4 W1 W2 R S _ (2 * G1 + 2) (2 * G2 + 2) (2 * CB + 2)
          (2 * C1 + 2) (2 * i + 1) true h1 h2 hR hS
          (by rw [List.length_append, jhT_length C2 j2 i (by omega) (by omega)]; omega),
        jhT_heal C2 j2 i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healC e1 e2, hw]
    rfl

/-- Live heal (phase 81, five prefixes). -/
theorem qp_healJ5s (body : List L3Instr) (W1 W2 R S U : List Bool)
    (G1 G2 CB C1 C2 NV k : ℕ) (E : List Bool) (h1 : W1.length = 2 * G1 + 2)
    (h2 : W2.length = 2 * G2 + 2) (hR : R.length = 2 * CB + 2) (hS : S.length = 2 * C1 + 2)
    (hU : U.length = 2 * C2 + 2) (hk : k ≤ NV) (idx : Fin (body.length + 1)) (s : Bool)
    (i : ℕ) (hi : i ≤ k) :
    run (pairTMachine body) (2 * i)
      ⟨(81, idx, s), 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2,
        W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k 0 ++ E)))))⟩
      = ⟨(81, idx, if i = 0 then s else true),
          2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i,
          W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k i ++ E)))))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e1 : (W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k i ++ E)))))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i) false
        = true := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * i))))
          from by omega]
      exact liftJ5 W1 W2 R S U _ h1 h2 hR hS hU (jhE_pair_lo NV k i E (by omega))
    have e2 : (W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k i ++ E)))))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * C2 + 2 + (2 * i + 1))))) from by omega]
      exact liftJ5 W1 W2 R S U _ h1 h2 hR hS hU (jhE_pair_hi NV k i E (by omega))
    have hw : writeAt (W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k i ++ E))))))
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1) true
        = W1 ++ (W2 ++ (R ++ (S ++ (U ++ (jhT NV k (i + 1) ++ E))))) := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * C2 + 2 + (2 * i + 1))))) from by omega,
        writeAt_append_right5 W1 W2 R S U _ (2 * G1 + 2) (2 * G2 + 2) (2 * CB + 2)
          (2 * C1 + 2) (2 * C2 + 2) (2 * i + 1) true h1 h2 hR hS hU
          (by rw [List.length_append, jhT_length NV k i (by omega) (by omega)]; omega),
        jhT_heal NV k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healJ e1 e2, hw]
    rfl

/-- The padded-bound heal (the finale, phase 94, two prefixes, evolving `jhT`). -/
theorem qp_healBJs (body : List L3Instr) (W1 W2 : List Bool) (G1 G2 CB j : ℕ)
    (E : List Bool) (h1 : W1.length = 2 * G1 + 2) (h2 : W2.length = 2 * G2 + 2)
    (hj : j ≤ CB) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ j) :
    run (pairTMachine body) (2 * i)
      ⟨(94, idx, s), 2 * G1 + 2 + 2 * G2 + 2, W1 ++ (W2 ++ (jhT CB j 0 ++ E))⟩
      = ⟨(94, idx, if i = 0 then s else true), 2 * G1 + 2 + 2 * G2 + 2 + 2 * i,
          W1 ++ (W2 ++ (jhT CB j i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e1 : (W1 ++ (W2 ++ (jhT CB j i ++ E))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * i) false = true := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      exact liftJ2 W1 W2 _ h1 h2 (jhE_pair_lo CB j i E (by omega))
    have e2 : (W1 ++ (W2 ++ (jhT CB j i ++ E))).getD
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1) false = false := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1 = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 W1 W2 _ h1 h2 (jhE_pair_hi CB j i E (by omega))
    have hw : writeAt (W1 ++ (W2 ++ (jhT CB j i ++ E)))
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1) true
        = W1 ++ (W2 ++ (jhT CB j (i + 1) ++ E)) := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1 = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 W1 W2 _ (2 * G1 + 2) (2 * G2 + 2) (2 * i + 1) true h1 h2
          (by rw [List.length_append, jhT_length CB j i (by omega) (by omega)]; omega),
        jhT_heal CB j i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      qp_healB e1 e2, hw]
    rfl
/-! ## The instruction lemmas

Round-`k` layout:
`cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k+1) ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
++ encodeD OUT)))))` — the grand prefix at `[0, 2G1+2)`, the row prefix at
`[2G1+2, 2G1+2G2+4)`, then the engine's padded regions (find-marked bound, the two source
mirrors, the live variable), output at `2G1+2G2+2CB+2C1+2C2+2NV+12`.  Every boundary-event
scan absorbs the padding as equal `(false,false)` pairs, so the leg counts pick up the
capacities; the clocks stay value-independent in `j`. -/

section Instr
variable {G1 g1 G2 g2 : ℕ}

/-- **An append instruction**, doubly prefixed on the padded layout: dispatch, skip both
prefixes, skip the find-marked padded bound, four boundary-event scans absorbing every pad,
snoc, advance. -/
theorem qp_instr_bit (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spJo = .bit b)
    (hg1 : g1 ≤ G1) (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB)
    (ht1 : t1 ≤ C1) (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool)
    (s : Bool) :
    run (pairTMachine body)
      (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 19)
      ⟨(2, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ [b]))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have hq6 : (cntT G1 g1).length + (cntT G2 g2).length + (jsT CB j (k + 1)).length
      + (jT C1 t1).length + (jT C2 t2).length + (jT NV k).length
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 := by
    rw [hW1, hW2, hB, hS1, jT_length C2 t2 ht2, jT_length NV k hkV]; omega
  have b0 := qp_dispatch_bit (s := s) (p := 0)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) h hp
  have b0a := qp_skipWbs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) 0 G1 idx s
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at b0a
  have b0b := qp_crossWb (body := body) (idx := idx) (s := if G1 = 0 then s else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have b0c := qp_skipW2bs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have b0d := qp_crossW2b (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have b1 := qp_skipB1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have b2 := qp_crossB1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have b3 := qp_scanB2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) ((CB - j) + t1) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (CB - j) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
            (by omega) hj (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
            (by omega) hj (by omega) (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i) false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * (i - (CB - j))))
              from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ (2 * (i - (CB - j))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1) false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * (i - (CB - j)) + 1)))
              from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ (2 * (i - (CB - j)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * ((CB - j) + t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 from by omega] at b3
  have b4 := qp_crossSB2 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) false ((CB - j) + t1))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have b5 := qp_scanB3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) ((C1 - t1) + t2) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (C1 - t1) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
              from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
            (by omega) ht1 (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1) false
            = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
              from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
            (by omega) ht1 (by omega) (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i) false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + 2 * (i - (C1 - t1))))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ (2 * (i - (C1 - t1))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1) false
            = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * (i - (C1 - t1)) + 1)))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ (2 * (i - (C1 - t1)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * ((C1 - t1) + t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 from by omega] at b5
  have b6 := qp_crossSB3 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) false ((C1 - t1) + t2))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have b7 := qp_scanB4s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) ((C2 - t2) + k)
    idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (C2 - t2) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i) false
            = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i)
            (by omega) ht2 (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i + 1)
            false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i + 1) (by omega) ht2 (by omega)
              (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i) false
            = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + 2 * (i - (C2 - t2)))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_data NV k 0 _ (2 * (i - (C2 - t2))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i + 1)
            false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * (i - (C2 - t2)) + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_data NV k 0 _ (2 * (i - (C2 - t2)) + 1) (by omega) (by omega) (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * ((C2 - t2) + k)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
      from by omega] at b7
  have b8 := qp_crossSB4 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) false
      ((C2 - t2) + k))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
          (jsE_m_lo NV k 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
          (jsE_m_hi NV k 0 _ (by omega)))
  have b9 := qp_scanB5s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2)
    ((NV - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (NV - k) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i) (by omega) hkV (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i + 1) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i + 1) (by omega) hkV (by omega)
              (by omega))
        rw [e1, e2]
      · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
              + 2 + 2 * i
            = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
                + 2 * (i - (NV - k)) from by omega]
        exact preD6_data_eq (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
          (jT C2 t2) (jT NV k) OUT
          (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) (i - (NV - k)) hq6
          (by omega))
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
        + 2 * ((NV - k) + OUT.length)
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * OUT.length
      from by omega] at b9
  have b10 := qp_detectB5 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2) false
      ((NV - k) + OUT.length))
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * OUT.length)
    (preD6_mark_lo (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) (jT C2 t2)
      (jT NV k) OUT (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6)
    (preD6_mark_hi (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) (jT C2 t2)
      (jT NV k) OUT (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6)
  have b11 := qp_four_bit (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * OUT.length)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) (by omega)
  rw [hp] at b11
  simp only [L3Instr.bitVal] at b11
  rw [writes_snoc6 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) (jT C2 t2)
    (jT NV k) OUT (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6 b] at b11
  rw [show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 19
      = 1 + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * ((CB - j) + t1) + (2
          + (2 * ((C1 - t1) + t2) + (2 + (2 * ((C2 - t2) + k) + (2
          + (2 * ((NV - k) + OUT.length) + (2 + 4))))))))))))))
      from by omega,
    run_add, b0, run_add, b0a, run_add, b0b, run_add, b0c, run_add, b0d, run_add, b1,
    run_add, b2, run_add, b3, run_add, b4, run_add, b5, run_add, b6, run_add, b7,
    run_add, b8, run_add, b9, run_add, b10, b11]

end Instr

/-! ### The open splice-A instruction on the padded layout -/

section InstrA
variable {G1 g1 G2 g2 : ℕ}

/-- One splice-A sub-round on the padded layout: skip both prefixes, seek through the
find-marked bound and its pad, mark the first source mirror's pair `i`, seek out through the
second source, the live variable and every pad, emit a doubled `true`. -/
theorem qp_spa_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k i : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (hi : i < t1) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body)
      (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i + 20)
      ⟨(101, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))⟩
      = ⟨(101, idx, false), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
          ++ (jsT C1 t1 (i + 1) ++ (jT C2 t2 ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jsT C1 t1 (i + 1)).length = 2 * C1 + 2 := jsT_length C1 t1 (i + 1) hi ht1
  have hq6 : (cntT G1 g1).length + (cntT G2 g2).length + (jsT CB j (k + 1)).length
      + (jsT C1 t1 (i + 1)).length + (jT C2 t2).length + (jT NV k).length
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 := by
    rw [hW1, hW2, hB, hS1, jT_length C2 t2 ht2, jT_length NV k hkV]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s0a := qp_skipWsas body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))) 0 G1 idx s
    (fun i' hi' => by simpa using cntE_lo G1 g1 _ i' hg1 hi')
  simp only [Nat.zero_add] at s0a
  have s0b := qp_crossWsa (body := body) (idx := idx) (s := if G1 = 0 then s else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have s0c := qp_skipW2sas body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * i' = 2 * G1 + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i' hg2 hi'))
  have s0d := qp_crossW2sa (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have s1 := qp_skipA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i')
          from by omega]
      rcases Nat.lt_or_ge i' (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i' hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i') (by omega) (by omega) (by omega)))
  have s2 := qp_crossA1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have s2b := qp_padPA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i')) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i')
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i' + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i' + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at s2b
  have s2c := qp_padPA1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (Or.inl (by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exact liftJ3 _ _ _ _ hW1 hW2 hB
          (jsE_data C1 t1 i _ 0 (by omega) (by omega) (by omega))
      · exact liftJ3 _ _ _ _ hW1 hW2 hB (by
          have := jsE_mark_lo C1 t1 i (jT C2 t2 ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate i true))) 0 h0
          simpa using this)))
  have s3 := qp_skipAms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i')) from by omega]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_mark_lo C1 t1 i _ i' hi'), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i' + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_mark_hi C1 t1 i _ i' hi')⟩)
  have s4 := qp_markA (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB
          (jsE_data C1 t1 i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB
          (jsE_data C1 t1 i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 i
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1) false
      = cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
          ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))) := by
    rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1
        = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 1))) from by omega,
      writeAt_append_right3 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) _ (2 * G1 + 2)
        (2 * G2 + 2) (2 * CB + 2) (2 * i + 1) false hW1 hW2 hB
        (by rw [List.length_append, jsT_length C1 t1 i (by omega) ht1]; omega),
      jsT_mark C1 t1 i _ hi ht1]
  rw [hw] at s4
  have s5 := qp_scanA2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2) (t1 - (i + 1)) idx true
    (fun i' hi' => by
      have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
          ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2 + 2 * i'
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 2 + 2 * i')))
            from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB
          (jsE_data C1 t1 (i + 1) _ (2 * i + 2 + 2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
          ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2 + 2 * i' + 1) false
          = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 2 + 2 * i' + 1)))
            from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB
          (jsE_data C1 t1 (i + 1) _ (2 * i + 2 + 2 * i' + 1) (by omega) (by omega)
            (by omega))
      rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2 + 2 * (t1 - (i + 1))
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 from by omega] at s5
  have s6 := qp_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 2) true (t1 - (i + 1)))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 (i + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 (i + 1) _ (by omega)))
  have s7 := qp_scanA3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) ((C1 - t1) + t2) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (C1 - t1) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i') false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i')))
              from by omega]
          exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 (i + 1) _ (2 * t1 + 2 + 2 * i')
            hi ht1 (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1) false
            = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i' + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_pad C1 t1 (i + 1) _ (2 * t1 + 2 + 2 * i' + 1) hi ht1 (by omega)
              (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i') false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + 2 * (i' - (C1 - t1))))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ (2 * (i' - (C1 - t1))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1) false
            = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * (i' - (C1 - t1)) + 1)))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ (2 * (i' - (C1 - t1)) + 1) (by omega) (by omega)
              (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * ((C1 - t1) + t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 from by omega] at s7
  have s8 := qp_crossSA3 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) false ((C1 - t1) + t2))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have s9 := qp_scanA4s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) ((C2 - t2) + k)
    idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (C2 - t2) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i')
            false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i')))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i')
            (by omega) ht2 (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i' + 1)
            false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i' + 1)))) from by omega, ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i' + 1) (by omega) ht2 (by omega)
              (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i')
            false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + 2 * (i' - (C2 - t2)))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_data NV k 0 _ (2 * (i' - (C2 - t2))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i' + 1)
            false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * (i' - (C2 - t2)) + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_data NV k 0 _ (2 * (i' - (C2 - t2)) + 1) (by omega) (by omega)
              (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * ((C2 - t2) + k)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
      from by omega] at s9
  have s10 := qp_crossSA4 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) false
      ((C2 - t2) + k))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
          (jsE_m_lo NV k 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
          (jsE_m_hi NV k 0 _ (by omega)))
  have s11 := qp_scanA5s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2)
    ((NV - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (NV - k) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i') false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i'))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i') (by omega) hkV (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i' + 1) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i' + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 (jT_length C2 t2 ht2)
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i' + 1) (by omega) hkV (by omega)
              (by omega))
        rw [e1, e2]
      · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
              + 2 + 2 * i'
            = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
                + 2 * (i' - (NV - k)) from by omega]
        exact preD6_data_eq (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1))
          (jsT C1 t1 (i + 1)) (jT C2 t2) (jT NV k) (OUT ++ List.replicate i true)
          (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) (i' - (NV - k)) hq6
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
        + 2 * ((NV - k) + (OUT.length + i))
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i)
      from by omega] at s11
  have hm1 := preD6_mark_lo (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1))
    (jsT C1 t1 (i + 1)) (jT C2 t2) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  have hm2 := preD6_mark_hi (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1))
    (jsT C1 t1 (i + 1)) (jT C2 t2) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  rw [hlen] at hm1 hm2
  have s12 := qp_detectA5 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2) false
      ((NV - k) + (OUT.length + i)))
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
      + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc6 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1))
    (jsT C1 t1 (i + 1)) (jT C2 t2) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := qp_four_TA (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i))
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 (i + 1)
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
  rw [hsn] at s13
  rw [show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i
        + 20
      = 2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * i + (2
          + (2 * (t1 - (i + 1)) + (2 + (2 * ((C1 - t1) + t2) + (2 + (2 * ((C2 - t2) + k)
          + (2 + (2 * ((NV - k) + (OUT.length + i)) + (2 + 4)))))))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s0c, run_add, s0d, run_add, s1, run_add, s2,
    run_add, s2b, run_add, s2c, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem qp_spa_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (r : ℕ) (hr : r ≤ t1)
    (s : Bool) :
    run (pairTMachine body)
      (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
        + 2 * OUT.length + 20) r)
      ⟨(101, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 0
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(101, idx, if r = 0 then s else false), 0, cntT G1 g1 ++ (cntT G2 g2
          ++ (jsT CB j (k + 1) ++ (jsT C1 t1 r ++ (jT C2 t2 ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate r true))))))⟩ := by
  induction r with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ r ih =>
    rw [show lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 20) (r + 1)
        = lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
            + 2 * OUT.length + 20) r
            + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 20
              + 2 * r) from rfl,
      show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 20
          + 2 * r
        = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * r
          + 20 from by omega,
      run_add, ih (by omega),
      qp_spa_round body idx hg1 hg2 CB C1 C2 NV j t1 t2 k r hj ht1 ht2 hk hkV (by omega)
        OUT _,
      if_neg (by omega)]

end InstrA

/-- The padded splice-A instruction clock: the sub-rounds plus the twin seek and heal
passes; `j`-independent (the bound skip and its pad-crossing always sum to `2CB+2`). -/
def pairTaCost (G1 G2 CB C1 C2 NV t1 L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 20) t1
    + ((2 * G1 + 2 * G2 + 2 * CB + 2 * t1 + 10) + (2 * G1 + 2 * G2 + 2 * CB + 2 * t1 + 10)))

section InstrA2
variable {G1 g1 G2 g2 : ℕ}

/-- **An open splice-A instruction**, doubly prefixed on the padded layout: emit `1^{t1}` from
the first source mirror (no closing `false`), heal it, advance. -/
theorem qp_instr_spAo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spAo) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body) (pairTaCost G1 G2 CB C1 C2 NV t1 OUT.length)
      ⟨(2, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have f0 := qp_dispatch_spAo (s := s) (p := 0)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) h hp
  have f1 := qp_spa_rounds body idx hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2 hk hkV OUT t1
    (le_refl t1) s
  have f2a := qp_skipWsas body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true))))))) 0 G1 idx
    (if t1 = 0 then s else false) (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f2a
  have f2b := qp_crossWsa (body := body) (idx := idx)
    (s := if G1 = 0 then (if t1 = 0 then s else false) else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f2c := qp_skipW2sas body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f2d := qp_crossW2sa (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f2 := qp_skipA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f3 := qp_crossA1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f3b := qp_padPA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f3b
  have f3c := qp_padPA1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          subst h0
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * 0)) from by omega]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 0 0 _ (le_refl 0))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * 0 + 1))) from by omega]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 0 0 _ (le_refl 0))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega]
          exact liftJ3 _ _ _ _ hW1 hW2 hB (by
            have := jsE_mark_lo C1 t1 t1 (jT C2 t2 ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate t1 true))) 0 h0
            simpa using this))
  have f4 := qp_skipAms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_mark_lo C1 t1 t1 _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_mark_hi C1 t1 t1 _ i hi)⟩)
  have f5 := qp_doneA (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jsT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 t1 _ (le_refl t1)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 t1 _ (le_refl t1)))
  have f6a := qp_skipWhas body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true))))))) 0 G1 idx
    false (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f6a
  have f6b := qp_crossWha (body := body) (idx := idx) (s := if G1 = 0 then false else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f6c := qp_skipW2has body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f6d := qp_crossW2ha (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f6 := qp_skiphA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f7 := qp_crosshA1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f7b := qp_padPhA1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f7b
  have f7c := qp_padPhA1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 0
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          subst h0
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * 0)) from by omega]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jhE_m_lo C1 0 _)
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * 0 + 1))) from by omega]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jhE_m_hi C1 0 _)
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega]
          exact liftJ3 _ _ _ _ hW1 hW2 hB (by
            have := jhE_pair_lo C1 t1 0 (jT C2 t2 ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate t1 true))) h0
            simpa using this))
  have f8 := qp_healT1s body (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) G1 G2 CB C1 t1
    (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true))) hW1 hW2 hB ht1 idx
    false t1 (le_refl t1)
  have f9 := qp_doneHealA (body := body) (idx := idx)
    (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jhT C1 t1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t1 true)))))))
    (by omega)
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jhE_m_lo C1 t1 _))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jhE_m_hi C1 t1 _))
  rw [show pairTaCost G1 G2 CB C1 C2 NV t1 OUT.length
      = 1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 20) t1
          + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
              + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2
              + (2 * t1 + 2))))))))))))))))))))
      from by simp only [pairTaCost]; omega,
    run_add, f0, ← jsT_zero C1 t1, run_add, f1, run_add, f2a, run_add, f2b, run_add, f2c,
    run_add, f2d, run_add, f2, run_add, f3, run_add, f3b, run_add, f3c, run_add, f4,
    run_add, f5, ← jhT_zero C1 t1, run_add, f6a, run_add, f6b, run_add, f6c, run_add, f6d,
    run_add, f6, run_add, f7, run_add, f7b, run_add, f7c, run_add, f8, f9, jhT_last,
    jsT_zero C1 t1]

end InstrA2

/-! ### The open splice-C instruction on the padded layout -/

section InstrC
variable {G1 g1 G2 g2 : ℕ}

/-- One splice-C sub-round on the padded layout: skip both prefixes, seek through the bound,
its pad, the first source and its pad, mark the second source mirror's pair `i`, seek out,
emit a doubled `true`. -/
theorem qp_spc_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k i : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (hi : i < t2) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body)
      (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i + 22)
      ⟨(105, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))⟩
      = ⟨(105, idx, false), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
          ++ (jT C1 t1 ++ (jsT C2 t2 (i + 1) ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have hS2 : (jsT C2 t2 (i + 1)).length = 2 * C2 + 2 := jsT_length C2 t2 (i + 1) hi ht2
  have hq6 : (cntT G1 g1).length + (cntT G2 g2).length + (jsT CB j (k + 1)).length
      + (jT C1 t1).length + (jsT C2 t2 (i + 1)).length + (jT NV k).length
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 := by
    rw [hW1, hW2, hB, hS1, hS2, jT_length NV k hkV]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s0a := qp_skipWscs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true))))))) 0 G1 idx
    s (fun i' hi' => by simpa using cntE_lo G1 g1 _ i' hg1 hi')
  simp only [Nat.zero_add] at s0a
  have s0b := qp_crossWsc (body := body) (idx := idx) (s := if G1 = 0 then s else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have s0c := qp_skipW2scs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * i' = 2 * G1 + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i' hg2 hi'))
  have s0d := qp_crossW2sc (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have s1 := qp_skipC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i')
          from by omega]
      rcases Nat.lt_or_ge i' (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i' hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i') (by omega) (by omega) (by omega)))
  have s2 := qp_crossC1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have s2b := qp_padPC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i')) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i')
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i' + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i' + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at s2b
  have s2c := qp_padPC1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have s3 := qp_skipC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i')) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have s4 := qp_crossC2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have s4b := qp_padPC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i')))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i')
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i' + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i' + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at s4b
  have s4c := qp_padPC2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (Or.inl (by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
          (jsE_data C2 t2 i _ 0 (by omega) (by omega) (by omega))
      · exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (by
          have := jsE_mark_lo C2 t2 i (jT NV k
            ++ encodeD (OUT ++ List.replicate i true)) 0 h0
          simpa using this)))
  have s5 := qp_skipCms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i')))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_mark_lo C2 t2 i _ i' hi'), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i' + 1))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_mark_hi C2 t2 i _ i' hi')⟩)
  have s6 := qp_markC (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
          (jsE_data C2 t2 i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
          (jsE_data C2 t2 i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 i ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1) false
      = cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jsT C2 t2 (i + 1) ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate i true)))))) := by
    rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1
        = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i + 1))))
        from by omega,
      writeAt_append_right4 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) _
        (2 * G1 + 2) (2 * G2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * i + 1) false hW1 hW2 hB
        hS1 (by rw [List.length_append, jsT_length C2 t2 i (by omega) ht2]; omega),
      jsT_mark C2 t2 i _ hi ht2]
  rw [hw] at s6
  have s7 := qp_scanC3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2) (t2 - (i + 1)) idx
    true
    (fun i' hi' => by
      have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jsT C2 t2 (i + 1) ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2 + 2 * i') false
          = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2 + 2 * i'
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                + (2 * i + 2 + 2 * i')))) from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
          (jsE_data C2 t2 (i + 1) _ (2 * i + 2 + 2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jsT C2 t2 (i + 1) ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2 + 2 * i' + 1)
          false = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2
              + 2 * i' + 1
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                + (2 * i + 2 + 2 * i' + 1)))) from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
          (jsE_data C2 t2 (i + 1) _ (2 * i + 2 + 2 * i' + 1) (by omega) (by omega)
            (by omega))
      rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2
        + 2 * (t2 - (i + 1))
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 from by omega] at s7
  have s8 := qp_crossSC3 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 2) true (t2 - (i + 1)))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 (i + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 (i + 1) _ (by omega)))
  have s9 := qp_scanC4s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) ((C2 - t2) + k) idx
    false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (C2 - t2) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i')
            false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i')))) from by omega]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_pad C2 t2 (i + 1) _ (2 * t2 + 2 + 2 * i') hi ht2 (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i' + 1)
            false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
                  + (2 * t2 + 2 + 2 * i' + 1)))) from by omega]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_pad C2 t2 (i + 1) _ (2 * t2 + 2 + 2 * i' + 1) hi ht2 (by omega)
              (by omega))
        rw [e1, e2]
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i')
            false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + 2 * (i' - (C2 - t2)))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_data NV k 0 _ (2 * (i' - (C2 - t2))) (by omega) (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i' + 1)
            false = true := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
                + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * (i' - (C2 - t2)) + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_data NV k 0 _ (2 * (i' - (C2 - t2)) + 1) (by omega) (by omega)
              (by omega))
        rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * ((C2 - t2) + k)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
      from by omega] at s9
  have s10 := qp_crossSC4 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) false
      ((C2 - t2) + k))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega, ← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_hi NV k 0 _ (by omega)))
  have s11 := qp_scanC5s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2)
    ((NV - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (NV - k) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i') false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i'))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i') (by omega) hkV (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jsT C2 t2 (i + 1) ++ (jT NV k
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i' + 1) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i' + 1))))) from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_pad NV k 0 _ (2 * k + 2 + 2 * i' + 1) (by omega) hkV (by omega)
              (by omega))
        rw [e1, e2]
      · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
              + 2 + 2 * i'
            = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
                + 2 * (i' - (NV - k)) from by omega]
        exact preD6_data_eq (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
          (jsT C2 t2 (i + 1)) (jT NV k) (OUT ++ List.replicate i true)
          (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) (i' - (NV - k)) hq6
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
        + 2 * ((NV - k) + (OUT.length + i))
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i)
      from by omega] at s11
  have hm1 := preD6_mark_lo (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jsT C2 t2 (i + 1)) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  have hm2 := preD6_mark_hi (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jsT C2 t2 (i + 1)) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  rw [hlen] at hm1 hm2
  have s12 := qp_detectC5 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2) false
      ((NV - k) + (OUT.length + i)))
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
      + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc6 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jsT C2 t2 (i + 1)) (jT NV k) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := qp_four_TC (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i))
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 (i + 1) ++ (jT NV k ++ encodeD (OUT ++ List.replicate i true)))))))
  rw [hsn] at s13
  rw [show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i
        + 22
      = 2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
          + (2 * (C1 - t1) + (2 + (2 * i + (2 + (2 * (t2 - (i + 1)) + (2
          + (2 * ((C2 - t2) + k) + (2 + (2 * ((NV - k) + (OUT.length + i))
          + (2 + 4)))))))))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s0c, run_add, s0d, run_add, s1, run_add, s2,
    run_add, s2b, run_add, s2c, run_add, s3, run_add, s4, run_add, s4b, run_add, s4c,
    run_add, s5, run_add, s6, run_add, s7, run_add, s8, run_add, s9, run_add, s10,
    run_add, s11, run_add, s12, s13]

theorem qp_spc_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (r : ℕ) (hr : r ≤ t2)
    (s : Bool) :
    run (pairTMachine body)
      (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
        + 2 * OUT.length + 22) r)
      ⟨(105, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jsT C2 t2 0 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(105, idx, if r = 0 then s else false), 0, cntT G1 g1 ++ (cntT G2 g2
          ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jsT C2 t2 r ++ (jT NV k
            ++ encodeD (OUT ++ List.replicate r true))))))⟩ := by
  induction r with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ r ih =>
    rw [show lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 22) (r + 1)
        = lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
            + 2 * OUT.length + 22) r
            + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 22
              + 2 * r) from rfl,
      show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 22
          + 2 * r
        = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * r
          + 22 from by omega,
      run_add, ih (by omega),
      qp_spc_round body idx hg1 hg2 CB C1 C2 NV j t1 t2 k r hj ht1 ht2 hk hkV (by omega)
        OUT _,
      if_neg (by omega)]

end InstrC

/-- The padded splice-C instruction clock; `j`-independent as before. -/
def pairTcCost (G1 G2 CB C1 C2 NV t2 L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 22) t2
    + ((2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * t2 + 14)
      + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * t2 + 14)))

section InstrC2
variable {G1 g1 G2 g2 : ℕ}

/-- **An open splice-C instruction**, doubly prefixed on the padded layout: emit `1^{t2}` from
the second source mirror (no closing `false`), heal it, advance. -/
theorem qp_instr_spCo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spCo) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body) (pairTcCost G1 G2 CB C1 C2 NV t2 OUT.length)
      ⟨(2, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have f0 := qp_dispatch_spCo (s := s) (p := 0)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) h hp
  have f1 := qp_spc_rounds body idx hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2 hk hkV OUT t2
    (le_refl t2) s
  have f2a := qp_skipWscs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true))))))) 0 G1
    idx (if t2 = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f2a
  have f2b := qp_crossWsc (body := body) (idx := idx)
    (s := if G1 = 0 then (if t2 = 0 then s else false) else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f2c := qp_skipW2scs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f2d := qp_crossW2sc (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f2 := qp_skipC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f3 := qp_crossC1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f3b := qp_padPC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f3b
  have f3c := qp_padPC1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have f4 := qp_skipC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f5 := qp_crossC2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have f5b := qp_padPC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f5b
  have f5c := qp_padPC2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
                from by omega]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 t2 _ (le_refl t2))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
                from by omega]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 t2 _ (le_refl t2))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (by
            have := jsE_mark_lo C2 t2 t2 (jT NV k
              ++ encodeD (OUT ++ List.replicate t2 true)) 0 h0
            simpa using this))
  have f6 := qp_skipCms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) t2 idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_mark_lo C2 t2 t2 _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * i + 1))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_mark_hi C2 t2 t2 _ i hi)⟩)
  have f7 := qp_doneC (body := body) (idx := idx) (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jsT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 t2 _ (le_refl t2)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 t2 _ (le_refl t2)))
  have f8a := qp_skipWhcs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true))))))) 0 G1
    idx false (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f8a
  have f8b := qp_crossWhc (body := body) (idx := idx) (s := if G1 = 0 then false else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f8c := qp_skipW2hcs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f8d := qp_crossW2hc (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f8 := qp_skiphC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f9 := qp_crosshC1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f9b := qp_padPhC1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f9b
  have f9c := qp_padPhC1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have f10 := qp_skiphC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f11 := qp_crosshC2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have f11b := qp_padPhC2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f11b
  have f11c := qp_padPhC2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 0 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          subst h0
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * 0)))
                from by omega]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jhE_m_lo C2 0 _)
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * 0 + 1))))
                from by omega]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jhE_m_hi C2 0 _)
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (by
            have := jhE_pair_lo C2 t2 0 (jT NV k
              ++ encodeD (OUT ++ List.replicate t2 true)) h0
            simpa using this))
  have f12 := qp_healT2s body (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) G1
    G2 CB C1 C2 t2 (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)) hW1 hW2 hB hS1
    ht2 idx false t2 (le_refl t2)
  have f13 := qp_doneHealC (body := body) (idx := idx)
    (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jhT C2 t2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate t2 true)))))))
    (by omega)
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jhE_m_lo C2 t2 _))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jhE_m_hi C2 t2 _))
  rw [show pairTcCost G1 G2 CB C1 C2 NV t2 OUT.length
      = 1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 22) t2
          + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
              + (2 * (C1 - t1) + (2 + (2 * t2 + (2 + (2 * G1 + (2 + (2 * G2 + (2
              + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2 + (2 * (C1 - t1) + (2
              + (2 * t2 + 2))))))))))))))))))))))))))))
      from by simp only [pairTcCost]; omega,
    run_add, f0, ← jsT_zero C2 t2, run_add, f1, run_add, f2a, run_add, f2b, run_add, f2c,
    run_add, f2d, run_add, f2, run_add, f3, run_add, f3b, run_add, f3c, run_add, f4,
    run_add, f5, run_add, f5b, run_add, f5c, run_add, f6, run_add, f7, ← jhT_zero C2 t2,
    run_add, f8a, run_add, f8b, run_add, f8c, run_add, f8d, run_add, f8, run_add, f9,
    run_add, f9b, run_add, f9c, run_add, f10, run_add, f11, run_add, f11b, run_add, f11c,
    run_add, f12, f13, jhT_last, jsT_zero C2 t2]

end InstrC2

/-! ### The open splice-J instruction on the padded layout -/

section InstrJ
variable {G1 g1 G2 g2 : ℕ}

/-- One splice-J sub-round on the padded layout: skip both prefixes, seek through the bound,
both sources and all three pads, mark the live variable's pair `i`, seek out, emit a doubled
`true`. -/
theorem qp_spj_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k i : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (hi : i < k) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body)
      (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i + 24)
      ⟨(109, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true))))))⟩
      = ⟨(109, idx, false), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
          ++ (jT C1 t1 ++ (jT C2 t2 ++ (jsT NV k (i + 1)
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have hS2 : (jT C2 t2).length = 2 * C2 + 2 := jT_length C2 t2 ht2
  have hq6 : (cntT G1 g1).length + (cntT G2 g2).length + (jsT CB j (k + 1)).length
      + (jT C1 t1).length + (jT C2 t2).length + (jsT NV k (i + 1)).length
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 := by
    rw [hW1, hW2, hB, hS1, hS2, jsT_length NV k (i + 1) hi hkV]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s0a := qp_skipWsjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true))))))) 0 G1
    idx s (fun i' hi' => by simpa using cntE_lo G1 g1 _ i' hg1 hi')
  simp only [Nat.zero_add] at s0a
  have s0b := qp_crossWsj (body := body) (idx := idx) (s := if G1 = 0 then s else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have s0c := qp_skipW2sjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * i' = 2 * G1 + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i' hg2 hi'))
  have s0d := qp_crossW2sj (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have s1 := qp_skipJr1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i')
          from by omega]
      rcases Nat.lt_or_ge i' (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i' hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i') (by omega) (by omega) (by omega)))
  have s2 := qp_crossJr1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have s2b := qp_padPJ1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i')) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i')
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i' + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i' + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at s2b
  have s2c := qp_padPJ1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have s3 := qp_skipJr2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i')) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have s4 := qp_crossJr2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have s4b := qp_padPJ2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i')))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i')
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i' + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i' + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at s4b
  have s4c := qp_padPJ2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ 0 (by omega) (by omega) (by omega)))
  have s5 := qp_skipJr3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) t2 idx false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i')))
          from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
        (jsE_data C2 t2 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have s6 := qp_crossJr3 (body := body) (idx := idx) (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have s6b := qp_padPJ3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) (C2 - t2) idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i')))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i')
        (by omega) ht2 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
            + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i' + 1)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i' + 1)
        (by omega) ht2 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * (C2 - t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at s6b
  have s6c := qp_padPJ3_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (Or.inl (by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2))))
          from by omega]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
          (jsE_data NV k i _ 0 (by omega) (by omega) (by omega))
      · exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (by
          have := jsE_mark_lo NV k i (encodeD (OUT ++ List.replicate i true)) 0 h0
          simpa using this)))
  have s7 := qp_skipJms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * i')))) from by omega]
      exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_mark_lo NV k i _ i' hi'), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * i' + 1))))) from by omega]
      exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_mark_hi NV k i _ i' hi')⟩)
  have s8 := qp_markJ (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * i))))
          from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
          (jsE_data NV k i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * i + 1))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
          (jsE_data NV k i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k i ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1) false
      = cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jT C2 t2 ++ (jsT NV k (i + 1)
            ++ encodeD (OUT ++ List.replicate i true)))))) := by
    rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 1
        = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
            + (2 * i + 1))))) from by omega,
      writeAt_append_right5 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
        (jT C2 t2) _ (2 * G1 + 2) (2 * G2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2)
        (2 * i + 1) false hW1 hW2 hB hS1 hS2
        (by rw [List.length_append, jsT_length NV k i (by omega) hkV]; omega),
      jsT_mark NV k i _ hi hkV]
  rw [hw] at s8
  have s9 := qp_scanJ4s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 2)
    (k - (i + 1)) idx true
    (fun i' hi' => by
      have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jT C2 t2 ++ (jsT NV k (i + 1)
            ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 2
            + 2 * i') false = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
              + 2 + 2 * i'
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                + (2 * i + 2 + 2 * i'))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
          (jsE_data NV k (i + 1) _ (2 * i + 2 + 2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jT C2 t2 ++ (jsT NV k (i + 1)
            ++ encodeD (OUT ++ List.replicate i true))))))).getD
          (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 2
            + 2 * i' + 1) false = true := by
        rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
              + 2 + 2 * i' + 1
            = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                + (2 * i + 2 + 2 * i' + 1))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
          (jsE_data NV k (i + 1) _ (2 * i + 2 + 2 * i' + 1) (by omega) (by omega)
            (by omega))
      rw [e1, e2])
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 2
        + 2 * (k - (i + 1))
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
      from by omega] at s9
  have s10 := qp_crossSJ4 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i + 2) true
      (k - (i + 1)))
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k (i + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_hi NV k (i + 1) _ (by omega)))
  have s11 := qp_scanJ5s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2)
    ((NV - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (NV - k) with hilt | hige
      · have e1 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jsT NV k (i + 1)
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i') false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i'
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i'))))) from by omega]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_pad NV k (i + 1) _ (2 * k + 2 + 2 * i') hi hkV (by omega) (by omega))
        have e2 : (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jsT NV k (i + 1)
              ++ encodeD (OUT ++ List.replicate i true))))))).getD
            (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
              + 2 * i' + 1) false = false := by
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                + 2 * k + 2 + 2 * i' + 1
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                  + (2 * k + 2 + 2 * i' + 1))))) from by omega]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_pad NV k (i + 1) _ (2 * k + 2 + 2 * i' + 1) hi hkV (by omega)
              (by omega))
        rw [e1, e2]
      · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
              + 2 + 2 * i'
            = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
                + 2 * (i' - (NV - k)) from by omega]
        exact preD6_data_eq (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
          (jT C2 t2) (jsT NV k (i + 1)) (OUT ++ List.replicate i true)
          (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) (i' - (NV - k)) hq6
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2
        + 2 * ((NV - k) + (OUT.length + i))
      = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i)
      from by omega] at s11
  have hm1 := preD6_mark_lo (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jT C2 t2) (jsT NV k (i + 1)) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  have hm2 := preD6_mark_hi (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jT C2 t2) (jsT NV k (i + 1)) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6
  rw [hlen] at hm1 hm2
  have s12 := qp_detectJ5 (body := body) (idx := idx)
    (s := storedD (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k + 2) false
      ((NV - k) + (OUT.length + i)))
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12
      + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc6 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jT C2 t2) (jsT NV k (i + 1)) (OUT ++ List.replicate i true)
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12) hq6 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := qp_four_TJ (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 12 + 2 * (OUT.length + i))
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k (i + 1) ++ encodeD (OUT ++ List.replicate i true)))))))
  rw [hsn] at s13
  rw [show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * i
        + 24
      = 2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
          + (2 * (C1 - t1) + (2 + (2 * t2 + (2 + (2 * (C2 - t2) + (2 + (2 * i + (2
          + (2 * (k - (i + 1)) + (2 + (2 * ((NV - k) + (OUT.length + i))
          + (2 + 4)))))))))))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s0c, run_add, s0d, run_add, s1, run_add, s2,
    run_add, s2b, run_add, s2c, run_add, s3, run_add, s4, run_add, s4b, run_add, s4c,
    run_add, s5, run_add, s6, run_add, s6b, run_add, s6c, run_add, s7, run_add, s8,
    run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem qp_spj_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (r : ℕ) (hr : r ≤ k)
    (s : Bool) :
    run (pairTMachine body)
      (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
        + 2 * OUT.length + 24) r)
      ⟨(109, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jsT NV k 0 ++ encodeD OUT)))))⟩
      = ⟨(109, idx, if r = 0 then s else false), 0, cntT G1 g1 ++ (cntT G2 g2
          ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2 ++ (jsT NV k r
            ++ encodeD (OUT ++ List.replicate r true))))))⟩ := by
  induction r with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ r ih =>
    rw [show lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 24) (r + 1)
        = lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
            + 2 * OUT.length + 24) r
            + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 24
              + 2 * r) from rfl,
      show 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 24
          + 2 * r
        = 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * OUT.length + 2 * r
          + 24 from by omega,
      run_add, ih (by omega),
      qp_spj_round body idx hg1 hg2 CB C1 C2 NV j t1 t2 k r hj ht1 ht2 hk hkV (by omega)
        OUT _,
      if_neg (by omega)]

end InstrJ

/-- The padded splice-J instruction clock; `j`-independent as before. -/
def pairTjCost (G1 G2 CB C1 C2 NV k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 24) k
    + ((2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * k + 18)
      + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * k + 18)))

section InstrJ2
variable {G1 g1 G2 g2 : ℕ}

/-- **An open splice-J instruction**, doubly prefixed on the padded layout: emit `1^k` from
the live variable (no closing `false`), heal it, advance. -/
theorem qp_instr_spJo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spJo) (hg1 : g1 ≤ G1)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (OUT : List Bool) (s : Bool) :
    run (pairTMachine body) (pairTjCost G1 G2 CB C1 C2 NV k OUT.length)
      ⟨(2, idx, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
            ++ (jT C2 t2 ++ (jT NV k ++ encodeD (OUT ++ List.replicate k true))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have hS2 : (jT C2 t2).length = 2 * C2 + 2 := jT_length C2 t2 ht2
  have f0 := qp_dispatch_spJo (s := s) (p := 0)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD OUT)))))) h hp
  have f1 := qp_spj_rounds body idx hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2 hk hkV OUT k
    (le_refl k) s
  have f2a := qp_skipWsjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true))))))) 0 G1
    idx (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f2a
  have f2b := qp_crossWsj (body := body) (idx := idx)
    (s := if G1 = 0 then (if k = 0 then s else false) else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f2c := qp_skipW2sjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f2d := qp_crossW2sj (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f2 := qp_skipJr1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f3 := qp_crossJr1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f3b := qp_padPJ1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f3b
  have f3c := qp_padPJ1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have f4 := qp_skipJr2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f5 := qp_crossJr2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have f5b := qp_padPJ2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f5b
  have f5c := qp_padPJ2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ 0 (by omega) (by omega) (by omega)))
  have f6 := qp_skipJr3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) t2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
        (jsE_data C2 t2 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f7 := qp_crossJr3 (body := body) (idx := idx) (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have f7b := qp_padPJ3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) (C2 - t2) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i)
        (by omega) ht2 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
            + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i + 1)
        (by omega) ht2 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * (C2 - t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at f7b
  have f7c := qp_padPJ3_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + 2 * k)))) from by omega]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k k _ (le_refl k))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + (2 * k + 1))))) from by omega]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_hi NV k k _ (le_refl k))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2))))
              from by omega]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (by
            have := jsE_mark_lo NV k k (encodeD (OUT ++ List.replicate k true)) 0 h0
            simpa using this))
  have f8 := qp_skipJms body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * i)))) from by omega]
      exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_mark_lo NV k k _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * i + 1))))) from by omega]
      exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_mark_hi NV k k _ i hi)⟩)
  have f9 := qp_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jsT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k k _ (le_refl k)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_hi NV k k _ (le_refl k)))
  have f10a := qp_skipWhjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true))))))) 0 G1
    idx false (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f10a
  have f10b := qp_crossWhj (body := body) (idx := idx)
    (s := if G1 = 0 then false else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f10c := qp_skipW2hjs body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2) G2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f10d := qp_crossW2hj (body := body) (idx := idx)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f10 := qp_skiphJ1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have f11 := qp_crosshJ1 (body := body) (idx := idx) (s := if j = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have f11b := qp_padPhJ1s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at f11b
  have f11c := qp_padPhJ1_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have f12 := qp_skiphJ2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f13 := qp_crosshJ2 (body := body) (idx := idx) (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have f13b := qp_padPhJ2s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at f13b
  have f13c := qp_padPhJ2_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ 0 (by omega) (by omega) (by omega)))
  have f14 := qp_skiphJ3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) t2 idx false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
        (jsE_data C2 t2 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have f15 := qp_crosshJ3 (body := body) (idx := idx) (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have f15b := qp_padPhJ3s body
    (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) (C2 - t2) idx false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i)
        (by omega) ht2 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
            + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i + 1)
        (by omega) ht2 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * (C2 - t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at f15b
  have f15c := qp_padPhJ3_bound (body := body) (idx := idx) (s := false)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k 0 ++ encodeD (OUT ++ List.replicate k true)))))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · right
          subst h0
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + 2 * 0)))) from by omega]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jhE_m_lo NV 0 _)
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + (2 * 0 + 1))))) from by omega]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jhE_m_hi NV 0 _)
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2))))
              from by omega]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (by
            have := jhE_pair_lo NV k 0 (encodeD (OUT ++ List.replicate k true)) h0
            simpa using this))
  have f16 := qp_healJ5s body (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1)
    (jT C2 t2) G1 G2 CB C1 C2 NV k (encodeD (OUT ++ List.replicate k true)) hW1 hW2 hB
    hS1 hS2 hkV idx false k (le_refl k)
  have f17 := qp_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jhT NV k k ++ encodeD (OUT ++ List.replicate k true)))))))
    (by omega)
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
          from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jhE_m_lo NV k _))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
            + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + (2 * k + 1))))) from by omega]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jhE_m_hi NV k _))
  rw [show pairTjCost G1 G2 CB C1 C2 NV k OUT.length
      = 1 + (lp3SpRounds (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * OUT.length + 24) k
          + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
              + (2 * (C1 - t1) + (2 + (2 * t2 + (2 + (2 * (C2 - t2) + (2 + (2 * k + (2
              + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2
              + (2 * t1 + (2 + (2 * (C1 - t1) + (2 + (2 * t2 + (2 + (2 * (C2 - t2) + (2
              + (2 * k + 2))))))))))))))))))))))))))))))))))))
      from by simp only [pairTjCost]; omega,
    run_add, f0, ← jsT_zero NV k, run_add, f1, run_add, f2a, run_add, f2b, run_add, f2c,
    run_add, f2d, run_add, f2, run_add, f3, run_add, f3b, run_add, f3c, run_add, f4,
    run_add, f5, run_add, f5b, run_add, f5c, run_add, f6, run_add, f7, run_add, f7b,
    run_add, f7c, run_add, f8, run_add, f9, ← jhT_zero NV k, run_add, f10a, run_add, f10b,
    run_add, f10c, run_add, f10d, run_add, f10, run_add, f11, run_add, f11b, run_add,
    f11c, run_add, f12, run_add, f13, run_add, f13b, run_add, f13c, run_add, f14,
    run_add, f15, run_add, f15b, run_add, f15c, run_add, f16, f17, jhT_last,
    jsT_zero NV k]

end InstrJ2

/-! ## The instruction segment and the round -/

/-- The per-instruction clock on the padded layout (`prog3OutN` reused with the source
mirror values and the live value). -/
def pairTInstrCost (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n .spJo with
  | .bit _ => 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
      + 2 * (L + (prog3OutN body t1 t2 k n).length) + 19
  | .spAo => pairTaCost G1 G2 CB C1 C2 NV t1 (L + (prog3OutN body t1 t2 k n).length)
  | .spCo => pairTcCost G1 G2 CB C1 C2 NV t2 (L + (prog3OutN body t1 t2 k n).length)
  | .spJo => pairTjCost G1 G2 CB C1 C2 NV k (L + (prog3OutN body t1 t2 k n).length)

def pairTSegN (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k L n
      + pairTInstrCost body G1 G2 CB C1 C2 NV t1 t2 k L n

/-- **The segment invariant** on the padded layout. -/
theorem qp_run_instrs (body : List L3Instr) (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k ≤ NV) (out' : List Bool) (n : ℕ)
    (hn : n ≤ body.length) (s : Bool) :
    run (pairTMachine body) (pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
        ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k ++ encodeD out')))))⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
            ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k n))))))⟩ := by
  induction n with
  | zero => simp only [pairTSegN]; rw [run_zero]; simp [prog3OutN]
  | succ n ih =>
    rw [show pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k out'.length (n + 1)
        = pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k out'.length n
            + pairTInstrCost body G1 G2 CB C1 C2 NV t1 t2 k out'.length n from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n .spJo with
    | bit b =>
      have hin := qp_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2
        hk hkV (out' ++ prog3OutN body t1 t2 k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body t1 t2 k n ++ [b] = prog3OutN body t1 t2 k (n + 1) from by
          simp only [prog3OutN, hp]; rfl] at hin
      simp only [pairTInstrCost, hp]
      rw [hin]
      simp
    | spAo =>
      have hin := qp_instr_spAo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2
        hk hkV (out' ++ prog3OutN body t1 t2 k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body t1 t2 k n ++ List.replicate t1 true
            = prog3OutN body t1 t2 k (n + 1) from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [pairTInstrCost, hp]
      rw [hin]
      simp
    | spCo =>
      have hin := qp_instr_spCo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2
        hk hkV (out' ++ prog3OutN body t1 t2 k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body t1 t2 k n ++ List.replicate t2 true
            = prog3OutN body t1 t2 k (n + 1) from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [pairTInstrCost, hp]
      rw [hin]
      simp
    | spJo =>
      have hin := qp_instr_spJo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg1 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2
        hk hkV (out' ++ prog3OutN body t1 t2 k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body t1 t2 k n ++ List.replicate k true
            = prog3OutN body t1 t2 k (n + 1) from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [pairTInstrCost, hp]
      rw [hin]
      simp

/-- The round clock: the doubly-prefixed loop find plus the segment plus the doubly-prefixed
increment pass with its three pad-crossings; `j`-independent. -/
def pairTRoundCost (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L : ℕ) : ℕ :=
  (2 * G1 + 2 * G2 + 2 * k + 6) + (pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k L body.length
    + (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * k + 21))

/-- **One loop round** on the padded layout: find-mark the padded bound's pair `k`, run the
body, increment the live variable in place across the three pads. -/
theorem qp_round (body : List L3Instr) (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 k : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hk : k < j) (hkV : k < NV) (out' : List Bool)
    (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (pairTMachine body) (pairTRoundCost body G1 G2 CB C1 C2 NV t1 t2 k out'.length)
      ⟨(97, ptrIn, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k
        ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k ++ encodeD out')))))⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
            ++ (jT NV (k + 1) ++ encodeD (out' ++ prog3Out body t1 t2 k))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hB : (jsT CB j (k + 1)).length = 2 * CB + 2 := jsT_length CB j (k + 1) (by omega) hj
  have hS1 : (jT C1 t1).length = 2 * C1 + 2 := jT_length C1 t1 ht1
  have hS2 : (jT C2 t2).length = 2 * C2 + 2 := jT_length C2 t2 ht2
  have r0a := qp_skipWfs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out')))))) 0 G1 ptrIn s
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at r0a
  have r0b := qp_crossWf (body := body) (idx := ptrIn) (s := if G1 = 0 then s else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out'))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have r0c := qp_skipW2fs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out')))))) (2 * G1 + 2) G2 ptrIn false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have r0d := qp_crossW2f (body := body) (idx := ptrIn)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out'))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have r1 := qp_skipBs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out')))))) (2 * G1 + 2 + 2 * G2 + 2) k ptrIn
    false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j k _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_hi CB j k _ i hi)⟩)
  have r2 := qp_markB (body := body) (idx := ptrIn) (s := if k = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * k)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out'))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * k = 2 * G1 + 2 + (2 * G2 + 2 + 2 * k)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j k _ (2 * k) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * k + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * k + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j k _ (2 * k + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV k ++ encodeD out'))))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * k + 1) false
      = cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1
          ++ (jT C2 t2 ++ (jT NV k ++ encodeD out'))))) := by
    rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * k + 1
        = 2 * G1 + 2 + (2 * G2 + 2 + (2 * k + 1)) from by omega,
      writeAt_append_right2 (cntT G1 g1) (cntT G2 g2) _ (2 * G1 + 2) (2 * G2 + 2)
        (2 * k + 1) false hW1 hW2
        (by rw [List.length_append, jsT_length CB j k (by omega) hj]; omega),
      jsT_mark CB j k _ hk hj]
  rw [hwm] at r2
  have r3 := qp_run_instrs body G1 g1 hg1 G2 g2 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2 hk
    (by omega) out' body.length (le_refl _) true
  have r4 := qp_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (Nat.lt_irrefl _)
  have r4a := qp_skipWis body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length))))))) 0 G1
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at r4a
  have r4b := qp_crossWi (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if G1 = 0 then (if body.length = 0 then true else false) else true)
    (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have r4c := qp_skipW2is body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length))))))) (2 * G1 + 2) G2
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have r4d := qp_crossW2i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have r5 := qp_skipi1s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j (k + 1) _ i hik)
      · exact liftJ2 _ _ _ hW1 hW2
          (jsE_data CB j (k + 1) _ (2 * i) (by omega) (by omega) (by omega)))
  have r6 := qp_crossi1 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if j = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j (k + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j (k + 1) _ (by omega)))
  have r6b := qp_padPI1s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2) (CB - j)
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i)
        (by omega) hj (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 2 + 2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_pad CB j (k + 1) _ (2 * j + 2 + 2 * i + 1)
        (by omega) hj (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 2 + 2 * (CB - j)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 from by omega] at r6b
  have r6c := qp_padPI1_bound (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := false) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rcases Nat.eq_zero_or_pos t1 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
              ← jsT_zero C1 t1]
            exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2)) from by omega, ← jsT_zero C1 t1]
          exact liftJ3 _ _ _ _ hW1 hW2 hB
            (jsE_data C1 t1 0 _ 0 (by omega) (by omega) (by omega)))
  have r7 := qp_skipi2s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2) t1 ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * i)) from by omega,
        ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB
        (jsE_data C1 t1 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r8 := qp_crossi2 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if t1 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + 2 * t1)) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_lo C1 t1 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 1))) from by omega,
        ← jsT_zero C1 t1]
        exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_m_hi C1 t1 0 _ (by omega)))
  have r8b := qp_padPI2s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2) (C1 - t1)
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i)
        (by omega) ht1 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * t1 + 2 + 2 * i + 1)))
          from by omega, ← jsT_zero C1 t1]
      exact liftJ3 _ _ _ _ hW1 hW2 hB (jsE_pad C1 t1 0 _ (2 * t1 + 2 + 2 * i + 1)
        (by omega) ht1 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * t1 + 2 + 2 * (C1 - t1)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 from by omega] at r8b
  have r8c := qp_padPI2_bound (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := false) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rcases Nat.eq_zero_or_pos t2 with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
                from by omega, ← jsT_zero C2 t2]
            exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2))) from by omega,
            ← jsT_zero C2 t2]
          exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
            (jsE_data C2 t2 0 _ 0 (by omega) (by omega) (by omega)))
  have r9 := qp_skipi3s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2) t2
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * i)))
          from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1
        (jsE_data C2 t2 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r10 := qp_crossi3 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if t2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + 2 * t2)))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_lo C2 t2 0 _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * t2 + 1))))
          from by omega, ← jsT_zero C2 t2]
        exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_m_hi C2 t2 0 _ (by omega)))
  have r10b := qp_padPI3s body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2) (C2 - t2)
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i)
        (by omega) ht2 (by omega) (by omega)), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
            + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2
              + (2 * t2 + 2 + 2 * i + 1)))) from by omega, ← jsT_zero C2 t2]
      exact liftJ4 _ _ _ _ _ hW1 hW2 hB hS1 (jsE_pad C2 t2 0 _ (2 * t2 + 2 + 2 * i + 1)
        (by omega) ht2 (by omega) (by omega))⟩)
  rw [ite_self, show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * t2 + 2
        + 2 * (C2 - t2)
      = 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
      from by omega] at r10b
  have r10c := qp_padPI3_bound (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := false) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rcases Nat.eq_zero_or_pos k with h0 | h0
        · right
          constructor
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + 2 * k)))) from by omega, ← jsT_zero NV k]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k 0 _ (by omega))
          · rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 1
                = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
                    + (2 * k + 1))))) from by omega, ← jsT_zero NV k]
            exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_hi NV k 0 _ (by omega))
        · left
          rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2
              = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2))))
              from by omega, ← jsT_zero NV k]
          exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
            (jsE_data NV k 0 _ 0 (by omega) (by omega) (by omega)))
  have r11 := qp_walkIs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1)
      ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV k
        ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2) k
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * i
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2
              + 2 * i)))) from by omega, ← jsT_zero NV k]
      exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2
        (jsE_data NV k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r12 := qp_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k)))))
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j (k + 1) ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)))))))
    (by rw [← jsT_zero NV k]
        exact liftJ5 _ _ _ _ _ _ hW1 hW2 hB hS1 hS2 (jsE_m_lo NV k 0 _ (by omega)))
  rw [W4_append_right5 (cntT G1 g1) (cntT G2 g2) (jsT CB j (k + 1)) (jT C1 t1) (jT C2 t2)
      (jT NV k ++ encodeD (out' ++ prog3OutN body t1 t2 k body.length)) (2 * G1 + 2)
      (2 * G2 + 2) (2 * CB + 2) (2 * C1 + 2) (2 * C2 + 2) (2 * k) true true false true
      hW1 hW2 hB hS1 hS2
      (by rw [List.length_append, jT_length NV k (by omega)]; omega),
    jT_incr NV k _ hkV] at r12
  rw [show pairTRoundCost body G1 G2 CB C1 C2 NV t1 t2 k out'.length
      = 2 * G1 + (2 + (2 * G2 + (2 + (2 * k + (2
          + (pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k out'.length body.length + (1
          + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * (CB - j) + (2 + (2 * t1 + (2
          + (2 * (C1 - t1) + (2 + (2 * t2 + (2 + (2 * (C2 - t2) + (2
          + (2 * k + 4))))))))))))))))))))))))
      from by simp only [pairTRoundCost]; omega,
    run_add, r0a, run_add, r0b, run_add, r0c, run_add, r0d, run_add, r1, run_add, r2,
    run_add, r3, run_add, r4, run_add, r4a, run_add, r4b, run_add, r4c, run_add, r4d,
    run_add, r5, run_add, r6, run_add, r6b, run_add, r6c, run_add, r7, run_add, r8,
    run_add, r8b, run_add, r8c, run_add, r9, run_add, r10, run_add, r10b, run_add, r10c,
    run_add, r11,
    show 2 * G1 + 2 + 2 * G2 + 2 + 2 * CB + 2 + 2 * C1 + 2 + 2 * C2 + 2 + 2 * k
      = 2 * G1 + 2 + (2 * G2 + 2 + (2 * CB + 2 + (2 * C1 + 2 + (2 * C2 + 2 + 2 * k))))
      from by omega,
    r12, prog3Out]

/-! ## The rounds invariant and the loop completion -/

def pairTClockN (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => pairTClockN body G1 G2 CB C1 C2 NV t1 t2 Lout k
      + pairTRoundCost body G1 G2 CB C1 C2 NV t1 t2 k
          (Lout + (loop3OutN body t1 t2 k).length)

/-- **The rounds invariant** on the padded layout: `k` rounds find-mark the padded bound to
`jsT CB j k` and drive the live variable to `jT NV k`, appending `loop3OutN`. -/
theorem qp_run_rounds (body : List L3Instr) (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hjV : j ≤ NV) (out : List Bool) (k : ℕ) (hk : k ≤ j) (s : Bool) :
    run (pairTMachine body) (pairTClockN body G1 G2 CB C1 C2 NV t1 t2 out.length k)
      ⟨(97, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j 0
        ++ (jT C1 t1 ++ (jT C2 t2 ++ (jT NV 0 ++ encodeD out)))))⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j k ++ (jT C1 t1 ++ (jT C2 t2
            ++ (jT NV k ++ encodeD (out ++ loop3OutN body t1 t2 k))))))⟩ := by
  induction k with
  | zero => simp only [pairTClockN]; rw [run_zero]; simp [loop3OutN]
  | succ k ih =>
    have hrd := qp_round body G1 g1 hg1 G2 g2 hg2 CB C1 C2 NV j t1 t2 k hj ht1 ht2
      (by omega) (by omega) (out ++ loop3OutN body t1 t2 k) ⟨0, Nat.succ_pos _⟩
      (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loop3OutN body t1 t2 k ++ prog3Out body t1 t2 k
        = loop3OutN body t1 t2 (k + 1) from rfl] at hrd
    rw [show pairTClockN body G1 G2 CB C1 C2 NV t1 t2 out.length (k + 1)
        = pairTClockN body G1 G2 CB C1 C2 NV t1 t2 out.length k
            + pairTRoundCost body G1 G2 CB C1 C2 NV t1 t2 k
                (out.length + (loop3OutN body t1 t2 k).length) from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

def pairTClock (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 j Lout : ℕ) : ℕ :=
  pairTClockN body G1 G2 CB C1 C2 NV t1 t2 Lout j
    + (2 * G1 + (2 + (2 * G2 + (2 + (2 * j + (2 + (2 * G1 + (2 + (2 * G2 + (2
        + (2 * j + 2)))))))))))

/-- **THE PADDED TRIANGLE-ROW ENGINE RUNS TO COMPLETION** — both prefixes preserved verbatim,
the padded bound find-marked and healed by the content-blind finale, the live variable driven
to the bound's value inside its fixed footprint. -/
theorem pairT_run (body : List L3Instr) (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hjV : j ≤ NV) (out : List Bool) :
    run (pairTMachine body) (pairTClock body G1 G2 CB C1 C2 NV t1 t2 j out.length)
      (init (pairTMachine body) (cntT G1 g1 ++ (cntT G2 g2 ++ (jT CB j ++ (jT C1 t1
        ++ (jT C2 t2 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1,
          cntT G1 g1 ++ (cntT G2 g2 ++ (jT CB j ++ (jT C1 t1 ++ (jT C2 t2
            ++ (jT NV j ++ encodeD (out ++ loop3Out body t1 t2 j))))))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  rw [init_pt]
  rw [show (cntT G1 g1 ++ (cntT G2 g2 ++ (jT CB j ++ (jT C1 t1 ++ (jT C2 t2
        ++ (jT NV 0 ++ encodeD out))))) : List Bool)
      = cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j 0 ++ (jT C1 t1 ++ (jT C2 t2
          ++ (jT NV 0 ++ encodeD out))))) from by rw [jsT_zero]]
  simp only [pairTClock]
  have f0a := qp_skipWfs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j))))))) 0 G1
    ⟨0, Nat.succ_pos _⟩ false (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f0a
  have f0b := qp_crossWf (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G1 = 0 then false else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f0c := qp_skipW2fs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (2 * G1 + 2) G2 ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f0d := qp_crossW2f (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f1 := qp_skipBs body (cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (2 * G1 + 2 + 2 * G2 + 2) j ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_lo CB j j _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (jsE_mark_hi CB j j _ i hi)⟩)
  have f2 := qp_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if j = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jsT CB j j ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_lo CB j j _ (le_refl j)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jsE_m_hi CB j j _ (le_refl j)))
  have f3a := qp_skipWfins body (cntT G1 g1 ++ (cntT G2 g2 ++ (jhT CB j 0 ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j))))))) 0 G1
    ⟨0, Nat.succ_pos _⟩ false (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f3a
  have f3b := qp_crossWfin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G1 = 0 then false else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jhT CB j 0 ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f3c := qp_skipW2fins body (cntT G1 g1 ++ (cntT G2 g2 ++ (jhT CB j 0 ++ (jT C1 t1
      ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (2 * G1 + 2) G2 ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f3d := qp_crossW2fin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jhT CB j 0 ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f4 := qp_healBJs body (cntT G1 g1) (cntT G2 g2) G1 G2 CB j
    (jT C1 t1 ++ (jT C2 t2 ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j))))
    hW1 hW2 hj ⟨0, Nat.succ_pos _⟩ false j (le_refl j)
  have f5 := qp_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if j = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * j)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (jhT CB j j ++ (jT C1 t1 ++ (jT C2 t2
      ++ (jT NV j ++ encodeD (out ++ loop3OutN body t1 t2 j)))))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j = 2 * G1 + 2 + (2 * G2 + 2 + 2 * j)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jhE_m_lo CB j _))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * j + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * j + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (jhE_m_hi CB j _))
  rw [run_add, qp_run_rounds body G1 g1 hg1 G2 g2 hg2 CB C1 C2 NV j t1 t2 hj ht1 ht2 hjV
      out j (le_refl j) false, ite_self,
    run_add, f0a, run_add, f0b, run_add, f0c, run_add, f0d, run_add, f1, run_add, f2,
    ← jhT_zero CB j, run_add, f3a, run_add, f3b, run_add, f3c, run_add, f3d, run_add, f4,
    f5, jhT_last,
    show loop3Out body t1 t2 j = loop3OutN body t1 t2 j from rfl]

/-- The engine **halts by itself** at its clock. -/
theorem pairT_halted (body : List L3Instr) (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ)
    (hg2 : g2 ≤ G2) (CB C1 C2 NV j t1 t2 : ℕ) (hj : j ≤ CB) (ht1 : t1 ≤ C1)
    (ht2 : t2 ≤ C2) (hjV : j ≤ NV) (out : List Bool) :
    (pairTMachine body).halt
      (run (pairTMachine body) (pairTClock body G1 G2 CB C1 C2 NV t1 t2 j out.length)
        (init (pairTMachine body) (cntT G1 g1 ++ (cntT G2 g2 ++ (jT CB j ++ (jT C1 t1
          ++ (jT C2 t2 ++ (jT NV 0 ++ encodeD out)))))))).st = true := by
  rw [pairT_run body G1 g1 hg1 G2 g2 hg2 CB C1 C2 NV j t1 t2 hj ht1 ht2 hjV out]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
