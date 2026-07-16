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
lands the machine and its full step layer; the instruction lemmas, rounds, and the triangle
composite follow in the continuation bricks.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
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

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
