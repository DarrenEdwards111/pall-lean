import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg2P

/-!
# Cook–Levin M2 emitter — the prefixed triple-source loop engine

`loopProg3PMachine body` is `loopProg3Machine body` re-derived for the layout
`cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out))))` — the passive
marked-counter prefix in front, the `rep_run` hypothesis shape.  The lift is the established
mechanical pattern (`progP`, `loopProg2P`): every reset-entry track gains one leading skip of the
prefix, every position shifts by `2G+2`, every fact climbs one lift level
(`liftJ3 → liftJ4`, `preD4 → preD5`, `writes_snoc4 → writes_snoc5`,
`W4_append_right3 → W4_append_right4`).  Control keeps the unprefixed phase numbering `0–96`
verbatim and appends the ten prefix-skip pairs as phases `97–116` — every reset-to-`0` transition
retargets to the corresponding pair, which crosses the prefix and hands off to the original track at
position `2G+2`.  The instruction set, denotation, and the at-most-one pair bodies are reused
unchanged — `loopProg3P_run` emits the same `loop3Out body a c N`, the prefix preserved verbatim,
and `amoPairHeadP_family_run` demonstrates a real pair row under the prefix.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

/-! ## The five-region lift layer -/

theorem liftJ4 (A B C D X : List Bool) {qa qb qc qd p : ℕ} (ha : A.length = qa)
    (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd) {w : Bool}
    (h : X.getD p false = w) :
    (A ++ (B ++ (C ++ (D ++ X)))).getD (qa + (qb + (qc + (qd + p)))) false = w := by
  exact liftJ A _ ha (liftJ3 B C D X hb hc hd h)

theorem writeAt_append_right4 (A B C D X : List Bool) (qa qb qc qd p : ℕ) (w : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd)
    (hp : p < X.length) :
    writeAt (A ++ (B ++ (C ++ (D ++ X)))) (qa + (qb + (qc + (qd + p)))) w
      = A ++ (B ++ (C ++ (D ++ writeAt X p w))) := by
  rw [writeAt_append_right A _ qa (qb + (qc + (qd + p))) w ha
      (by simp only [List.length_append]; omega),
    writeAt_append_right3 B C D X qb qc qd p w hb hc hd hp]

theorem preD5_data_eq (A B C D E out : List Bool) (q i : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length = q) (h : i < out.length) :
    (A ++ (B ++ (C ++ (D ++ (E ++ encodeD out))))).getD (q + 2 * i) false
      = (A ++ (B ++ (C ++ (D ++ (E ++ encodeD out))))).getD (q + 2 * i + 1) false := by
  have := preD_data_eq (A ++ (B ++ (C ++ (D ++ E)))) out q i
    (by simp only [List.length_append]; omega) h
  simpa [List.append_assoc] using this

theorem preD5_mark_lo (A B C D E out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length = q) :
    (A ++ (B ++ (C ++ (D ++ (E ++ encodeD out))))).getD (q + 2 * out.length) false
      = false := by
  have := preD_mark_lo (A ++ (B ++ (C ++ (D ++ E)))) out q
    (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem preD5_mark_hi (A B C D E out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length = q) :
    (A ++ (B ++ (C ++ (D ++ (E ++ encodeD out))))).getD (q + 2 * out.length + 1) false
      = true := by
  have := preD_mark_hi (A ++ (B ++ (C ++ (D ++ E)))) out q
    (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem writes_snoc5 (A B C D E out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length + E.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ (D ++ (E ++ encodeD out)))))
        (q + 2 * out.length) b) (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false)
        (q + 2 * out.length + 3) true
      = A ++ (B ++ (C ++ (D ++ (E ++ encodeD (out ++ [b]))))) := by
  have h := writes_snoc (A ++ (B ++ (C ++ (D ++ E)))) out q
    (by simp only [List.length_append]; omega) b
  simpa [List.append_assoc] using h

theorem W4_append_right4 (A B C D X : List Bool) (qa qb qc qd p : ℕ) (b1 b2 b3 b4 : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hd : D.length = qd)
    (hp : p + 3 < X.length) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ (D ++ X))))
        (qa + (qb + (qc + (qd + p)))) b1) (qa + (qb + (qc + (qd + p))) + 1) b2)
        (qa + (qb + (qc + (qd + p))) + 2) b3) (qa + (qb + (qc + (qd + p))) + 3) b4
      = A ++ (B ++ (C ++ (D ++ writeAt (writeAt (writeAt (writeAt X p b1) (p + 1) b2)
          (p + 2) b3) (p + 3) b4))) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  have hl2 : (writeAt (writeAt X p b1) (p + 1) b2).length = X.length := by
    rw [writeAt_of_lt b2 (by omega), List.length_set, hl1]
  have hl3 : (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3).length = X.length := by
    rw [writeAt_of_lt b3 (by omega), List.length_set, hl2]
  rw [writeAt_append_right4 A B C D X qa qb qc qd p b1 ha hb hc hd (by omega),
    show qa + (qb + (qc + (qd + p))) + 1 = qa + (qb + (qc + (qd + (p + 1)))) from by omega,
    writeAt_append_right4 A B C D _ qa qb qc qd (p + 1) b2 ha hb hc hd (by rw [hl1]; omega),
    show qa + (qb + (qc + (qd + p))) + 2 = qa + (qb + (qc + (qd + (p + 2)))) from by omega,
    writeAt_append_right4 A B C D _ qa qb qc qd (p + 2) b3 ha hb hc hd (by rw [hl2]; omega),
    show qa + (qb + (qc + (qd + p))) + 3 = qa + (qb + (qc + (qd + (p + 3)))) from by omega,
    writeAt_append_right4 A B C D _ qa qb qc qd (p + 3) b4 ha hb hc hd (by rw [hl3]; omega)]

/-! ## The machine

Control: `Fin 117 × Fin (|body|+1) × Bool`.  Phases `0–96` are the unprefixed machine verbatim —
`0/1` the loop find, `2` the four-way dispatch, `3–16` the append track, `17–36` the open splice-A
track, `37–58` the open splice-C track, `59–82` the open splice-J track, `83–93` the in-place
increment, `94/95` heal the bound, `96` = halt.  Phases `97–116` are the ten prefix-skip pairs, one
per reset-entry track: `97/98 → 0` (the find; also the machine start), `99/100 → 3` (append),
`101/102 → 17` (splice-A), `103/104 → 33` (heal-A), `105/106 → 37` (splice-C), `107/108 → 53`
(heal-C), `109/110 → 59` (splice-J), `111/112 → 75` (heal-J), `113/114 → 83` (increment),
`115/116 → 94` (the finale).  Every reset-to-`0` transition targets its pair; each pair crosses
`cntT G g` and hands off at position `2G+2`. -/

def loopProg3PMachine (body : List L3Instr) : Machine where
  State := Fin 117 × Fin (body.length + 1) × Bool
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
       else (if b then ((19, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((35, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((39, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 39 then ((40, s.2.1, b), none, 1)
    else if s.1 = 40 then
      (if s.2.2 then ((39, s.2.1, s.2.2), none, 1)
       else (if b then ((41, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((55, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 55 then ((56, s.2.1, b), none, 1)
    else if s.1 = 56 then
      (if s.2.2 then ((55, s.2.1, s.2.2), none, 1)
       else (if b then ((57, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((61, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 61 then ((62, s.2.1, b), none, 1)
    else if s.1 = 62 then
      (if s.2.2 then ((61, s.2.1, s.2.2), none, 1)
       else (if b then ((63, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 63 then ((64, s.2.1, b), none, 1)
    else if s.1 = 64 then
      (if s.2.2 then ((63, s.2.1, s.2.2), none, 1)
       else (if b then ((65, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((77, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 77 then ((78, s.2.1, b), none, 1)
    else if s.1 = 78 then
      (if s.2.2 then ((77, s.2.1, s.2.2), none, 1)
       else (if b then ((79, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 79 then ((80, s.2.1, b), none, 1)
    else if s.1 = 80 then
      (if s.2.2 then ((79, s.2.1, s.2.2), none, 1)
       else (if b then ((81, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((85, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 85 then ((86, s.2.1, b), none, 1)
    else if s.1 = 86 then
      (if s.2.2 then ((85, s.2.1, s.2.2), none, 1)
       else (if b then ((87, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 87 then ((88, s.2.1, b), none, 1)
    else if s.1 = 88 then
      (if s.2.2 then ((87, s.2.1, s.2.2), none, 1)
       else (if b then ((89, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
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
       else (if b then ((0, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 99 then ((100, s.2.1, b), none, 1)
    else if s.1 = 100 then
      (if s.2.2 then ((99, s.2.1, s.2.2), none, 1)
       else (if b then ((3, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 101 then ((102, s.2.1, b), none, 1)
    else if s.1 = 102 then
      (if s.2.2 then ((101, s.2.1, s.2.2), none, 1)
       else (if b then ((17, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 103 then ((104, s.2.1, b), none, 1)
    else if s.1 = 104 then
      (if s.2.2 then ((103, s.2.1, s.2.2), none, 1)
       else (if b then ((33, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 105 then ((106, s.2.1, b), none, 1)
    else if s.1 = 106 then
      (if s.2.2 then ((105, s.2.1, s.2.2), none, 1)
       else (if b then ((37, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 107 then ((108, s.2.1, b), none, 1)
    else if s.1 = 108 then
      (if s.2.2 then ((107, s.2.1, s.2.2), none, 1)
       else (if b then ((53, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 109 then ((110, s.2.1, b), none, 1)
    else if s.1 = 110 then
      (if s.2.2 then ((109, s.2.1, s.2.2), none, 1)
       else (if b then ((59, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 111 then ((112, s.2.1, b), none, 1)
    else if s.1 = 112 then
      (if s.2.2 then ((111, s.2.1, s.2.2), none, 1)
       else (if b then ((75, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 113 then ((114, s.2.1, b), none, 1)
    else if s.1 = 114 then
      (if s.2.2 then ((113, s.2.1, s.2.2), none, 1)
       else (if b then ((83, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 115 then ((116, s.2.1, b), none, 1)
    else if s.1 = 116 then
      (if s.2.2 then ((115, s.2.1, s.2.2), none, 1)
       else (if b then ((94, s.2.1, s.2.2), none, 1) else ((96, s.2.1, s.2.2), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lp3p (body : List L3Instr) (t : List Bool) :
    init (loopProg3PMachine body) t
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl


/-! ## The step layer — phases 0–96 verbatim from the unprefixed machine -/

section Steps
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem q3_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .bit b) :
    run (loopProg3PMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(99, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3PMachine, moveHead, h, hp']

theorem q3_dispatch_spAo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spAo) :
    run (loopProg3PMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(101, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spAo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3PMachine, moveHead, h, hp']

theorem q3_dispatch_spCo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spCo) :
    run (loopProg3PMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(105, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spCo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3PMachine, moveHead, h, hp']

theorem q3_dispatch_spJo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spJo) :
    run (loopProg3PMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(109, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spJo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3PMachine, moveHead, h, hp']

theorem q3_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProg3PMachine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(113, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProg3PMachine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps3
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem q3_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(115, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipB1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossB1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipA1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(17, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphA1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(33, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(35, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipC1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(37, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(39, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipC2 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(39, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(41, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphC1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(53, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(55, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphC2 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(55, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(57, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipJr1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(59, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossJr1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(61, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipJr2 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(61, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossJr2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(63, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipJr3 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(63, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossJr3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(65, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphJ1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(75, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(77, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphJ2 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(77, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(79, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skiphJ3 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crosshJ3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(81, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipi1 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(83, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossi1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(85, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipi2 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossi2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(87, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipi3 (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(87, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossi3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(89, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanB2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanB3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(7, idx, s), p, T⟩
      = ⟨(7, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanB4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanB5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(21, idx, s), p, T⟩
      = ⟨(21, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanA4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(25, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanA5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanC3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(43, idx, s), p, T⟩
      = ⟨(43, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanC4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(45, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanC5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanJ4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(67, idx, s), p, T⟩
      = ⟨(67, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_scanJ5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3PMachine body) 2 ⟨(69, idx, s), p, T⟩
      = ⟨(69, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_crossSB2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSB3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSB4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSA4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(27, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSC3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSC4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(47, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_crossSJ4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2']

theorem q3_detectB5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q3_detectA5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q3_detectC5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(49, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q3_detectJ5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(71, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3PMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem q3_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(19, idx, s), p, T⟩
      = ⟨(21, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(103, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipCm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_markC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(41, idx, s), p, T⟩
      = ⟨(43, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneC (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(107, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(65, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(67, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(111, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(35, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2, h]

theorem q3_healC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneHealC (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2, h]

theorem q3_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(81, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2, h]

theorem q3_four_TA :
    run (loopProg3PMachine body) 4 ⟨(29, idx, s), p, T⟩
      = ⟨(101, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3PMachine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3PMachine body) ⟨(30, idx, s), p', T'⟩
      = ⟨(31, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3PMachine body) ⟨(31, idx, s), p', T'⟩
      = ⟨(32, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3PMachine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(101, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q3_four_TC :
    run (loopProg3PMachine body) 4 ⟨(49, idx, s), p, T⟩
      = ⟨(105, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3PMachine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3PMachine body) ⟨(50, idx, s), p', T'⟩
      = ⟨(51, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3PMachine body) ⟨(51, idx, s), p', T'⟩
      = ⟨(52, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3PMachine body) ⟨(52, idx, s), p', T'⟩
      = ⟨(105, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem q3_four_TJ :
    run (loopProg3PMachine body) 4 ⟨(71, idx, s), p, T⟩
      = ⟨(109, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3PMachine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3PMachine body) ⟨(72, idx, s), p', T'⟩
      = ⟨(73, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3PMachine body) ⟨(73, idx, s), p', T'⟩
      = ⟨(74, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3PMachine body) ⟨(74, idx, s), p', T'⟩
      = ⟨(109, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e1, e2, e3, e4]

/-- The append snoc: the instruction's bit doubled plus the closing marker; advance. -/
theorem q3_four_bit (h : idx.val + 1 < body.length + 1) :
    run (loopProg3PMachine body) 4 ⟨(13, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spJo).bitVal)
            (p + 1) (body.getD idx.val .spJo).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3PMachine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, s), p + 1, writeAt T p (body.getD idx.val .spJo).bitVal⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3PMachine body) ⟨(14, idx, s), p', T'⟩
      = ⟨(15, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spJo).bitVal⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3PMachine body) ⟨(15, idx, s), p', T'⟩
      = ⟨(16, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3PMachine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProg3PMachine, moveHead, h]
  rw [e1, e2, e3, e4]

theorem q3_walkI (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(89, idx, s), p, T⟩ = ⟨(89, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(89, idx, s), p, T⟩
      = ⟨(90, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg3PMachine, moveHead, h1']
  rw [e0]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_four_incr (h1 : T.getD p false = false) :
    run (loopProg3PMachine body) 4 ⟨(89, idx, s), p, T⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e89 : step (loopProg3PMachine body) ⟨(89, idx, s), p, T⟩
      = ⟨(91, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg3PMachine, moveHead, h1']
  have e91 : ∀ p' T', step (loopProg3PMachine body) ⟨(91, idx, s), p', T'⟩
      = ⟨(92, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e92 : ∀ p' T', step (loopProg3PMachine body) ⟨(92, idx, s), p', T'⟩
      = ⟨(93, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  have e93 : ∀ p' T', step (loopProg3PMachine body) ⟨(93, idx, s), p', T'⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e89, e91, e92, e93]

theorem q3_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3PMachine body) 2 ⟨(94, idx, s), p, T⟩
      = ⟨(94, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(94, idx, s), p, T⟩ = ⟨(96, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

end Steps3

/-! ### Scan run-invariants -/

theorem q3_skipBs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3PMachine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipB hk.1 hk.2]
    rfl

theorem q3_skipB1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipB1 (h k (by omega))]
    rfl

theorem q3_skipA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipA1 (h k (by omega))]
    rfl

theorem q3_skiphA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(33, idx, s), q, T⟩
      = ⟨(33, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphA1 (h k (by omega))]
    rfl

theorem q3_skipC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(37, idx, s), q, T⟩
      = ⟨(37, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipC1 (h k (by omega))]
    rfl

theorem q3_skipC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(39, idx, s), q, T⟩
      = ⟨(39, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipC2 (h k (by omega))]
    rfl

theorem q3_skiphC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(53, idx, s), q, T⟩
      = ⟨(53, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphC1 (h k (by omega))]
    rfl

theorem q3_skiphC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphC2 (h k (by omega))]
    rfl

theorem q3_skipJr1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipJr1 (h k (by omega))]
    rfl

theorem q3_skipJr2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(61, idx, s), q, T⟩
      = ⟨(61, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipJr2 (h k (by omega))]
    rfl

theorem q3_skipJr3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(63, idx, s), q, T⟩
      = ⟨(63, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipJr3 (h k (by omega))]
    rfl

theorem q3_skiphJ1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(75, idx, s), q, T⟩
      = ⟨(75, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphJ1 (h k (by omega))]
    rfl

theorem q3_skiphJ2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(77, idx, s), q, T⟩
      = ⟨(77, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphJ2 (h k (by omega))]
    rfl

theorem q3_skiphJ3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skiphJ3 (h k (by omega))]
    rfl

theorem q3_skipi1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(83, idx, s), q, T⟩
      = ⟨(83, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipi1 (h k (by omega))]
    rfl

theorem q3_skipi2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipi2 (h k (by omega))]
    rfl

theorem q3_skipi3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(87, idx, s), q, T⟩
      = ⟨(87, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipi3 (h k (by omega))]
    rfl

theorem q3_scanB2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanB2 (h k (by omega))]
    rfl

theorem q3_scanB3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanB3 (h k (by omega))]
    rfl

theorem q3_scanB4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanB4 (h k (by omega))]
    rfl

theorem q3_scanB5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanB5 (h k (by omega))]
    rfl

theorem q3_scanA2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanA2 (h k (by omega))]
    rfl

theorem q3_scanA3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanA3 (h k (by omega))]
    rfl

theorem q3_scanA4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanA4 (h k (by omega))]
    rfl

theorem q3_scanA5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanA5 (h k (by omega))]
    rfl

theorem q3_scanC3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanC3 (h k (by omega))]
    rfl

theorem q3_scanC4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanC4 (h k (by omega))]
    rfl

theorem q3_scanC5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(47, idx, s), q, T⟩
      = ⟨(47, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanC5 (h k (by omega))]
    rfl

theorem q3_scanJ4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanJ4 (h k (by omega))]
    rfl

theorem q3_scanJ5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3PMachine body) (2 * k) ⟨(69, idx, s), q, T⟩
      = ⟨(69, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_scanJ5 (h k (by omega))]
    rfl

theorem q3_skipAms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3PMachine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipAm hk.1 hk.2]
    rfl

theorem q3_skipCms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3PMachine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipCm hk.1 hk.2]
    rfl

theorem q3_skipJms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3PMachine body) (2 * k) ⟨(65, idx, s), q, T⟩
      = ⟨(65, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipJm hk.1 hk.2]
    rfl

theorem q3_walkIs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(89, idx, s), q, T⟩
      = ⟨(89, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_walkI (h k (by omega))]
    rfl


/-! ### The ten prefix-skip pairs -/

section StepsW
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem q3_skipWf (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(97, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(97, idx, s), p, T⟩ = ⟨(0, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(97, idx, s), p, T⟩
      = ⟨(98, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWb (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(99, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWb (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(99, idx, s), p, T⟩ = ⟨(3, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(99, idx, s), p, T⟩
      = ⟨(100, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWsa (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(101, idx, s), p, T⟩ = ⟨(101, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(101, idx, s), p, T⟩
      = ⟨(102, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWsa (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(101, idx, s), p, T⟩ = ⟨(17, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(101, idx, s), p, T⟩
      = ⟨(102, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWha (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(103, idx, s), p, T⟩ = ⟨(103, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(103, idx, s), p, T⟩
      = ⟨(104, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWha (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(103, idx, s), p, T⟩ = ⟨(33, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(103, idx, s), p, T⟩
      = ⟨(104, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWsc (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(105, idx, s), p, T⟩ = ⟨(105, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(105, idx, s), p, T⟩
      = ⟨(106, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWsc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(105, idx, s), p, T⟩ = ⟨(37, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(105, idx, s), p, T⟩
      = ⟨(106, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWhc (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(107, idx, s), p, T⟩ = ⟨(107, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(107, idx, s), p, T⟩
      = ⟨(108, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWhc (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(107, idx, s), p, T⟩ = ⟨(53, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(107, idx, s), p, T⟩
      = ⟨(108, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWsj (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(109, idx, s), p, T⟩ = ⟨(109, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(109, idx, s), p, T⟩
      = ⟨(110, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWsj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(109, idx, s), p, T⟩ = ⟨(59, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(109, idx, s), p, T⟩
      = ⟨(110, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWhj (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(111, idx, s), p, T⟩ = ⟨(111, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(111, idx, s), p, T⟩
      = ⟨(112, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWhj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(111, idx, s), p, T⟩ = ⟨(75, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(111, idx, s), p, T⟩
      = ⟨(112, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWi (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(113, idx, s), p, T⟩ = ⟨(113, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(113, idx, s), p, T⟩
      = ⟨(114, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWi (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(113, idx, s), p, T⟩ = ⟨(83, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(113, idx, s), p, T⟩
      = ⟨(114, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

theorem q3_skipWfin (h1 : T.getD p false = true) :
    run (loopProg3PMachine body) 2 ⟨(115, idx, s), p, T⟩ = ⟨(115, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(115, idx, s), p, T⟩
      = ⟨(116, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3PMachine, moveHead]; rfl

theorem q3_crossWfin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3PMachine body) 2 ⟨(115, idx, s), p, T⟩ = ⟨(94, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3PMachine body) ⟨(115, idx, s), p, T⟩
      = ⟨(116, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3PMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3PMachine, moveHead, h2]

end StepsW

/-! ### Prefix-skip scan invariants -/

theorem q3_skipWfs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(97, idx, s), q, T⟩
      = ⟨(97, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWf (h k (by omega))]
    rfl

theorem q3_skipWbs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(99, idx, s), q, T⟩
      = ⟨(99, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWb (h k (by omega))]
    rfl

theorem q3_skipWsas (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(101, idx, s), q, T⟩
      = ⟨(101, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWsa (h k (by omega))]
    rfl

theorem q3_skipWhas (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(103, idx, s), q, T⟩
      = ⟨(103, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWha (h k (by omega))]
    rfl

theorem q3_skipWscs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(105, idx, s), q, T⟩
      = ⟨(105, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWsc (h k (by omega))]
    rfl

theorem q3_skipWhcs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(107, idx, s), q, T⟩
      = ⟨(107, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWhc (h k (by omega))]
    rfl

theorem q3_skipWsjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(109, idx, s), q, T⟩
      = ⟨(109, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWsj (h k (by omega))]
    rfl

theorem q3_skipWhjs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(111, idx, s), q, T⟩
      = ⟨(111, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWhj (h k (by omega))]
    rfl

theorem q3_skipWis (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(113, idx, s), q, T⟩
      = ⟨(113, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWi (h k (by omega))]
    rfl

theorem q3_skipWfins (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3PMachine body) (2 * k) ⟨(115, idx, s), q, T⟩
      = ⟨(115, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), q3_skipWfin (h k (by omega))]
    rfl

/-! ### The prefixed heal walks -/

/-- The first-source heal (evolving `hlT`, two prefixes: grand bound, engine bound). -/
theorem q3_healAs (body : List L3Instr) (W P : List Bool) (G N a : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2) (idx : Fin (body.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ a) :
    run (loopProg3PMachine body) (2 * i)
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
      q3_healA h1 h2, hw]
    rfl

/-- The second-source heal (evolving `hlT`, three prefixes). -/
theorem q3_healCs (body : List L3Instr) (W P Q : List Bool) (G N a c : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2) (hQ : Q.length = 2 * a + 2)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ c) :
    run (loopProg3PMachine body) (2 * i)
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
      q3_healC h1 h2, hw]
    rfl

/-- The variable heal (evolving `jhT`, four prefixes). -/
theorem q3_healJs (body : List L3Instr) (W P Q R : List Bool) (G N a c k : ℕ)
    (E : List Bool) (hW : W.length = 2 * G + 2) (hP : P.length = 2 * N + 2)
    (hQ : Q.length = 2 * a + 2) (hR : R.length = 2 * c + 2) (hk : k ≤ N)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (loopProg3PMachine body) (2 * i)
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
      q3_healJ h1 h2, hw]
    rfl

/-- The bound heal (the finale, one prefix). -/
theorem q3_healBs (body : List L3Instr) (W : List Bool) (G v : ℕ) (E : List Bool)
    (hW : W.length = 2 * G + 2) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ)
    (hi : i ≤ v) :
    run (loopProg3PMachine body) (2 * i) ⟨(94, idx, s), 2 * G + 2, W ++ (hlT v 0 ++ E)⟩
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
      q3_healB h1 h2, hw]
    rfl

/-! ## The instruction lemmas

Round-`k` layout: `cntT G g ++ (cntT N (k+1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))`
— the grand prefix at `[0, 2G+2)`, then the engine's regions, output at `2G+4N+2a+2c+10`. -/

section Instr
variable {G g : ℕ}

/-- **An append instruction**, prefixed: dispatch, skip the grand prefix, skip the bound, four
boundary-event scans, snoc, advance. -/
theorem q3_instr_bit (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spJo = .bit b)
    (hg : g ≤ G) (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 17)
      ⟨(2, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
        ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ [b])))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq5 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (unaryD c).length + (jT N k).length = 2 * G + 4 * N + 2 * a + 2 * c + 10 := by
    rw [hW, hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have b0 := q3_dispatch_bit (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) h hp
  have b0a := q3_skipWbs body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    0 G idx s (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at b0a
  have b0b := q3_crossWb (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have b1 := q3_skipB1s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have b2 := q3_crossB1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have b3 := q3_scanB2s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD (2 * G + 2 + 2 * N + 2 + 2 * i) false
          = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
            from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
          = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
            from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1
          (cntE_data a 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b4 := q3_crossSB2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) (2 * G + 2 + 2 * N + 2) false a)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have b5 := q3_scanB3s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega,
          ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := q3_crossSB3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) (2 * G + 2 + 2 * N + 2 + 2 * a + 2) false c)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have b7 := q3_scanB4s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i))) from by omega,
          ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD OUT))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))))
            from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b8 := q3_crossSB4 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega,
        ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have b9 := q3_scanB5s body
    (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) ((N - k) + OUT.length)
    idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1)
            ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i))))
              from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i)
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1)
            ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2
                  + (2 * k + 2 + 2 * i + 1)))) from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD5_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
          (2 * G + 4 * N + 2 * a + 2 * c + 10) (i - (N - k)) hq5 (by omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2
      + 2 * ((N - k) + OUT.length)
      = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * OUT.length from by omega] at b9
  have b10 := q3_detectB5 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT)))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false
      ((N - k) + OUT.length))
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * OUT.length)
    (preD5_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
      (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5)
    (preD5_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
      (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5)
  have b11 := q3_four_bit (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * OUT.length)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))))
    (by omega)
  rw [hp] at b11
  simp only [L3Instr.bitVal] at b11
  rw [writes_snoc5 (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
    (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5 b] at b11
  rw [show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 17
      = 1 + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4)))))))))))) from by omega,
    run_add, b0, run_add, b0a, run_add, b0b, run_add, b1, run_add, b2, run_add, b3,
    run_add, b4, run_add, b5, run_add, b6, run_add, b7, run_add, b8, run_add, b9,
    run_add, b10, b11]

end Instr

/-! ### The open splice-A instruction, prefixed -/

section InstrA
variable {G g : ℕ}

/-- One prefixed splice-A sub-round: skip the grand prefix, mark the first source's pair `i`, seek
out through the second source, the variable, and the padding, emit a doubled `true`. -/
theorem q3_spa_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k i : ℕ) (hi : i < a) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 16)
      ⟨(101, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))⟩
      = ⟨(101, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (cntT a (i + 1) ++ (unaryD c ++ (jT N k
            ++ encodeD (OUT ++ List.replicate (i + 1) true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (cntT a (i + 1)).length = 2 * a + 2 := cntT_length a (i + 1) (by omega)
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq5 : (cntT G g).length + (cntT N (k + 1)).length + (cntT a (i + 1)).length
      + (unaryD c).length + (jT N k).length = 2 * G + 4 * N + 2 * a + 2 * c + 10 := by
    rw [hW, hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s0a := q3_skipWsas body (cntT G g ++ (cntT N (k + 1)
      ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))) 0 G
    idx s (fun i' hi' => by simpa using cntE_lo G g _ i' hg hi')
  simp only [Nat.zero_add] at s0a
  have s0b := q3_crossWsa (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have s1 := q3_skipA1s body (cntT G g ++ (cntT N (k + 1)
      ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2) N idx false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * i' = 2 * G + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i' (by omega) hi'))
  have s2 := q3_crossA1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have s3 := q3_skipAms body (cntT G g ++ (cntT N (k + 1)
      ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i' = 2 * G + 2 + (2 * N + 2 + 2 * i')
          from by omega]
      exact liftJ2 _ _ _ hW hR1 (cntE_mark_lo a i _ i' hi'), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i' + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i' + 1))
          from by omega]
      exact liftJ2 _ _ _ hW hR1 (cntE_mark_hi a i _ i' hi')⟩)
  have s4 := q3_markA (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * i)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega]
        exact liftJ2 _ _ _ hW hR1
          (cntE_data a i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hR1
          (cntE_data a i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * i + 1) false
      = cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
        from by omega,
      writeAt_append_right2 _ _ _ (2 * G + 2) (2 * N + 2) (2 * i + 1) false hW hR1
        (by rw [List.length_append, cntT_length a i (by omega)]; omega),
      cntT_mark a i _ hi]
  rw [hw] at s4
  have s5 := q3_scanA2s body (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * i + 2) (a - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * (i + 1) + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i') (by omega)
          (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * (i + 1) + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 2 + 2 * (a - i - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * a from by omega] at s5
  have s6 := q3_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * i + 2) true (a - i - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a (i + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a (i + 1) _ (by omega)))
  have s7 := q3_scanA3s body (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i')) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i' + 1))) from by omega,
          ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s8 := q3_crossSA3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2) false c)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have s9 := q3_scanA4s body (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i'))) from by omega,
          ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i' + 1))))
            from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s10 := q3_crossSA4 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega,
        ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have s11 := q3_scanA5s body (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2)
    ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i') false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i'))))
              from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i')
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2
                  + (2 * k + 2 + 2 * i' + 1)))) from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD5_data_eq (cntT G g) (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c)
          (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10)
          (i' - (N - k)) hq5 (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2
      + 2 * ((N - k) + (OUT.length + i))
      = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i) from by omega] at s11
  have hm1 := preD5_mark_lo (cntT G g) (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c)
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  have hm2 := preD5_mark_hi (cntT G g) (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c)
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  rw [hlen] at hm1 hm2
  have s12 := q3_detectA5 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false
      ((N - k) + (OUT.length + i)))
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc5 (cntT G g) (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c)
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := q3_four_TA (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i))
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
  rw [hsn] at s13
  rw [show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 16
      = 2 * G + (2 + (2 * N + (2 + (2 * i + (2 + (2 * (a - i - 1) + (2 + (2 * c + (2
          + (2 * k + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4)))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s1, run_add, s2, run_add, s3, run_add, s4,
    run_add, s5, run_add, s6, run_add, s7, run_add, s8, run_add, s9, run_add, s10,
    run_add, s11, run_add, s12, s13]

theorem q3_spa_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ a) (s : Bool) :
    run (loopProg3PMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j)
      ⟨(101, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (cntT a 0 ++ (unaryD c ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(101, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (cntT a j ++ (unaryD c ++ (jT N k
            ++ encodeD (OUT ++ List.replicate j true)))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j
            + (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j
        = 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 16 from by omega,
      run_add, ih (by omega), q3_spa_round body idx hg N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

end InstrA

def lp3paCost (G N a c L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * L + 16) a
    + ((2 * G + 2 * N + 2 * a + 6) + (2 * G + 2 * N + 2 * a + 6)))

section InstrA2
variable {G g : ℕ}

/-- **An open splice-A instruction**, prefixed: emit `1^a` from the first source (no closing
`false`), heal it, advance. -/
theorem q3_instr_spAo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spAo) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (lp3paCost G N a c OUT.length)
      ⟨(2, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
        ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have g0 := q3_dispatch_spAo (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) h hp
  have g1 := q3_spa_rounds body idx hg N a c k hk OUT a (le_refl a) s
  have g2a := q3_skipWsas body (cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) 0 G idx
    (if a = 0 then s else false) (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g2a
  have g2b := q3_crossWsa (body := body) (idx := idx)
    (s := if G = 0 then (if a = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g2 := q3_skipA1s body (cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g3 := q3_crossA1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g4 := q3_skipAms body (cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) (2 * G + 2 + 2 * N + 2)
    a idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega]
      exact liftJ2 _ _ _ hW hR1 (cntE_mark_lo a a _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i + 1 = 2 * G + 2 + (2 * N + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 _ _ _ hW hR1 (cntE_mark_hi a a _ i hi)⟩)
  have g5 := q3_doneA (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a a _ (le_refl a)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a a _ (le_refl a)))
  have g6a := q3_skipWhas body (cntT G g ++ (cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g6a
  have g6b := q3_crossWha (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g6 := q3_skiphA1s body (cntT G g ++ (cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g7 := q3_crosshA1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g8 := q3_healAs body (cntT G g) (cntT N (k + 1)) G N a
    (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))) hW hR1 idx false a
    (le_refl a)
  have g9 := q3_doneHealA (body := body) (idx := idx)
    (s := if a = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (hlT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (hlE_cm_lo a _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega]
        exact liftJ2 _ _ _ hW hR1 (hlE_cm_hi a _))
  rw [show lp3paCost G N a c OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) a
          + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * G + (2 + (2 * N + (2
              + (2 * a + 2))))))))))))
      from by simp only [lp3paCost]; omega,
    run_add, g0, ← cntT_zero a, run_add, g1, run_add, g2a, run_add, g2b, run_add, g2,
    run_add, g3, run_add, g4, run_add, g5, ← hlT_zero a, run_add, g6a, run_add, g6b,
    run_add, g6, run_add, g7, run_add, g8, g9, hlT_last, cntT_zero a]

end InstrA2

/-! ### The open splice-C instruction, prefixed -/

section InstrC
variable {G g : ℕ}

/-- One prefixed splice-C sub-round: skip the grand prefix, mark the second source's pair `i`, seek
out through the variable and the padding, emit a doubled `true`. -/
theorem q3_spc_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k i : ℕ) (hi : i < c) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 16)
      ⟨(105, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))⟩
      = ⟨(105, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (cntT c (i + 1) ++ (jT N k
            ++ encodeD (OUT ++ List.replicate (i + 1) true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (cntT c (i + 1)).length = 2 * c + 2 := cntT_length c (i + 1) (by omega)
  have hq5 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (cntT c (i + 1)).length + (jT N k).length = 2 * G + 4 * N + 2 * a + 2 * c + 10 := by
    rw [hW, hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s0a := q3_skipWscs body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))) 0 G
    idx s (fun i' hi' => by simpa using cntE_lo G g _ i' hg hi')
  simp only [Nat.zero_add] at s0a
  have s0b := q3_crossWsc (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have s1 := q3_skipC1s body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2) N idx false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * i' = 2 * G + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i' (by omega) hi'))
  have s2 := q3_crossC1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have s3 := q3_skipC2s body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i' hi' => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i' = 2 * G + 2 + (2 * N + 2 + 2 * i')
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i' (by omega) hi'))
  have s4 := q3_crossC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have s5 := q3_skipCms body (cntT G g ++ (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i'
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i')) from by omega]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_mark_lo c i _ i' hi'), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i' + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i' + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_mark_hi c i _ i' hi')⟩)
  have s6 := q3_markC (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa
          (cntE_data c i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1) false
      = cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega,
      writeAt_append_right3 _ _ _ _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * i + 1) false
        hW hR1 hQa (by rw [List.length_append, cntT_length c i (by omega)]; omega),
      cntT_mark c i _ hi]
  rw [hw] at s6
  have s7 := q3_scanC3s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2) (c - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * (i + 1) + 2 * i')))
            from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_data c (i + 1) _ (2 * (i + 1) + 2 * i')
          (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * (i + 1) + 2 * i' + 1)))
            from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_data c (i + 1) _ (2 * (i + 1) + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * (c - i - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c from by omega] at s7
  have s8 := q3_crossSC3 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 2) true (c - i - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c (i + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c (i + 1) _ (by omega)))
  have s9 := q3_scanC4s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i' hi' => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i') false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i'
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i'))) from by omega,
          ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i' + 1))))
            from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s10 := q3_crossSC4 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega,
        ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega, ← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have s11 := q3_scanC5s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2)
    ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i') false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i'))))
              from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i')
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2
                  + (2 * k + 2 + 2 * i' + 1)))) from by omega, ← jsT_zero N k]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD5_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (cntT c (i + 1))
          (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10)
          (i' - (N - k)) hq5 (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2
      + 2 * ((N - k) + (OUT.length + i))
      = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i) from by omega] at s11
  have hm1 := preD5_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (cntT c (i + 1))
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  have hm2 := preD5_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (cntT c (i + 1))
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  rw [hlen] at hm1 hm2
  have s12 := q3_detectC5 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false
      ((N - k) + (OUT.length + i)))
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc5 (cntT G g) (cntT N (k + 1)) (unaryD a) (cntT c (i + 1))
    (jT N k) (OUT ++ List.replicate i true) (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := q3_four_TC (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + i))
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))))
  rw [hsn] at s13
  rw [show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 16
      = 2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * i + (2 + (2 * (c - i - 1) + (2
          + (2 * k + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4)))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s1, run_add, s2, run_add, s3, run_add, s4,
    run_add, s5, run_add, s6, run_add, s7, run_add, s8, run_add, s9, run_add, s10,
    run_add, s11, run_add, s12, s13]

theorem q3_spc_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ c) (s : Bool) :
    run (loopProg3PMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j)
      ⟨(105, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (cntT c 0 ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(105, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (cntT c j ++ (jT N k
            ++ encodeD (OUT ++ List.replicate j true)))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j
            + (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j
        = 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 16 from by omega,
      run_add, ih (by omega), q3_spc_round body idx hg N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

end InstrC

def lp3pcCost (G N a c L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * L + 16) c
    + ((2 * G + 2 * N + 2 * a + 2 * c + 8) + (2 * G + 2 * N + 2 * a + 2 * c + 8)))

section InstrC2
variable {G g : ℕ}

/-- **An open splice-C instruction**, prefixed: emit `1^c` from the second source, heal it,
advance. -/
theorem q3_instr_spCo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spCo) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (lp3pcCost G N a c OUT.length)
      ⟨(2, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
        ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have g0 := q3_dispatch_spCo (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) h hp
  have g1 := q3_spc_rounds body idx hg N a c k hk OUT c (le_refl c) s
  have g2a := q3_skipWscs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) 0 G idx
    (if c = 0 then s else false) (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g2a
  have g2b := q3_crossWsc (body := body) (idx := idx)
    (s := if G = 0 then (if c = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g2 := q3_skipC1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g3 := q3_crossC1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g4 := q3_skipC2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) (2 * G + 2 + 2 * N + 2)
    a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g5 := q3_crossC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g6 := q3_skipCms body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_mark_lo c c _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_mark_hi c c _ i hi)⟩)
  have g7 := q3_doneC (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c c _ (le_refl c)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c c _ (le_refl c)))
  have g8a := q3_skipWhcs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g8a
  have g8b := q3_crossWhc (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g8 := q3_skiphC1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g9 := q3_crosshC1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g10 := q3_skiphC2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) (2 * G + 2 + 2 * N + 2)
    a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g11 := q3_crosshC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g12 := q3_healCs body (cntT G g) (cntT N (k + 1)) (unaryD a) G N a c
    (jT N k ++ encodeD (OUT ++ List.replicate c true)) hW hR1 hQa idx false c (le_refl c)
  have g13 := q3_doneHealC (body := body) (idx := idx)
    (s := if c = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (hlT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (hlE_cm_lo c _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega]
        exact liftJ3 _ _ _ _ hW hR1 hQa (hlE_cm_hi c _))
  rw [show lp3pcCost G N a c OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) c
          + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * G + (2
              + (2 * N + (2 + (2 * a + (2 + (2 * c + 2))))))))))))))))
      from by simp only [lp3pcCost]; omega,
    run_add, g0, ← cntT_zero c, run_add, g1, run_add, g2a, run_add, g2b, run_add, g2,
    run_add, g3, run_add, g4, run_add, g5, run_add, g6, run_add, g7, ← hlT_zero c,
    run_add, g8a, run_add, g8b, run_add, g8, run_add, g9, run_add, g10, run_add, g11,
    run_add, g12, g13, hlT_last, cntT_zero c]

end InstrC2

/-! ### The open splice-J instruction, prefixed -/

section InstrJ
variable {G g : ℕ}

/-- One prefixed splice-J sub-round: skip the grand prefix, mark the variable's pair `j'`, seek out
through the padding, emit a doubled `true`. -/
theorem q3_spj_round (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k j' : ℕ) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j' + 16)
      ⟨(109, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jsT N k j'
          ++ encodeD (OUT ++ List.replicate j' true)))))⟩
      = ⟨(109, idx, false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (unaryD c ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq5 : (cntT G g).length + (cntT N (k + 1)).length + (unaryD a).length
      + (unaryD c).length + (jsT N k (j' + 1)).length
      = 2 * G + 4 * N + 2 * a + 2 * c + 10 := by
    rw [hW, hR1, hQa, hQc, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have s0a := q3_skipWsjs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))) 0 G idx s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at s0a
  have s0b := q3_crossWsj (body := body) (idx := idx) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have s1 := q3_skipJr1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have s2 := q3_crossJr1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have s3 := q3_skipJr2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have s4 := q3_crossJr2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have s5 := q3_skipJr3s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have s6 := q3_crossJr3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have s7 := q3_skipJms body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i))) from by omega]
      exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_mark_hi N k j' _ i hi)⟩)
  have s8 := q3_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j')
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j'
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * j'))) from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * j' + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1) false
      = cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))) := by
    rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1
        = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * j' + 1))))
        from by omega,
      writeAt_append_right4 _ _ _ _ _ (2 * G + 2) (2 * N + 2) (2 * a + 2) (2 * c + 2)
        (2 * j' + 1) false hW hR1 hQa hQc
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at s8
  have s9 := q3_scanJ4s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i) false
          = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * (j' + 1) + 2 * i))))
            from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))).getD
          (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i + 1) false
          = true := by
        rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2
                + (2 * (j' + 1) + 2 * i + 1)))) from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
          (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1) (by omega) (by omega)
            (by omega))
      rw [e1, e2])
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k from by omega] at s9
  have s10 := q3_crossSJ4 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_hi N k (j' + 1) _ (by omega)))
  have s11 := q3_scanJ5s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2)
    ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i))))
              from by omega]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k (j' + 1) _
            (2 * k + 2 + 2 * i) (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))).getD
            (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1) false
            = false := by
          rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2
                  + (2 * k + 2 + 2 * i + 1)))) from by omega]
          exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_pad N k (j' + 1) _
            (2 * k + 2 + 2 * i + 1) (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) from by omega,
          show 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) + 1
            = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD5_data_eq (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c)
          (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
          (2 * G + 4 * N + 2 * a + 2 * c + 10) (i - (N - k)) hq5
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2
      + 2 * ((N - k) + (OUT.length + j'))
      = 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + j') from by omega] at s11
  have hm1 := preD5_mark_lo (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c)
    (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  have hm2 := preD5_mark_hi (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c)
    (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5
  rw [hlen] at hm1 hm2
  have s12 := q3_detectJ5 (body := body) (idx := idx)
    (s := storedD (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
      (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false
      ((N - k) + (OUT.length + j')))
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc5 (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c)
    (jsT N k (j' + 1)) (OUT ++ List.replicate j' true)
    (2 * G + 4 * N + 2 * a + 2 * c + 10) hq5 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true
      from by rw [← List.replicate_succ']] at hsn
  have s13 := q3_four_TJ (body := body) (idx := idx) (s := false)
    (p := 2 * G + 4 * N + 2 * a + 2 * c + 10 + 2 * (OUT.length + j'))
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))))
  rw [hsn] at s13
  rw [show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j' + 16
      = 2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * j' + (2
          + (2 * (k - j' - 1) + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4)))))))))))))
      from by omega,
    run_add, s0a, run_add, s0b, run_add, s1, run_add, s2, run_add, s3, run_add, s4,
    run_add, s5, run_add, s6, run_add, s7, run_add, s8, run_add, s9, run_add, s10,
    run_add, s11, run_add, s12, s13]

theorem q3_spj_rounds (body : List L3Instr) (idx : Fin (body.length + 1)) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k) (s : Bool) :
    run (loopProg3PMachine body)
      (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j)
      ⟨(109, idx, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jsT N k 0 ++ encodeD OUT))))⟩
      = ⟨(109, idx, if j = 0 then s else false), 0, cntT G g ++ (cntT N (k + 1)
          ++ (unaryD a ++ (unaryD c ++ (jsT N k j
            ++ encodeD (OUT ++ List.replicate j true)))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) (j + 1)
        = lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) j
            + (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j) from rfl,
      show 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16 + 2 * j
        = 2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 16 from by omega,
      run_add, ih (by omega), q3_spj_round body idx hg N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

end InstrJ

def lp3pjCost3 (G N a c k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * L + 16) k
    + ((2 * G + 2 * N + 2 * a + 2 * c + 2 * k + 10)
        + (2 * G + 2 * N + 2 * a + 2 * c + 2 * k + 10)))

section InstrJ2
variable {G g : ℕ}

/-- **An open splice-J instruction**, prefixed: emit `1^k` from the live variable, heal it,
advance. -/
theorem q3_instr_spJo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spJo) (hg : g ≤ G)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3PMachine body) (lp3pjCost3 G N a c k OUT.length)
      ⟨(2, idx, s), 0, cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
        ++ (jT N k ++ encodeD OUT))))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate k true)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have g0 := q3_dispatch_spJo (s := s) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD OUT))))) h hp
  have g1 := q3_spj_rounds body idx hg N a c k hk OUT k (le_refl k) s
  have g2a := q3_skipWsjs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))) 0 G idx
    (if k = 0 then s else false) (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g2a
  have g2b := q3_crossWsj (body := body) (idx := idx)
    (s := if G = 0 then (if k = 0 then s else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g2 := q3_skipJr1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g3 := q3_crossJr1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g4 := q3_skipJr2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g5 := q3_crossJr2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g6 := q3_skipJr3s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have g7 := q3_crossJr3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have g8 := q3_skipJms body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i))) from by omega]
      exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))))
          from by omega]
      exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_mark_hi N k k _ i hi)⟩)
  have g9 := q3_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_hi N k k _ (le_refl k)))
  have g10a := q3_skipWhjs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))) 0 G idx false
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at g10a
  have g10b := q3_crossWhj (body := body) (idx := idx) (s := if G = 0 then false else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have g10 := q3_skiphJ1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))) (2 * G + 2) N idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have g11 := q3_crosshJ1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have g12 := q3_skiphJ2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (2 * G + 2 + 2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g13 := q3_crosshJ2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g14 := q3_skiphJ3s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have g15 := q3_crosshJ3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have g16 := q3_healJs body (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c) G N a c k
    (encodeD (OUT ++ List.replicate k true)) hW hR1 hQa hQc (by omega) idx false k
    (le_refl k)
  have g17 := q3_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k k ++ encodeD (OUT ++ List.replicate k true)))))) (by omega)
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jhE_m_lo N k _))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))))
          from by omega]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jhE_m_hi N k _))
  rw [show lp3pjCost3 G N a c k OUT.length
      = 1 + (lp3SpRounds (2 * G + 4 * N + 2 * a + 2 * c + 2 * OUT.length + 16) k
          + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + (2 + (2 * G
              + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + 2))))))))))))))))))))
      from by simp only [lp3pjCost3]; omega,
    run_add, g0, ← jsT_zero, run_add, g1, run_add, g2a, run_add, g2b, run_add, g2,
    run_add, g3, run_add, g4, run_add, g5, run_add, g6, run_add, g7, run_add, g8,
    run_add, g9, ← jhT_zero, run_add, g10a, run_add, g10b, run_add, g10, run_add, g11,
    run_add, g12, run_add, g13, run_add, g14, run_add, g15, run_add, g16, g17, jhT_last,
    jsT_zero]

end InstrJ2

/-! ## The instruction segment, the round, and the loop -/

def lp3pInstrCost (body : List L3Instr) (G N a c k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n .spJo with
  | .bit _ => 2 * G + 4 * N + 2 * a + 2 * c + 2 * (L + (prog3OutN body a c k n).length) + 17
  | .spAo => lp3paCost G N a c (L + (prog3OutN body a c k n).length)
  | .spCo => lp3pcCost G N a c (L + (prog3OutN body a c k n).length)
  | .spJo => lp3pjCost3 G N a c k (L + (prog3OutN body a c k n).length)

def lp3pSegN (body : List L3Instr) (G N a c k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lp3pSegN body G N a c k L n + lp3pInstrCost body G N a c k L n

/-- **The segment invariant**, prefixed. -/
theorem q3_run_instrs (body : List L3Instr) (G g : ℕ) (hg : g ≤ G) (N a c k : ℕ)
    (hk : k < N) (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (loopProg3PMachine body) (lp3pSegN body G N a c k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G g ++ (cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out'))))⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k n)))))⟩ := by
  induction n with
  | zero => simp only [lp3pSegN]; rw [run_zero]; simp [prog3OutN]
  | succ n ih =>
    rw [show lp3pSegN body G N a c k out'.length (n + 1)
        = lp3pSegN body G N a c k out'.length n + lp3pInstrCost body G N a c k out'.length n
        from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n .spJo with
    | bit b =>
      have hin := q3_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N a c k hk
        (out' ++ prog3OutN body a c k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ [b] = prog3OutN body a c k (n + 1) from by
          simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3pInstrCost, hp]
      rw [hin]
      simp
    | spAo =>
      have hin := q3_instr_spAo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N a c k hk
        (out' ++ prog3OutN body a c k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate a true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3pInstrCost, hp]
      rw [hin]
      simp
    | spCo =>
      have hin := q3_instr_spCo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N a c k hk
        (out' ++ prog3OutN body a c k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate c true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3pInstrCost, hp]
      rw [hin]
      simp
    | spJo =>
      have hin := q3_instr_spJo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp hg N a c k hk
        (out' ++ prog3OutN body a c k n) (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate k true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3pInstrCost, hp]
      rw [hin]
      simp

def lp3pRoundCost (body : List L3Instr) (G N a c k L : ℕ) : ℕ :=
  (2 * G + 2 * k + 4) + (lp3pSegN body G N a c k L body.length
    + (2 * G + 2 * N + 2 * a + 2 * c + 2 * k + 13))

/-- **One loop round**, prefixed. -/
theorem q3_round (body : List L3Instr) (G g : ℕ) (hg : g ≤ G) (N a c k : ℕ) (hk : k < N)
    (out' : List Bool) (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (loopProg3PMachine body) (lp3pRoundCost body G N a c k out'.length)
      ⟨(97, ptrIn, s), 0, cntT G g ++ (cntT N k
        ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out'))))⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N (k + 1)
            ++ encodeD (out' ++ prog3Out body a c k)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have r0a := q3_skipWfs body (cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD out'))))) 0 G ptrIn s
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at r0a
  have r0b := q3_crossWf (body := body) (idx := ptrIn) (s := if G = 0 then s else true)
    (p := 2 * G)
    (T := cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out')))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r1 := q3_skipBs body (cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD out'))))) (2 * G + 2) k ptrIn false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo N k _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi N k _ i hi)⟩)
  have r2 := q3_markB (body := body) (idx := ptrIn) (s := if k = 0 then false else true)
    (p := 2 * G + 2 + 2 * k)
    (T := cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out')))))
    (by rw [show 2 * G + 2 + 2 * k = 2 * G + 2 + (2 * k) from rfl]
        exact liftJ _ _ hW (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G + 2 + 2 * k + 1 = 2 * G + 2 + (2 * k + 1) from by omega]
        exact liftJ _ _ hW (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD out'))))) (2 * G + 2 + 2 * k + 1) false
      = cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jT N k ++ encodeD out')))) := by
    rw [show 2 * G + 2 + 2 * k + 1 = 2 * G + 2 + (2 * k + 1) from by omega,
      writeAt_append_right _ _ (2 * G + 2) (2 * k + 1) false hW
        (by rw [List.length_append, cntT_length N k (by omega)]; omega),
      cntT_mark N k _ hk]
  rw [hwm] at r2
  have r3 := q3_run_instrs body G g hg N a c k hk out' body.length (le_refl _) true
  have r4 := q3_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (Nat.lt_irrefl _)
  have r4a := q3_skipWis body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))) 0 G
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at r4a
  have r4b := q3_crossWi (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if G = 0 then (if body.length = 0 then true else false) else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have r5 := q3_skipi1s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))) (2 * G + 2) N
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_lo N (k + 1) _ i (by omega) hi))
  have r6 := q3_crossi1 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N (k + 1) _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N (k + 1) _ (by omega)))
  have r7 := q3_skipi2s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (2 * G + 2 + 2 * N + 2) a ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * i = 2 * G + 2 + (2 * N + 2 + 2 * i)
          from by omega, ← cntT_zero a]
      exact liftJ2 _ _ _ hW hR1 (cntE_lo a 0 _ i (by omega) hi))
  have r8 := q3_crossi2 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if a = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * a)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a = 2 * G + 2 + (2 * N + 2 + 2 * a)
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 1 = 2 * G + 2 + (2 * N + 2 + (2 * a + 1))
          from by omega, ← cntT_zero a]
        exact liftJ2 _ _ _ hW hR1 (cntE_cm_hi a 0 _ (by omega)))
  have r9 := q3_skipi3s body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2) c ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * i)) from by omega, ← cntT_zero c]
      exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have r10 := q3_crossi3 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if c = 0 then false else true) (p := 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + 2 * c)) from by omega, ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 1
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 1))) from by omega,
        ← cntT_zero c]
        exact liftJ3 _ _ _ _ hW hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have r11 := q3_walkIs body (cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2) k
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i))) from by omega,
        ← jsT_zero N k]
      exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc
        (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r12 := q3_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))))
    (T := cntT G g ++ (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))))
    (by rw [← jsT_zero N k]
        exact liftJ4 _ _ _ _ _ hW hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right4 (cntT G g) (cntT N (k + 1)) (unaryD a) (unaryD c)
      (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)) (2 * G + 2)
      (2 * N + 2) (2 * a + 2) (2 * c + 2) (2 * k) true true false true hW hR1 hQa hQc
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r12
  rw [show lp3pRoundCost body G N a c k out'.length
      = 2 * G + (2 + (2 * k + (2 + (lp3pSegN body G N a c k out'.length body.length + (1
          + (2 * G + (2 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + 4))))))))))))))
      from by simp only [lp3pRoundCost]; omega,
    run_add, r0a, run_add, r0b, run_add, r1, run_add, r2, run_add, r3, run_add, r4,
    run_add, r4a, run_add, r4b, run_add, r5, run_add, r6, run_add, r7, run_add, r8,
    run_add, r9, run_add, r10, run_add, r11,
    show 2 * G + 2 + 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
      = 2 * G + 2 + (2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k))) from by omega,
    r12, prog3Out]

def lp3pClockN (body : List L3Instr) (G N a c Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lp3pClockN body G N a c Lout k
      + lp3pRoundCost body G N a c k (Lout + (loop3OutN body a c k).length)

/-- **The rounds invariant**, prefixed. -/
theorem q3_run_rounds (body : List L3Instr) (G g : ℕ) (hg : g ≤ G) (N a c : ℕ)
    (out : List Bool) (k : ℕ) (hk : k ≤ N) (s : Bool) :
    run (loopProg3PMachine body) (lp3pClockN body G N a c out.length k)
      ⟨(97, ⟨0, Nat.succ_pos _⟩, s), 0, cntT G g ++ (cntT N 0
        ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))))⟩
      = ⟨(97, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT G g ++ (cntT N k ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (out ++ loop3OutN body a c k)))))⟩ := by
  induction k with
  | zero => simp only [lp3pClockN]; rw [run_zero]; simp [loop3OutN]
  | succ k ih =>
    have hrd := q3_round body G g hg N a c k (by omega) (out ++ loop3OutN body a c k)
      ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loop3OutN body a c k ++ prog3Out body a c k = loop3OutN body a c (k + 1)
        from rfl] at hrd
    rw [show lp3pClockN body G N a c out.length (k + 1)
        = lp3pClockN body G N a c out.length k
            + lp3pRoundCost body G N a c k (out.length + (loop3OutN body a c k).length)
        from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

def lp3pClock (body : List L3Instr) (G N a c Lout : ℕ) : ℕ :=
  lp3pClockN body G N a c Lout N
    + (2 * G + (2 + (2 * N + (2 + (2 * G + (2 + (2 * N + 2)))))))

/-- **THE PREFIXED TRIPLE-SOURCE LOOP ENGINE RUNS TO COMPLETION** — the prefix preserved verbatim,
the `rep_run` hypothesis shape. -/
theorem loopProg3P_run (body : List L3Instr) (G g : ℕ) (hg : g ≤ G) (N a c : ℕ)
    (out : List Bool) :
    run (loopProg3PMachine body) (lp3pClock body G N a c out.length)
      (init (loopProg3PMachine body)
        (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * N + 1,
          cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
            ++ (unaryD N ++ encodeD (out ++ loop3Out body a c N)))))⟩ := by
  have hW : (cntT G g).length = 2 * G + 2 := cntT_length G g hg
  rw [init_lp3p]
  rw [show (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))))
        : List Bool)
      = cntT G g ++ (cntT N 0 ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))))
      from by rw [cntT_zero]]
  simp only [lp3pClock]
  have f0a := q3_skipWfs body (cntT G g ++ (cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))))) 0 G
    ⟨0, Nat.succ_pos _⟩ false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f0a
  have f0b := q3_crossWf (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f1 := q3_skipBs body (cntT G g ++ (cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))))) (2 * G + 2) N
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW (cntE_mark_lo N N _ i hi), by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hW (cntE_mark_hi N N _ i hi)⟩)
  have f2 := q3_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (cntE_cm_lo N N _ (le_refl N)))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (cntE_cm_hi N N _ (le_refl N)))
  have f3a := q3_skipWfins body (cntT G g ++ (hlT N 0 ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))))) 0 G
    ⟨0, Nat.succ_pos _⟩ false (fun i hi => by simpa using cntE_lo G g _ i hg hi)
  simp only [Nat.zero_add] at f3a
  have f3b := q3_crossWfin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if G = 0 then false else true) (p := 2 * G)
    (T := cntT G g ++ (hlT N 0 ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))))
    (cntE_cm_lo G g _ hg) (cntE_cm_hi G g _ hg)
  have f4 := q3_healBs body (cntT G g) G N
    (unaryD a ++ (unaryD c ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))) hW
    ⟨0, Nat.succ_pos _⟩ false N (le_refl N)
  have f5 := q3_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * G + 2 + 2 * N)
    (T := cntT G g ++ (hlT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))))
    (by rw [show 2 * G + 2 + 2 * N = 2 * G + 2 + (2 * N) from rfl]
        exact liftJ _ _ hW (hlE_cm_lo N _))
    (by rw [show 2 * G + 2 + 2 * N + 1 = 2 * G + 2 + (2 * N + 1) from by omega]
        exact liftJ _ _ hW (hlE_cm_hi N _))
  rw [run_add, q3_run_rounds body G g hg N a c out N (le_refl N) false, ite_self,
    run_add, f0a, run_add, f0b, run_add, f1, run_add, f2, ← hlT_zero, run_add, f3a,
    run_add, f3b, run_add, f4, f5, hlT_last, jT_full,
    show loop3Out body a c N = loop3OutN body a c N from rfl]

/-- The machine **halts by itself** at its clock. -/
theorem loopProg3P_halted (body : List L3Instr) (G g : ℕ) (hg : g ≤ G) (N a c : ℕ)
    (out : List Bool) :
    (loopProg3PMachine body).halt
      (run (loopProg3PMachine body) (lp3pClock body G N a c out.length)
        (init (loopProg3PMachine body)
          (cntT G g ++ (unaryD N ++ (unaryD a ++ (unaryD c
            ++ (jT N 0 ++ encodeD out))))))).st = true := by
  rw [loopProg3P_run body G g hg N a c out]; rfl

/-! ## Polynomial clock bounds -/

/-- The per-instruction cap. -/
def lp3pCap (G N a c LM : ℕ) : ℕ :=
  N * (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16 + 2 * N)
    + a * (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16 + 2 * a)
    + c * (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16 + 2 * c)
    + (4 * G + 4 * N + 4 * a + 25) + (4 * G + 4 * N + 4 * a + 4 * c + 33)
    + (4 * G + 8 * N + 4 * a + 4 * c + 41)
    + (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 17)

theorem lp3pInstrCost_le (body : List L3Instr) (G N a c k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3pInstrCost body G N a c k L n ≤ lp3pCap G N a c LM := by
  have hlen : (prog3OutN body a c k n).length ≤ body.length * (a + c + N + 1) :=
    le_trans (prog3OutN_length_le body a c k n) (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n .spJo with
  | bit b =>
    simp only [lp3pInstrCost, hp, lp3pCap]
    omega
  | spAo =>
    have h1 := lp3SpRounds_le (2 * G + 4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 16)
      (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16) a a (by omega) (le_refl a)
    simp only [lp3pInstrCost, hp, lp3paCost, lp3pCap]
    omega
  | spCo =>
    have h1 := lp3SpRounds_le (2 * G + 4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 16)
      (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16) c c (by omega) (le_refl c)
    simp only [lp3pInstrCost, hp, lp3pcCost, lp3pCap]
    omega
  | spJo =>
    have h1 := lp3SpRounds_le (2 * G + 4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 16)
      (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16) k N (by omega) (by omega)
    have h2 : k * (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16 + 2 * N)
        ≤ N * (2 * G + 4 * N + 2 * a + 2 * c + 2 * LM + 16 + 2 * N) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [lp3pInstrCost, hp, lp3pjCost3, lp3pCap]
    omega

theorem lp3pSegN_le (body : List L3Instr) (G N a c k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3pSegN body G N a c k L n ≤ n * lp3pCap G N a c LM := by
  induction n with
  | zero => simp [lp3pSegN]
  | succ n ih =>
    calc lp3pSegN body G N a c k L (n + 1)
        = lp3pSegN body G N a c k L n + lp3pInstrCost body G N a c k L n := rfl
      _ ≤ n * lp3pCap G N a c LM + lp3pCap G N a c LM :=
          Nat.add_le_add (ih (by omega))
            (lp3pInstrCost_le body G N a c k L n LM hk (by omega) hL)
      _ = (n + 1) * lp3pCap G N a c LM := by ring

theorem lp3pRoundCost_le (body : List L3Instr) (G N a c k L LM : ℕ) (hk : k < N)
    (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3pRoundCost body G N a c k L
      ≤ body.length * lp3pCap G N a c LM + (4 * G + 6 * N + 2 * a + 2 * c + 17) := by
  have h := lp3pSegN_le body G N a c k L body.length LM hk (le_refl _) hL
  simp only [lp3pRoundCost]
  omega

/-- **The prefixed loop clock is polynomial.** -/
theorem lp3pClock_le (body : List L3Instr) (G N a c Lout : ℕ) :
    lp3pClock body G N a c Lout
      ≤ N * (body.length * lp3pCap G N a c (Lout + N * (body.length * (a + c + N + 1))
            + body.length * (a + c + N + 1)) + (4 * G + 6 * N + 2 * a + 2 * c + 17))
        + (4 * G + 4 * N + 8) := by
  have hrounds : ∀ k, k ≤ N → lp3pClockN body G N a c Lout k
      ≤ k * (body.length * lp3pCap G N a c (Lout + N * (body.length * (a + c + N + 1))
            + body.length * (a + c + N + 1)) + (4 * G + 6 * N + 2 * a + 2 * c + 17)) := by
    intro k hk
    induction k with
    | zero => simp [lp3pClockN]
    | succ k ih =>
      have hLk : (Lout + (loop3OutN body a c k).length)
          + body.length * (a + c + N + 1)
          ≤ Lout + N * (body.length * (a + c + N + 1))
              + body.length * (a + c + N + 1) := by
        have h1 : (loop3OutN body a c k).length
            ≤ k * (body.length * (a + c + N + 1)) :=
          loop3OutN_length_le body N a c k (by omega)
        have h2 : k * (body.length * (a + c + N + 1))
            ≤ N * (body.length * (a + c + N + 1)) := Nat.mul_le_mul_right _ (by omega)
        omega
      calc lp3pClockN body G N a c Lout (k + 1)
          = lp3pClockN body G N a c Lout k
              + lp3pRoundCost body G N a c k (Lout + (loop3OutN body a c k).length) := rfl
        _ ≤ k * (body.length * lp3pCap G N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1)) + (4 * G + 6 * N + 2 * a + 2 * c + 17))
            + (body.length * lp3pCap G N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1))
              + (4 * G + 6 * N + 2 * a + 2 * c + 17)) :=
            Nat.add_le_add (ih (by omega))
              (lp3pRoundCost_le body G N a c k (Lout + (loop3OutN body a c k).length) _
                (by omega) hLk)
        _ = (k + 1) * (body.length
              * lp3pCap G N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1))
              + (4 * G + 6 * N + 2 * a + 2 * c + 17)) := by ring
  have h := hrounds N (le_refl N)
  simp only [lp3pClock]
  omega

/-! ## THE PREFIXED PAIR-ROW DEMONSTRATIONS -/

/-- **The at-most-one pair row under the grand bound** (head one-hot): the prefixed engine emits
the whole row `(i, j)` for `j = i+1..i+R` at time `t`, the grand prefix preserved verbatim — the
exact per-round shape `rep_run` consumes. -/
theorem amoPairHeadP_family_run (G g : ℕ) (hg : g ≤ G) (t i R : ℕ) (out : List Bool) :
    run (loopProg3PMachine amoPairHeadBody) (lp3pClock amoPairHeadBody G R t i out.length)
      (init (loopProg3PMachine amoPairHeadBody)
        (cntT G g ++ (unaryD R ++ (unaryD t ++ (unaryD i ++ (jT R 0 ++ encodeD out))))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * R + 1,
          cntT G g ++ (unaryD R ++ (unaryD t ++ (unaryD i ++ (unaryD R ++ encodeD (out
            ++ ((List.range R).map (fun d =>
                encodeClause' [(headVar t i, false),
                  (headVar t (i + 1 + d), false)])).flatten)))))⟩ := by
  have h := loopProg3P_run amoPairHeadBody G g hg R t i out
  rwa [amoPairHead_split] at h

theorem amoPairStateP_family_run (G g : ℕ) (hg : g ≤ G) (t i R : ℕ) (out : List Bool) :
    run (loopProg3PMachine amoPairStateBody)
      (lp3pClock amoPairStateBody G R t i out.length)
      (init (loopProg3PMachine amoPairStateBody)
        (cntT G g ++ (unaryD R ++ (unaryD t ++ (unaryD i ++ (jT R 0 ++ encodeD out))))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * G + 2 + 2 * R + 1,
          cntT G g ++ (unaryD R ++ (unaryD t ++ (unaryD i ++ (unaryD R ++ encodeD (out
            ++ ((List.range R).map (fun d =>
                encodeClause' [(stateVar t i, false),
                  (stateVar t (i + 1 + d), false)])).flatten)))))⟩ := by
  have h := loopProg3P_run amoPairStateBody G g hg R t i out
  rwa [amoPairState_split] at h
end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3P
