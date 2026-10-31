import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitLoopProg

/-!
# Cook–Levin M2 emitter — the two-source looped program emitter, and the first looped family

The final mechanism of the emitter toolkit.  `loopProg2Machine body` runs

    for k in 0..N-1:  execute `body`,

where `body : List LInstr` executes against **two** splice sources: `.bit b` appends the bit `b`;
`.spliceA` splices the **static source region's value** `a` (a counter frozen for the whole loop — at
nesting time, the outer loop's live variable); `.spliceJ` splices the **live round index** `k`.  Layout:
`cntT N k ++ (unaryD a ++ (jT N k ++ encodeD out))` — bound, static source, live variable, output.  The
static source is spliced by the E1/E3 marking discipline (`cntT a i` marks, `hlT` heal); the live
variable by the E4-ii `jsT`/`jhT` discipline; rounds end with the in-place increment (`jT_incr`).

**Top theorem** (`loopProg2_run`): from `unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out))` the machine
halts by itself at the explicit polynomial clock with tape **exactly**
`unaryD N ++ (unaryD a ++ (unaryD N ++ encodeD (out ++ loop2Out body a N)))` — the two-source denotation
appended, bound healed, source untouched, variable saturated.

**THE FIRST LOOPED FAMILY EMITTER** falls out: the head one-hot at-least-one clause at time `t` is
`encodeNat (P+1) ++ (for p in 0..P: encodeNat t · encodeNat p · encodeNat 1 · [true])`
(`encodeClause'_atLeastOne_head` of `...EmitTemplates`).  Its per-iteration stream is the five-instruction
body `[.spliceA, .spliceJ, .bit true, .bit false, .bit true]`; `aloHead_split` factors the clause as
`encodeNat (P+1) ++ loop2Out aloHeadBody t (P+1)`, and `aloHead_family_run` runs the machine — an actual
`ComposableMachine` emits the clause's whole literal stream with `t` read from the source region and `p`
from the live variable.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg

/-! ## The two-source instruction set and its denotation -/

/-- A two-source emitter instruction: a fixed bit, a splice of the static source, or a splice of the
live loop variable. -/
inductive LInstr where
  | bit (b : Bool)
  | spliceA
  | spliceJ
deriving DecidableEq

/-- The bit an append instruction writes (junk `false` on the splice kinds — never consulted there). -/
def LInstr.bitVal : LInstr → Bool
  | .bit b => b
  | _ => false

/-- One instruction's output at source value `a`, round index `k`. -/
def instr2Out (a k : ℕ) : LInstr → List Bool
  | .bit b => [b]
  | .spliceA => encodeNat a
  | .spliceJ => encodeNat k

/-- The first `n` instructions' output. -/
def prog2OutN (body : List LInstr) (a k : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => prog2OutN body a k n ++ instr2Out a k (body.getD n .spliceJ)

/-- The whole body's output at round `k`. -/
def prog2Out (body : List LInstr) (a k : ℕ) : List Bool := prog2OutN body a k body.length

/-- The first `k` rounds' output. -/
def loop2OutN (body : List LInstr) (a : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => loop2OutN body a k ++ prog2Out body a k

/-- The whole loop's output. -/
def loop2Out (body : List LInstr) (a N : ℕ) : List Bool := loop2OutN body a N

/-- The mapped form consumed by the template layouts. -/
theorem loop2Out_eq_flatten (body : List LInstr) (a N : ℕ) :
    loop2Out body a N = ((List.range N).map (fun k => prog2Out body a k)).flatten := by
  show loop2OutN body a N = _
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show loop2OutN body a (N + 1) = loop2OutN body a N ++ prog2Out body a N from rfl, ih,
      List.range_succ, List.map_append, List.flatten_append]
    simp

theorem prog2OutN_length_le (body : List LInstr) (a k n : ℕ) :
    (prog2OutN body a k n).length ≤ n * (a + k + 1) := by
  induction n with
  | zero => simp [prog2OutN]
  | succ n ih =>
    rw [show prog2OutN body a k (n + 1)
        = prog2OutN body a k n ++ instr2Out a k (body.getD n .spliceJ) from rfl,
      List.length_append]
    have hone : (instr2Out a k (body.getD n .spliceJ)).length ≤ a + k + 1 := by
      cases body.getD n .spliceJ with
      | bit b => simp [instr2Out]
      | spliceA => rw [show instr2Out a k .spliceA = encodeNat a from rfl, encodeNat_length]; omega
      | spliceJ => rw [show instr2Out a k .spliceJ = encodeNat k from rfl, encodeNat_length]; omega
    calc (prog2OutN body a k n).length + (instr2Out a k (body.getD n .spliceJ)).length
        ≤ n * (a + k + 1) + (a + k + 1) := Nat.add_le_add ih hone
      _ = (n + 1) * (a + k + 1) := by ring

/-! ## A four-write lift under two prefixes -/

theorem W4_append_right2 (A C X : List Bool) (qa qc p : ℕ) (b1 b2 b3 b4 : Bool)
    (ha : A.length = qa) (hc : C.length = qc) (hp : p + 3 < X.length) :
    writeAt (writeAt (writeAt (writeAt (A ++ (C ++ X)) (qa + (qc + p)) b1)
        (qa + (qc + p) + 1) b2) (qa + (qc + p) + 2) b3) (qa + (qc + p) + 3) b4
      = A ++ (C ++ writeAt (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3)
          (p + 3) b4) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  have hl2 : (writeAt (writeAt X p b1) (p + 1) b2).length = X.length := by
    rw [writeAt_of_lt b2 (by omega), List.length_set, hl1]
  have hl3 : (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3).length = X.length := by
    rw [writeAt_of_lt b3 (by omega), List.length_set, hl2]
  rw [writeAt_append_right2 A C X qa qc p b1 ha hc (by omega),
    show qa + (qc + p) + 1 = qa + (qc + (p + 1)) from by omega,
    writeAt_append_right2 A C _ qa qc (p + 1) b2 ha hc (by rw [hl1]; omega),
    show qa + (qc + p) + 2 = qa + (qc + (p + 2)) from by omega,
    writeAt_append_right2 A C _ qa qc (p + 2) b3 ha hc (by rw [hl2]; omega),
    show qa + (qc + p) + 3 = qa + (qc + (p + 3)) from by omega,
    writeAt_append_right2 A C _ qa qc (p + 3) b4 ha hc (by rw [hl3]; omega)]

/-! ## The machine

Control: `Fin 79 × Fin (|body|+1) × Bool`.  Phase groups: `0/1` the loop find, `2` the three-way
dispatch, `3–14` the append track (skip the bound, three boundary-event scans across source / variable /
padding+output, snoc, advance), `15–40` the splice-J track (skip bound and source, mark the variable,
two-event seek, snoc; closing `false`, heal walk, advance), `41–66` the splice-A track (skip the bound,
mark the source, **three**-event seek, snoc; closing `false`, heal, advance), `67–75` the in-place
increment, `76/77` heal the bound, `78` = halt. -/

def loopProg2Machine (body : List LInstr) : Machine where
  State := Fin 79 × Fin (body.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 78)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 3)
         else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((76, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val .spliceJ with
         | .bit _ => ((3, s.2.1, s.2.2), none, 2)
         | .spliceA => ((41, s.2.1, s.2.2), none, 2)
         | .spliceJ => ((15, s.2.1, s.2.2), none, 2))
       else ((67, s.2.1, s.2.2), none, 2))
    else if s.1 = 3 then ((4, s.2.1, b), none, 1)
    else if s.1 = 4 then
      (if s.2.2 then ((3, s.2.1, s.2.2), none, 1)
       else (if b then ((5, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 5 then ((6, s.2.1, b), none, 1)
    else if s.1 = 6 then
      (if b = s.2.2 then ((5, s.2.1, s.2.2), none, 1) else ((7, s.2.1, s.2.2), none, 1))
    else if s.1 = 7 then ((8, s.2.1, b), none, 1)
    else if s.1 = 8 then
      (if b = s.2.2 then ((7, s.2.1, s.2.2), none, 1) else ((9, s.2.1, s.2.2), none, 1))
    else if s.1 = 9 then ((10, s.2.1, b), none, 1)
    else if s.1 = 10 then
      (if b = s.2.2 then ((9, s.2.1, s.2.2), none, 1) else ((11, s.2.1, s.2.2), none, 0))
    else if s.1 = 11 then
      ((12, s.2.1, s.2.2), some (body.getD s.2.1.val .spliceJ).bitVal, 1)
    else if s.1 = 12 then
      ((13, s.2.1, s.2.2), some (body.getD s.2.1.val .spliceJ).bitVal, 1)
    else if s.1 = 13 then ((14, s.2.1, s.2.2), some false, 1)
    else if s.1 = 14 then
      (if h : s.2.1.val + 1 < body.length + 1 then
        ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), some true, 3)
       else ((78, s.2.1, s.2.2), some true, 2))
    else if s.1 = 15 then ((16, s.2.1, b), none, 1)
    else if s.1 = 16 then
      (if s.2.2 then ((15, s.2.1, s.2.2), none, 1)
       else (if b then ((17, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 17 then ((18, s.2.1, b), none, 1)
    else if s.1 = 18 then
      (if s.2.2 then ((17, s.2.1, s.2.2), none, 1)
       else (if b then ((19, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 19 then ((20, s.2.1, b), none, 1)
    else if s.1 = 20 then
      (if s.2.2 then
        (if b then ((21, s.2.1, s.2.2), some false, 1) else ((19, s.2.1, s.2.2), none, 1))
       else (if b then ((29, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 21 then ((22, s.2.1, b), none, 1)
    else if s.1 = 22 then
      (if b = s.2.2 then ((21, s.2.1, s.2.2), none, 1) else ((23, s.2.1, s.2.2), none, 1))
    else if s.1 = 23 then ((24, s.2.1, b), none, 1)
    else if s.1 = 24 then
      (if b = s.2.2 then ((23, s.2.1, s.2.2), none, 1) else ((25, s.2.1, s.2.2), none, 0))
    else if s.1 = 25 then ((26, s.2.1, s.2.2), some true, 1)
    else if s.1 = 26 then ((27, s.2.1, s.2.2), some true, 1)
    else if s.1 = 27 then ((28, s.2.1, s.2.2), some false, 1)
    else if s.1 = 28 then ((15, s.2.1, s.2.2), some true, 3)
    else if s.1 = 29 then ((30, s.2.1, b), none, 1)
    else if s.1 = 30 then
      (if b = s.2.2 then ((29, s.2.1, s.2.2), none, 1) else ((31, s.2.1, s.2.2), none, 0))
    else if s.1 = 31 then ((32, s.2.1, s.2.2), some false, 1)
    else if s.1 = 32 then ((33, s.2.1, s.2.2), some false, 1)
    else if s.1 = 33 then ((34, s.2.1, s.2.2), some false, 1)
    else if s.1 = 34 then ((35, s.2.1, s.2.2), some true, 3)
    else if s.1 = 35 then ((36, s.2.1, b), none, 1)
    else if s.1 = 36 then
      (if s.2.2 then ((35, s.2.1, s.2.2), none, 1)
       else (if b then ((37, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 37 then ((38, s.2.1, b), none, 1)
    else if s.1 = 38 then
      (if s.2.2 then ((37, s.2.1, s.2.2), none, 1)
       else (if b then ((39, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 39 then ((40, s.2.1, b), none, 1)
    else if s.1 = 40 then
      (if s.2.2 then
        (if b then ((78, s.2.1, s.2.2), none, 2) else ((39, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((78, s.2.1, s.2.2), none, 2))
             else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 41 then ((42, s.2.1, b), none, 1)
    else if s.1 = 42 then
      (if s.2.2 then ((41, s.2.1, s.2.2), none, 1)
       else (if b then ((43, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 43 then ((44, s.2.1, b), none, 1)
    else if s.1 = 44 then
      (if s.2.2 then
        (if b then ((45, s.2.1, s.2.2), some false, 1) else ((43, s.2.1, s.2.2), none, 1))
       else (if b then ((55, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 45 then ((46, s.2.1, b), none, 1)
    else if s.1 = 46 then
      (if b = s.2.2 then ((45, s.2.1, s.2.2), none, 1) else ((47, s.2.1, s.2.2), none, 1))
    else if s.1 = 47 then ((48, s.2.1, b), none, 1)
    else if s.1 = 48 then
      (if b = s.2.2 then ((47, s.2.1, s.2.2), none, 1) else ((49, s.2.1, s.2.2), none, 1))
    else if s.1 = 49 then ((50, s.2.1, b), none, 1)
    else if s.1 = 50 then
      (if b = s.2.2 then ((49, s.2.1, s.2.2), none, 1) else ((51, s.2.1, s.2.2), none, 0))
    else if s.1 = 51 then ((52, s.2.1, s.2.2), some true, 1)
    else if s.1 = 52 then ((53, s.2.1, s.2.2), some true, 1)
    else if s.1 = 53 then ((54, s.2.1, s.2.2), some false, 1)
    else if s.1 = 54 then ((41, s.2.1, s.2.2), some true, 3)
    else if s.1 = 55 then ((56, s.2.1, b), none, 1)
    else if s.1 = 56 then
      (if b = s.2.2 then ((55, s.2.1, s.2.2), none, 1) else ((57, s.2.1, s.2.2), none, 1))
    else if s.1 = 57 then ((58, s.2.1, b), none, 1)
    else if s.1 = 58 then
      (if b = s.2.2 then ((57, s.2.1, s.2.2), none, 1) else ((59, s.2.1, s.2.2), none, 0))
    else if s.1 = 59 then ((60, s.2.1, s.2.2), some false, 1)
    else if s.1 = 60 then ((61, s.2.1, s.2.2), some false, 1)
    else if s.1 = 61 then ((62, s.2.1, s.2.2), some false, 1)
    else if s.1 = 62 then ((63, s.2.1, s.2.2), some true, 3)
    else if s.1 = 63 then ((64, s.2.1, b), none, 1)
    else if s.1 = 64 then
      (if s.2.2 then ((63, s.2.1, s.2.2), none, 1)
       else (if b then ((65, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 65 then ((66, s.2.1, b), none, 1)
    else if s.1 = 66 then
      (if s.2.2 then
        (if b then ((78, s.2.1, s.2.2), none, 2) else ((65, s.2.1, true), some true, 1))
       else (if b then
              (if h : s.2.1.val + 1 < body.length + 1 then
                ((2, ⟨s.2.1.val + 1, h⟩, s.2.2), none, 3)
               else ((78, s.2.1, s.2.2), none, 2))
             else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 67 then ((68, s.2.1, b), none, 1)
    else if s.1 = 68 then
      (if s.2.2 then ((67, s.2.1, s.2.2), none, 1)
       else (if b then ((69, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 69 then ((70, s.2.1, b), none, 1)
    else if s.1 = 70 then
      (if s.2.2 then ((69, s.2.1, s.2.2), none, 1)
       else (if b then ((71, s.2.1, s.2.2), none, 1) else ((78, s.2.1, s.2.2), none, 2)))
    else if s.1 = 71 then
      (if b then ((72, s.2.1, b), none, 1) else ((73, s.2.1, s.2.2), some true, 1))
    else if s.1 = 72 then ((71, s.2.1, s.2.2), none, 1)
    else if s.1 = 73 then ((74, s.2.1, s.2.2), some true, 1)
    else if s.1 = 74 then ((75, s.2.1, s.2.2), some false, 1)
    else if s.1 = 75 then ((0, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 76 then ((77, s.2.1, b), none, 1)
    else if s.1 = 77 then
      (if s.2.2 then
        (if b then ((78, s.2.1, false), none, 2) else ((76, s.2.1, true), some true, 1))
       else (if b then ((78, s.2.1, false), none, 2) else ((78, s.2.1, false), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lp2 (body : List LInstr) (t : List Bool) :
    init (loopProg2Machine body) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

/-! ### Step and pair-step lemmas -/

section Steps
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem l2_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(76, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .bit b) :
    run (loopProg2Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2Machine, moveHead, h, hp']

theorem l2_dispatch_spliceA (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceA) :
    run (loopProg2Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(41, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceA := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2Machine, moveHead, h, hp']

theorem l2_dispatch_spliceJ (h : idx.val < body.length)
    (hp : body.getD idx.val .spliceJ = .spliceJ) :
    run (loopProg2Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(15, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spliceJ := by
    rwa [List.getD_eq_getElem body .spliceJ h] at hp
  simp [step, loopProg2Machine, moveHead, h, hp']

theorem l2_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProg2Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(67, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProg2Machine, moveHead, h]

end Steps

/-! ### The generated pair-step layer (skips, scans, finds, heals, snocs) -/

section Steps2
variable {body : List LInstr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem l2_skipR1a (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1a (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR1j (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(15, idx, s), p, T⟩ = ⟨(15, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(15, idx, s), p, T⟩ = ⟨(17, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(15, idx, s), p, T⟩
      = ⟨(16, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR2j (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(17, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR2j (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR1hj (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(35, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(35, idx, s), p, T⟩ = ⟨(37, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR2hj (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(37, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR2hj (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(39, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR1A (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1A (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(43, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR1hA (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(63, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1hA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(65, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR1i (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(67, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR1i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipR2i (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(69, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg2Machine, moveHead]; rfl

theorem l2_crossR2i (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(71, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanA1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(7, idx, s), p, T⟩
      = ⟨(7, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanJ1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(21, idx, s), p, T⟩
      = ⟨(21, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanJ2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanJD (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(29, idx, s), p, T⟩
      = ⟨(29, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanS1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(45, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanS2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanS3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(49, idx, s), p, T⟩
      = ⟨(49, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanD1 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(55, idx, s), p, T⟩
      = ⟨(55, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_scanD2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg2Machine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_crossSA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_crossSJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_crossSS1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(47, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_crossSS2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(49, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_crossSD1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(57, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2']

theorem l2_detectA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l2_detectJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l2_detectJD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(29, idx, s), p, T⟩ = ⟨(31, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l2_detectS3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(49, idx, s), p, T⟩ = ⟨(51, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l2_detectD2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(57, idx, s), p, T⟩ = ⟨(59, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg2Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l2_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(19, idx, s), p, T⟩
      = ⟨(21, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(29, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(43, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(43, idx, s), p, T⟩
      = ⟨(45, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(55, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(39, idx, s), p, T⟩
      = ⟨(39, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(39, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2, h]

theorem l2_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(65, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

theorem l2_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2, h]

theorem l2_four_trueJ :
    run (loopProg2Machine body) 4 ⟨(25, idx, s), p, T⟩
      = ⟨(15, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2Machine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2Machine body) ⟨(26, idx, s), p', T'⟩
      = ⟨(27, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2Machine body) ⟨(27, idx, s), p', T'⟩
      = ⟨(28, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2Machine body) ⟨(28, idx, s), p', T'⟩
      = ⟨(15, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem l2_four_falseJ :
    run (loopProg2Machine body) 4 ⟨(31, idx, s), p, T⟩
      = ⟨(35, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2Machine body) ⟨(31, idx, s), p, T⟩
      = ⟨(32, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2Machine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(33, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2Machine body) ⟨(33, idx, s), p', T'⟩
      = ⟨(34, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2Machine body) ⟨(34, idx, s), p', T'⟩
      = ⟨(35, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem l2_four_trueA :
    run (loopProg2Machine body) 4 ⟨(51, idx, s), p, T⟩
      = ⟨(41, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2Machine body) ⟨(51, idx, s), p, T⟩
      = ⟨(52, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2Machine body) ⟨(52, idx, s), p', T'⟩
      = ⟨(53, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2Machine body) ⟨(53, idx, s), p', T'⟩
      = ⟨(54, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2Machine body) ⟨(54, idx, s), p', T'⟩
      = ⟨(41, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem l2_four_falseA :
    run (loopProg2Machine body) 4 ⟨(59, idx, s), p, T⟩
      = ⟨(63, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2Machine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, s), p + 1, writeAt T p false⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2Machine body) ⟨(60, idx, s), p', T'⟩
      = ⟨(61, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2Machine body) ⟨(61, idx, s), p', T'⟩
      = ⟨(62, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2Machine body) ⟨(62, idx, s), p', T'⟩
      = ⟨(63, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

/-- The append snoc: the instruction's bit, doubled, plus the closing marker; advance the pointer. -/
theorem l2_four_bit (h : idx.val + 1 < body.length + 1) :
    run (loopProg2Machine body) 4 ⟨(11, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spliceJ).bitVal)
            (p + 1) (body.getD idx.val .spliceJ).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg2Machine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, s), p + 1, writeAt T p (body.getD idx.val .spliceJ).bitVal⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg2Machine body) ⟨(12, idx, s), p', T'⟩
      = ⟨(13, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spliceJ).bitVal⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg2Machine body) ⟨(13, idx, s), p', T'⟩
      = ⟨(14, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg2Machine body) ⟨(14, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProg2Machine, moveHead, h]
  rw [e1, e2, e3, e4]

/-- The increment walk: skip a data pair of the variable. -/
theorem l2_walkI (h1 : T.getD p false = true) :
    run (loopProg2Machine body) 2 ⟨(71, idx, s), p, T⟩ = ⟨(71, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2Machine, moveHead, h1']
  rw [e0]
  simp only [step, loopProg2Machine, moveHead]; rfl

/-- The increment's four marker-advancing writes; reset everything into the next round. -/
theorem l2_four_incr (h1 : T.getD p false = false) :
    run (loopProg2Machine body) 4 ⟨(71, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e71 : step (loopProg2Machine body) ⟨(71, idx, s), p, T⟩
      = ⟨(73, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg2Machine, moveHead, h1']
  have e73 : ∀ p' T', step (loopProg2Machine body) ⟨(73, idx, s), p', T'⟩
      = ⟨(74, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e74 : ∀ p' T', step (loopProg2Machine body) ⟨(74, idx, s), p', T'⟩
      = ⟨(75, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  have e75 : ∀ p' T', step (loopProg2Machine body) ⟨(75, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e71, e73, e74, e75]

/-- The finale: heal a marked bound pair. -/
theorem l2_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg2Machine body) 2 ⟨(76, idx, s), p, T⟩
      = ⟨(76, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(76, idx, s), p, T⟩
      = ⟨(77, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

/-- The finale completes: halt. -/
theorem l2_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg2Machine body) 2 ⟨(76, idx, s), p, T⟩ = ⟨(78, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg2Machine body) ⟨(76, idx, s), p, T⟩
      = ⟨(77, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg2Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg2Machine, moveHead, h2]

end Steps2

/-! ### Scan run-invariants -/

theorem l2_skipBs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2Machine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipB hk.1 hk.2]
    rfl

theorem l2_skipR1as (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1a (h k (by omega))]
    rfl

theorem l2_skipR1js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(15, idx, s), q, T⟩
      = ⟨(15, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1j (h k (by omega))]
    rfl

theorem l2_skipR2js (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR2j (h k (by omega))]
    rfl

theorem l2_skipR1hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(35, idx, s), q, T⟩
      = ⟨(35, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1hj (h k (by omega))]
    rfl

theorem l2_skipR2hjs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(37, idx, s), q, T⟩
      = ⟨(37, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR2hj (h k (by omega))]
    rfl

theorem l2_skipR1As (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1A (h k (by omega))]
    rfl

theorem l2_skipR1hAs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(63, idx, s), q, T⟩
      = ⟨(63, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1hA (h k (by omega))]
    rfl

theorem l2_skipR1is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR1i (h k (by omega))]
    rfl

theorem l2_skipR2is (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(69, idx, s), q, T⟩
      = ⟨(69, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipR2i (h k (by omega))]
    rfl

theorem l2_scanA1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanA1 (h k (by omega))]
    rfl

theorem l2_scanA2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanA2 (h k (by omega))]
    rfl

theorem l2_scanA3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanA3 (h k (by omega))]
    rfl

theorem l2_scanJ1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanJ1 (h k (by omega))]
    rfl

theorem l2_scanJ2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanJ2 (h k (by omega))]
    rfl

theorem l2_scanJDs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(29, idx, s), q, T⟩
      = ⟨(29, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanJD (h k (by omega))]
    rfl

theorem l2_scanS1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanS1 (h k (by omega))]
    rfl

theorem l2_scanS2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(47, idx, s), q, T⟩
      = ⟨(47, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanS2 (h k (by omega))]
    rfl

theorem l2_scanS3s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(49, idx, s), q, T⟩
      = ⟨(49, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanS3 (h k (by omega))]
    rfl

theorem l2_scanD1s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanD1 (h k (by omega))]
    rfl

theorem l2_scanD2s (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg2Machine body) (2 * k) ⟨(57, idx, s), q, T⟩
      = ⟨(57, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_scanD2 (h k (by omega))]
    rfl

theorem l2_skipJms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2Machine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipJm hk.1 hk.2]
    rfl

theorem l2_skipAms (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg2Machine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_skipAm hk.1 hk.2]
    rfl

/-- The increment's data walk. -/
theorem l2_walkIs (body : List LInstr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg2Machine body) (2 * k) ⟨(71, idx, s), q, T⟩
      = ⟨(71, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l2_walkI (h k (by omega))]
    rfl

/-- The source-heal invariant (evolving `hlT`, past the bound prefix). -/
theorem l2_healAs (body : List LInstr) (P : List Bool) (N a : ℕ) (E : List Bool)
    (hP : P.length = 2 * N + 2) (idx : Fin (body.length + 1)) (s : Bool)
    (i : ℕ) (hi : i ≤ a) :
    run (loopProg2Machine body) (2 * i) ⟨(65, idx, s), 2 * N + 2, P ++ (hlT a 0 ++ E)⟩
      = ⟨(65, idx, if i = 0 then s else true), 2 * N + 2 + 2 * i, P ++ (hlT a i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (hlT a i ++ E)).getD (2 * N + 2 + 2 * i) false = true := by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
      exact liftJ P _ hP (hlE_pair_lo a i E (by omega))
    have h2 : (P ++ (hlT a i ++ E)).getD (2 * N + 2 + 2 * i + 1) false = false := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ P _ hP (hlE_pair_hi a i E (by omega))
    have hw : writeAt (P ++ (hlT a i ++ E)) (2 * N + 2 + 2 * i + 1) true
        = P ++ (hlT a (i + 1) ++ E) := by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
        writeAt_append_right P _ (2 * N + 2) (2 * i + 1) true hP
          (by rw [List.length_append, hlT_length a i (by omega)]; omega),
        hlT_heal a i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l2_healA h1 h2, hw]
    rfl

/-- The variable-heal invariant (evolving `jhT`, past the bound and source prefixes). -/
theorem l2_healJs2 (body : List LInstr) (P Q : List Bool) (N a k : ℕ) (E : List Bool)
    (hP : P.length = 2 * N + 2) (hQ : Q.length = 2 * a + 2) (hk : k ≤ N)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (loopProg2Machine body) (2 * i)
      ⟨(39, idx, s), 2 * N + 2 + 2 * a + 2, P ++ (Q ++ (jhT N k 0 ++ E))⟩
      = ⟨(39, idx, if i = 0 then s else true), 2 * N + 2 + 2 * a + 2 + 2 * i,
          P ++ (Q ++ (jhT N k i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (jhT N k i ++ E))).getD (2 * N + 2 + 2 * a + 2 + 2 * i) false
        = true := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega]
      exact liftJ2 P Q _ hP hQ (jhE_pair_lo N k i E (by omega))
    have h2 : (P ++ (Q ++ (jhT N k i ++ E))).getD (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 P Q _ hP hQ (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (P ++ (Q ++ (jhT N k i ++ E))) (2 * N + 2 + 2 * a + 2 + 2 * i + 1) true
        = P ++ (Q ++ (jhT N k (i + 1) ++ E)) := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 P Q _ (2 * N + 2) (2 * a + 2) (2 * i + 1) true hP hQ
          (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l2_healJ h1 h2, hw]
    rfl

/-- The bound-heal invariant (the finale). -/
theorem l2_healBs (body : List LInstr) (v : ℕ) (E : List Bool)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (loopProg2Machine body) (2 * i) ⟨(76, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(76, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l2_healB (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The instruction lemmas

Round-`k` layout: `cntT N (k+1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))` — regions at `[0, 2N+2)`,
`[2N+2, 2N+2a+4)`, `[2N+2a+4, 4N+2a+6)`, output at `4N+2a+6`. -/

/-- **An append instruction**: dispatch, skip the bound, three boundary-event scans, snoc, advance. -/
theorem lp2_instr_bit (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spliceJ = .bit b)
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2Machine body) (4 * N + 2 * a + 2 * OUT.length + 13)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD (OUT ++ [b])))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQ : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq3 : (cntT N (k + 1)).length + (unaryD a).length + (jT N k).length
      = 4 * N + 2 * a + 6 := by
    rw [hR1, hQ, jT_length N k (by omega)]; omega
  have b0 := l2_dispatch_bit (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) h hp
  have b1 := l2_skipR1as body (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) 0 N
    idx s (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at b1
  have b2 := l2_crossR1a (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have b3 := l2_scanA1s body (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2) a idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 2 * i) false = true := by
        rw [← cntT_zero]
        exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b4 := l2_crossSA1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) (2 * N + 2)
      false a)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have b5 := l2_scanA2s body (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2 + 2 * a + 2) k idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i)
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := l2_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 2 * a + 2) false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_hi N k 0 _ (by omega)))
  have b7 := l2_scanA3s body (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
    (2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i)) from by omega, ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (unaryD a) (jT N k) OUT (4 * N + 2 * a + 6)
          (i - (N - k)) hq3 (by omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 4 * N + 2 * a + 6 + 2 * OUT.length from by omega] at b7
  have b8 := l2_detectA3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT)))
      (2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 4 * N + 2 * a + 6 + 2 * OUT.length)
    (preD3_mark_lo (cntT N (k + 1)) (unaryD a) (jT N k) OUT (4 * N + 2 * a + 6) hq3)
    (preD3_mark_hi (cntT N (k + 1)) (unaryD a) (jT N k) OUT (4 * N + 2 * a + 6) hq3)
  have b9 := l2_four_bit (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 6 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) (by omega)
  rw [hp] at b9
  simp only [LInstr.bitVal] at b9
  rw [writes_snoc3 (cntT N (k + 1)) (unaryD a) (jT N k) OUT (4 * N + 2 * a + 6) hq3 b] at b9
  rw [show 4 * N + 2 * a + 2 * OUT.length + 13
      = 1 + (2 * N + (2 + (2 * a + (2 + (2 * k + (2 + (2 * ((N - k) + OUT.length)
          + (2 + 4)))))))) from by omega,
    run_add, b0, run_add, b1, run_add, b2, run_add, b3, run_add, b4, run_add, b5,
    run_add, b6, run_add, b7, run_add, b8, b9]

/-! ### The splice sub-round clock (shared by both splice tracks) -/

def lp2SpRounds (N a L : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => lp2SpRounds N a L j + (4 * N + 2 * a + 2 * L + 2 * j + 12)

/-! ### The splice-J instruction -/

/-- One splice-J sub-round. -/
theorem lp2_spj_round (body : List LInstr) (idx : Fin (body.length + 1))
    (N a k j' : ℕ) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2Machine body) (4 * N + 2 * a + 2 * OUT.length + 2 * j' + 12)
      ⟨(15, idx, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))⟩
      = ⟨(15, idx, false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQ : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq3 : (cntT N (k + 1)).length + (unaryD a).length + (jsT N k (j' + 1)).length
      = 4 * N + 2 * a + 6 := by
    rw [hR1, hQ, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have j1 := l2_skipR1js body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at j1
  have j2 := l2_crossR1j (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have j3 := l2_skipR2js body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))) (2 * N + 2)
    a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero]
      exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have j4 := l2_crossR2j (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have j5 := l2_skipJms body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 2 * a + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega]
      exact liftJ2 _ _ _ hR1 hQ (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 _ _ _ hR1 hQ (jsE_mark_hi N k j' _ i hi)⟩)
  have j6 := l2_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * j')
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' = 2 * N + 2 + (2 * a + 2 + 2 * j')
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * a + 2 + (2 * j' + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))
      (2 * N + 2 + 2 * a + 2 + 2 * j' + 1) false
      = cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' + 1 = 2 * N + 2 + (2 * a + 2 + (2 * j' + 1))
        from by omega,
      writeAt_append_right2 _ _ _ (2 * N + 2) (2 * a + 2) (2 * j' + 1) false hR1 hQ
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at j6
  have j7 := l2_scanJ1s body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 2 * a + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i
            = 2 * N + 2 + (2 * a + 2 + (2 * (j' + 1) + 2 * i)) from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i) (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
          ++ encodeD (OUT ++ List.replicate j' true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * (j' + 1) + 2 * i + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * N + 2 + 2 * a + 2 + 2 * k from by omega] at j7
  have j8 := l2_crossSJ1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * N + 2 + 2 * a + 2 + 2 * j' + 2)
      true (k - j' - 1))
    (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_hi N k (j' + 1) _ (by omega)))
  have j9 := l2_scanJ2s body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))
    (2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate j' true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate j' true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (4 * N + 2 * a + 6) (i - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 4 * N + 2 * a + 6 + 2 * (OUT.length + j') from by omega] at j9
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 6) hq3
  rw [hlen] at hm1 hm2
  have j10 := l2_detectJ2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true)))) (2 * N + 2 + 2 * a + 2 + 2 * k + 2)
      false ((N - k) + (OUT.length + j')))
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (unaryD a) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 6) hq3 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have j11 := l2_four_trueJ (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + j'))
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k (j' + 1)
      ++ encodeD (OUT ++ List.replicate j' true))))
  rw [hsn] at j11
  rw [show 4 * N + 2 * a + 2 * OUT.length + 2 * j' + 12
      = 2 * N + (2 + (2 * a + (2 + (2 * j' + (2 + (2 * (k - j' - 1)
          + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4))))))))) from by omega,
    run_add, j1, run_add, j2, run_add, j3, run_add, j4, run_add, j5, run_add, j6,
    run_add, j7, run_add, j8, run_add, j9, run_add, j10, j11]

theorem lp2_spj_rounds (body : List LInstr) (idx : Fin (body.length + 1))
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k) (s : Bool) :
    run (loopProg2Machine body) (lp2SpRounds N a OUT.length j)
      ⟨(15, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (jsT N k 0 ++ encodeD OUT))⟩
      = ⟨(15, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (jsT N k j ++ encodeD (OUT ++ List.replicate j true)))⟩ := by
  induction j with
  | zero => simp only [lp2SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp2SpRounds N a OUT.length (j + 1)
        = lp2SpRounds N a OUT.length j + (4 * N + 2 * a + 2 * OUT.length + 2 * j + 12)
        from rfl,
      run_add, ih (by omega), lp2_spj_round body idx N a k j (by omega) hk OUT _,
      if_neg (by omega)]

def lp2jCost (N a k L : ℕ) : ℕ :=
  1 + (lp2SpRounds N a L k
    + ((4 * N + 2 * a + 2 * L + 2 * k + 12) + (2 * N + 2 * a + 2 * k + 6)))

/-- **A splice-J instruction**: emit `encodeNat k` from the live variable, heal it, advance. -/
theorem lp2_instr_spliceJ (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spliceJ = .spliceJ)
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2Machine body) (lp2jCost N a k OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD (OUT ++ encodeNat k)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQ : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hq3 : (cntT N (k + 1)).length + (unaryD a).length + (jsT N k k).length
      = 4 * N + 2 * a + 6 := by
    rw [hR1, hQ, jsT_length N k k (le_refl k) (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate k true).length = OUT.length + k := by
    rw [List.length_append, List.length_replicate]
  have d0 := l2_dispatch_spliceJ (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) h hp
  have d1 := lp2_spj_rounds body idx N a k hk OUT k (le_refl k) s
  have d2 := l2_skipR1js body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))) 0 N idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d2
  have d3 := l2_crossR1j (body := body) (idx := idx)
    (s := if N = 0 then (if k = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d4 := l2_skipR2js body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))) (2 * N + 2)
    a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero]
      exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have d5 := l2_crossR2j (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have d6 := l2_skipJms body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (2 * N + 2 + 2 * a + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega]
      exact liftJ2 _ _ _ hR1 hQ (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 _ _ _ hR1 hQ (jsE_mark_hi N k k _ i hi)⟩)
  have d7 := l2_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_hi N k k _ (le_refl k)))
  have d8 := l2_scanJDs body (cntT N (k + 1)
      ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
    (2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + k)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k k
            ++ encodeD (OUT ++ List.replicate k true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i)) from by omega]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k k _ (2 * k + 2 + 2 * i) (le_refl k)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (unaryD a ++ (jsT N k k
            ++ encodeD (OUT ++ List.replicate k true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)) from by omega]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k k _ (2 * k + 2 + 2 * i + 1) (le_refl k)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (unaryD a) (jsT N k k)
          (OUT ++ List.replicate k true) (4 * N + 2 * a + 6) (i - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + k))
      = 4 * N + 2 * a + 6 + 2 * (OUT.length + k) from by omega] at d8
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 2 * a + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 2 * a + 6) hq3
  rw [hlen2] at hm1 hm2
  have d9 := l2_detectJD (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (jsT N k k
      ++ encodeD (OUT ++ List.replicate k true)))) (2 * N + 2 + 2 * a + 2 + 2 * k + 2)
      false ((N - k) + (OUT.length + k)))
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + k)) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (unaryD a) (jsT N k k)
    (OUT ++ List.replicate k true) (4 * N + 2 * a + 6) hq3 false
  rw [hlen2, List.append_assoc,
    show (List.replicate k true ++ [false] : List Bool) = encodeNat k from rfl] at hsn
  have d10 := l2_four_falseJ (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + k))
    (T := cntT N (k + 1) ++ (unaryD a ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))
  rw [hsn] at d10
  have d11 := l2_skipR1hjs body (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at d11
  have d12 := l2_crossR1hj (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have d13 := l2_skipR2hjs body (cntT N (k + 1)
      ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k)))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero]
      exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have d14 := l2_crossR2hj (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jhT N k 0 ++ encodeD (OUT ++ encodeNat k))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have d15 := l2_healJs2 body (cntT N (k + 1)) (unaryD a) N a k
    (encodeD (OUT ++ encodeNat k)) hR1 hQ (by omega) idx false k (le_refl k)
  have d16 := l2_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true) (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jhT N k k ++ encodeD (OUT ++ encodeNat k))))
    (by omega)
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jhE_m_lo N k _))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQ (jhE_m_hi N k _))
  rw [show lp2jCost N a k OUT.length
      = 1 + (lp2SpRounds N a OUT.length k + (2 * N + (2 + (2 * a + (2 + (2 * k + (2
          + (2 * ((N - k) + (OUT.length + k)) + (2 + (4 + (2 * N + (2 + (2 * a + (2
          + (2 * k + 2)))))))))))))))
      from by simp only [lp2jCost]; omega,
    run_add, d0, ← jsT_zero, run_add, d1, run_add, d2, run_add, d3, run_add, d4,
    run_add, d5, run_add, d6, run_add, d7, run_add, d8, run_add, d9, run_add, d10,
    ← jhT_zero, run_add, d11, run_add, d12, run_add, d13, run_add, d14, run_add, d15,
    d16, jhT_last, jsT_zero]

/-! ### The splice-A instruction -/

/-- One splice-A sub-round: mark the source's pair `i`, seek out through variable and padding, emit a
doubled `true`. -/
theorem lp2_spa_round (body : List LInstr) (idx : Fin (body.length + 1))
    (N a k i : ℕ) (hi : i < a) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2Machine body) (4 * N + 2 * a + 2 * OUT.length + 2 * i + 12)
      ⟨(41, idx, s), 0, cntT N (k + 1)
        ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))⟩
      = ⟨(41, idx, false), 0, cntT N (k + 1)
          ++ (cntT a (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate (i + 1) true)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQ : (cntT a (i + 1)).length = 2 * a + 2 := cntT_length a (i + 1) (by omega)
  have hq3 : (cntT N (k + 1)).length + (cntT a (i + 1)).length + (jT N k).length
      = 4 * N + 2 * a + 6 := by
    rw [hR1, hQ, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s1 := l2_skipR1As body (cntT N (k + 1)
      ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) 0 N idx s
    (fun i' hi' => by simpa using cntE_lo N (k + 1) _ i' (by omega) hi')
  simp only [Nat.zero_add] at s1
  have s2 := l2_crossR1A (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have s3 := l2_skipAms body (cntT N (k + 1)
      ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) (2 * N + 2)
    i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * N + 2 + 2 * i' = 2 * N + 2 + (2 * i') from rfl]
      exact liftJ _ _ hR1 (cntE_mark_lo a i _ i' hi'), by
      rw [show 2 * N + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * i' + 1) from by omega]
      exact liftJ _ _ hR1 (cntE_mark_hi a i _ i' hi')⟩)
  have s4 := l2_markA (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * N + 2 + 2 * i)
    (T := cntT N (k + 1) ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (by rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
        exact liftJ _ _ hR1 (cntE_data a i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_data a i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1)
      ++ (cntT a i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
      (2 * N + 2 + 2 * i + 1) false
      = cntT N (k + 1)
          ++ (cntT a (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))) := by
    rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (2 * i + 1) false hR1
        (by rw [List.length_append, cntT_length a i (by omega)]; omega),
      cntT_mark a i _ hi]
  rw [hw] at s4
  have s5 := l2_scanS1s body (cntT N (k + 1)
      ++ (cntT a (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (2 * N + 2 + 2 * i + 2) (a - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (cntT a (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * N + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * i + 2 + 2 * i' = 2 * N + 2 + (2 * (i + 1) + 2 * i')
            from by omega]
        exact liftJ _ _ hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i') (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * N + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * i + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * (i + 1) + 2 * i' + 1)
            from by omega]
        exact liftJ _ _ hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i' + 1) (by omega)
          (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * i + 2 + 2 * (a - i - 1) = 2 * N + 2 + 2 * a from by omega] at s5
  have s6 := l2_crossSS1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) (2 * N + 2 + 2 * i + 2)
      true (a - i - 1))
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (cntE_cm_lo a (i + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_cm_hi a (i + 1) _ (by omega)))
  have s7 := l2_scanS2s body (cntT N (k + 1)
      ++ (cntT a (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (2 * N + 2 + 2 * a + 2) k idx false
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (cntT a (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' = 2 * N + 2 + (2 * a + 2 + 2 * i')
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ
          (jsE_data N k 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i' + 1))
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ
          (jsE_data N k 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s8 := l2_crossSS2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) (2 * N + 2 + 2 * a + 2)
      false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_hi N k 0 _ (by omega)))
  have s9 := l2_scanS3s body (cntT N (k + 1)
      ++ (cntT a (i + 1) ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
    (2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (cntT a (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i') false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i'
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i')) from by omega, ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k 0 _ (2 * k + 2 + 2 * i') (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (cntT a (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i' + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i' + 1)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQ (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i'
            = 4 * N + 2 * a + 6 + 2 * (i' - (N - k)) from by omega,
          show 4 * N + 2 * a + 6 + 2 * (i' - (N - k)) + 1
            = 4 * N + 2 * a + 6 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (cntT a (i + 1)) (jT N k)
          (OUT ++ List.replicate i true) (4 * N + 2 * a + 6) (i' - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + i))
      = 4 * N + 2 * a + 6 + 2 * (OUT.length + i) from by omega] at s9
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (cntT a (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (cntT a (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 6) hq3
  rw [hlen] at hm1 hm2
  have s10 := l2_detectS3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
      (2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + (OUT.length + i)))
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (cntT a (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 6) hq3 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s11 := l2_four_trueA (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + i))
    (T := cntT N (k + 1) ++ (cntT a (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))
  rw [hsn] at s11
  rw [show 4 * N + 2 * a + 2 * OUT.length + 2 * i + 12
      = 2 * N + (2 + (2 * i + (2 + (2 * (a - i - 1) + (2 + (2 * k
          + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4))))))))) from by omega,
    run_add, s1, run_add, s2, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, s11]

theorem lp2_spa_rounds (body : List LInstr) (idx : Fin (body.length + 1))
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ a) (s : Bool) :
    run (loopProg2Machine body) (lp2SpRounds N a OUT.length j)
      ⟨(41, idx, s), 0, cntT N (k + 1) ++ (cntT a 0 ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(41, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (cntT a j ++ (jT N k ++ encodeD (OUT ++ List.replicate j true)))⟩ := by
  induction j with
  | zero => simp only [lp2SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp2SpRounds N a OUT.length (j + 1)
        = lp2SpRounds N a OUT.length j + (4 * N + 2 * a + 2 * OUT.length + 2 * j + 12)
        from rfl,
      run_add, ih (by omega), lp2_spa_round body idx N a k j (by omega) hk OUT _,
      if_neg (by omega)]

def lp2aCost (N a L : ℕ) : ℕ :=
  1 + (lp2SpRounds N a L a
    + ((4 * N + 4 * a + 2 * L + 12) + (2 * N + 2 * a + 4)))

/-- **A splice-A instruction**: emit `encodeNat a` from the static source, heal it, advance. -/
theorem lp2_instr_spliceA (body : List LInstr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spliceJ = .spliceA)
    (N a k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg2Machine body) (lp2aCost N a OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD (OUT ++ encodeNat a)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (cntT a a).length = 2 * a + 2 := cntT_length a a (le_refl a)
  have hq3 : (cntT N (k + 1)).length + (cntT a a).length + (jT N k).length
      = 4 * N + 2 * a + 6 := by
    rw [hR1, hQa, jT_length N k (by omega)]; omega
  have hlen2 : (OUT ++ List.replicate a true).length = OUT.length + a := by
    rw [List.length_append, List.length_replicate]
  have g0 := l2_dispatch_spliceA (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD OUT))) h hp
  have g1 := lp2_spa_rounds body idx N a k hk OUT a (le_refl a) s
  have g2 := l2_skipR1As body (cntT N (k + 1)
      ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))) 0 N idx
    (if a = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g2
  have g3 := l2_crossR1A (body := body) (idx := idx)
    (s := if N = 0 then (if a = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g4 := l2_skipAms body (cntT N (k + 1)
      ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))) (2 * N + 2)
    a idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
      exact liftJ _ _ hR1 (cntE_mark_lo a a _ i hi), by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hR1 (cntE_mark_hi a a _ i hi)⟩)
  have g5 := l2_doneA (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (cntE_cm_lo a a _ (le_refl a)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_cm_hi a a _ (le_refl a)))
  have g6 := l2_scanD1s body (cntT N (k + 1)
      ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
    (2 * N + 2 + 2 * a + 2) k idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (cntT a a
          ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i)
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQa
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a a
          ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
            from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQa
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have g7 := l2_crossSD1 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a a
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))) (2 * N + 2 + 2 * a + 2)
      false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k)
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQa (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 1 = 2 * N + 2 + (2 * a + 2 + (2 * k + 1))
          from by omega, ← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQa (jsE_m_hi N k 0 _ (by omega)))
  have g8 := l2_scanD2s body (cntT N (k + 1)
      ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
    (2 * N + 2 + 2 * a + 2 + 2 * k + 2) ((N - k) + (OUT.length + a)) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (cntT a a
            ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i)) from by omega, ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQa (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (cntT a a
            ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * k + 2 + 2 * i + 1)) from by omega,
            ← jsT_zero N k]
          exact liftJ2 _ _ _ hR1 hQa (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1) (by omega)
            (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 6 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD3_data_eq (cntT N (k + 1)) (cntT a a) (jT N k)
          (OUT ++ List.replicate a true) (4 * N + 2 * a + 6) (i - (N - k)) hq3
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + a))
      = 4 * N + 2 * a + 6 + 2 * (OUT.length + a) from by omega] at g8
  have hm1 := preD3_mark_lo (cntT N (k + 1)) (cntT a a) (jT N k)
    (OUT ++ List.replicate a true) (4 * N + 2 * a + 6) hq3
  have hm2 := preD3_mark_hi (cntT N (k + 1)) (cntT a a) (jT N k)
    (OUT ++ List.replicate a true) (4 * N + 2 * a + 6) hq3
  rw [hlen2] at hm1 hm2
  have g9 := l2_detectD2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a a
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
      (2 * N + 2 + 2 * a + 2 + 2 * k + 2) false ((N - k) + (OUT.length + a)))
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + a)) hm1 hm2
  have hsn := writes_snoc3 (cntT N (k + 1)) (cntT a a) (jT N k)
    (OUT ++ List.replicate a true) (4 * N + 2 * a + 6) hq3 false
  rw [hlen2, List.append_assoc,
    show (List.replicate a true ++ [false] : List Bool) = encodeNat a from rfl] at hsn
  have g10 := l2_four_falseA (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 6 + 2 * (OUT.length + a))
    (T := cntT N (k + 1) ++ (cntT a a ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))
  rw [hsn] at g10
  have g11 := l2_skipR1hAs body (cntT N (k + 1)
      ++ (hlT a 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat a)))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g11
  have g12 := l2_crossR1hA (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (hlT a 0 ++ (jT N k ++ encodeD (OUT ++ encodeNat a))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g13 := l2_healAs body (cntT N (k + 1)) N a
    (jT N k ++ encodeD (OUT ++ encodeNat a)) hR1 idx false a (le_refl a)
  have g14 := l2_doneHealA (body := body) (idx := idx)
    (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (hlT a a ++ (jT N k ++ encodeD (OUT ++ encodeNat a))))
    (by omega)
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (hlE_cm_lo a _))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (hlE_cm_hi a _))
  rw [show lp2aCost N a OUT.length
      = 1 + (lp2SpRounds N a OUT.length a + (2 * N + (2 + (2 * a + (2 + (2 * k + (2
          + (2 * ((N - k) + (OUT.length + a)) + (2 + (4 + (2 * N + (2 + (2 * a + 2)))))))))))))
      from by simp only [lp2aCost]; omega,
    run_add, g0, ← cntT_zero, run_add, g1, run_add, g2, run_add, g3, run_add, g4,
    run_add, g5, run_add, g6, run_add, g7, run_add, g8, run_add, g9, run_add, g10,
    ← hlT_zero, run_add, g11, run_add, g12, run_add, g13, g14, hlT_last, cntT_zero]

/-! ## The instruction segment, the round, and the loop -/

/-- One instruction's clock inside round `k`. -/
def lp2InstrCost (body : List LInstr) (N a k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n .spliceJ with
  | .bit _ => 4 * N + 2 * a + 2 * (L + (prog2OutN body a k n).length) + 13
  | .spliceA => lp2aCost N a (L + (prog2OutN body a k n).length)
  | .spliceJ => lp2jCost N a k (L + (prog2OutN body a k n).length)

/-- The cumulative segment clock. -/
def lp2SegN (body : List LInstr) (N a k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lp2SegN body N a k L n + lp2InstrCost body N a k L n

/-- **The segment invariant**: `n` instructions of round `k` executed. -/
theorem lp2_run_instrs (body : List LInstr) (N a k : ℕ) (hk : k < N)
    (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (loopProg2Machine body) (lp2SegN body N a k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (jT N k ++ encodeD out'))⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (jT N k ++ encodeD (out' ++ prog2OutN body a k n)))⟩ := by
  induction n with
  | zero => simp only [lp2SegN]; rw [run_zero]; simp [prog2OutN]
  | succ n ih =>
    rw [show lp2SegN body N a k out'.length (n + 1)
        = lp2SegN body N a k out'.length n + lp2InstrCost body N a k out'.length n from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n .spliceJ with
    | bit b =>
      have hin := lp2_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a k hk (out' ++ prog2OutN body a k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body a k n ++ [b] = prog2OutN body a k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [lp2InstrCost, hp]
      rw [hin]
      simp
    | spliceA =>
      have hin := lp2_instr_spliceA body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a k hk (out' ++ prog2OutN body a k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body a k n ++ encodeNat a = prog2OutN body a k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [lp2InstrCost, hp]
      rw [hin]
      simp
    | spliceJ =>
      have hin := lp2_instr_spliceJ body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a k hk (out' ++ prog2OutN body a k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog2OutN body a k n ++ encodeNat k = prog2OutN body a k (n + 1) from by
          simp only [prog2OutN, hp]; rfl] at hin
      simp only [lp2InstrCost, hp]
      rw [hin]
      simp

/-- The round clock: mark, segment, increment. -/
def lp2RoundCost (body : List LInstr) (N a k L : ℕ) : ℕ :=
  (2 * k + 2) + (lp2SegN body N a k L body.length + (2 * N + 2 * a + 2 * k + 9))

/-- **One loop round**: mark the bound's pair `k`, run the body (appends and splices of the source value
`a` and the live value `k`), increment the variable in place. -/
theorem lp2_round (body : List LInstr) (N a k : ℕ) (hk : k < N) (out' : List Bool)
    (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (loopProg2Machine body) (lp2RoundCost body N a k out'.length)
      ⟨(0, ptrIn, s), 0, cntT N k ++ (unaryD a ++ (jT N k ++ encodeD out'))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (jT N (k + 1)
            ++ encodeD (out' ++ prog2Out body a k)))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQ : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have r1 := l2_skipBs body (cntT N k ++ (unaryD a ++ (jT N k ++ encodeD out'))) 0 k ptrIn s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := l2_markB (body := body) (idx := ptrIn) (s := if k = 0 then s else true)
    (p := 2 * k) (T := cntT N k ++ (unaryD a ++ (jT N k ++ encodeD out')))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at r2
  have r3 := lp2_run_instrs body N a k hk out' body.length (le_refl _) true
  have r4 := l2_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k
      ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (Nat.lt_irrefl _)
  have r5 := l2_skipR1is body (cntT N (k + 1)
      ++ (unaryD a ++ (jT N k ++ encodeD (out' ++ prog2OutN body a k body.length)))) 0 N
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r5
  have r6 := l2_crossR1i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then (if body.length = 0 then true else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k
      ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r7 := l2_skipR2is body (cntT N (k + 1)
      ++ (unaryD a ++ (jT N k ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (2 * N + 2) a ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero]
      exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r8 := l2_crossR2i (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k
      ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have r9 := l2_walkIs body (cntT N (k + 1)
      ++ (unaryD a ++ (jT N k ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (2 * N + 2 + 2 * a + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← jsT_zero N k]
      exact liftJ2 _ _ _ hR1 hQ (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r10 := l2_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true) (p := 2 * N + 2 + (2 * a + 2 + 2 * k))
    (T := cntT N (k + 1) ++ (unaryD a ++ (jT N k
      ++ encodeD (out' ++ prog2OutN body a k body.length))))
    (by rw [← jsT_zero N k]
        exact liftJ2 _ _ _ hR1 hQ (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right2 (cntT N (k + 1)) (unaryD a)
      (jT N k ++ encodeD (out' ++ prog2OutN body a k body.length)) (2 * N + 2) (2 * a + 2)
      (2 * k) true true false true hR1 hQ
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r10
  rw [show lp2RoundCost body N a k out'.length
      = 2 * k + (2 + (lp2SegN body N a k out'.length body.length + (1 + (2 * N + (2
          + (2 * a + (2 + (2 * k + 4)))))))) from by simp only [lp2RoundCost]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, run_add, r9,
    show 2 * N + 2 + 2 * a + 2 + 2 * k = 2 * N + 2 + (2 * a + 2 + 2 * k) from by omega,
    r10, prog2Out]

/-- The loop clock. -/
def lp2ClockN (body : List LInstr) (N a Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lp2ClockN body N a Lout k
      + lp2RoundCost body N a k (Lout + (loop2OutN body a k).length)

/-- **The rounds invariant.** -/
theorem lp2_run_rounds (body : List LInstr) (N a : ℕ) (out : List Bool) (k : ℕ)
    (hk : k ≤ N) (s : Bool) :
    run (loopProg2Machine body) (lp2ClockN body N a out.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N 0 ++ (unaryD a ++ (jT N 0 ++ encodeD out))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT N k ++ (unaryD a ++ (jT N k ++ encodeD (out ++ loop2OutN body a k)))⟩ := by
  induction k with
  | zero => simp only [lp2ClockN]; rw [run_zero]; simp [loop2OutN]
  | succ k ih =>
    have hrd := lp2_round body N a k (by omega) (out ++ loop2OutN body a k)
      ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loop2OutN body a k ++ prog2Out body a k = loop2OutN body a (k + 1) from rfl] at hrd
    rw [show lp2ClockN body N a out.length (k + 1)
        = lp2ClockN body N a out.length k
            + lp2RoundCost body N a k (out.length + (loop2OutN body a k).length) from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

/-- The full clock. -/
def lp2Clock (body : List LInstr) (N a Lout : ℕ) : ℕ :=
  lp2ClockN body N a Lout N + (2 * N + (2 + (2 * N + 2)))

/-- **THE TWO-SOURCE LOOPED EMITTER RUNS TO COMPLETION.**  From
`unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out))` the machine halts by itself at the explicit clock
with tape **exactly** `unaryD N ++ (unaryD a ++ (unaryD N ++ encodeD (out ++ loop2Out body a N)))` — the
two-source denotation at every round index appended in order, the bound healed, the source untouched,
the variable saturated. -/
theorem loopProg2_run (body : List LInstr) (N a : ℕ) (out : List Bool) :
    run (loopProg2Machine body) (lp2Clock body N a out.length)
      (init (loopProg2Machine body) (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 1,
          unaryD N ++ (unaryD a ++ (unaryD N ++ encodeD (out ++ loop2Out body a N)))⟩ := by
  rw [init_lp2]
  rw [show (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out)) : List Bool)
      = cntT N 0 ++ (unaryD a ++ (jT N 0 ++ encodeD out)) from by rw [cntT_zero]]
  simp only [lp2Clock]
  have f1 := l2_skipBs body
    (cntT N N ++ (unaryD a ++ (jT N N ++ encodeD (out ++ loop2OutN body a N)))) 0 N
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := l2_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (unaryD a ++ (jT N N ++ encodeD (out ++ loop2OutN body a N))))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have f3 := l2_healBs body N (unaryD a ++ (jT N N ++ encodeD (out ++ loop2OutN body a N)))
    ⟨0, Nat.succ_pos _⟩ false N (le_refl N)
  have f4 := l2_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := hlT N N ++ (unaryD a ++ (jT N N ++ encodeD (out ++ loop2OutN body a N))))
    (hlE_cm_lo N _) (hlE_cm_hi N _)
  rw [run_add, lp2_run_rounds body N a out N (le_refl N) false, ite_self,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last, jT_full,
    show loop2Out body a N = loop2OutN body a N from rfl]

/-- The machine **halts by itself** at its clock. -/
theorem loopProg2_halted (body : List LInstr) (N a : ℕ) (out : List Bool) :
    (loopProg2Machine body).halt
      (run (loopProg2Machine body) (lp2Clock body N a out.length)
        (init (loopProg2Machine body)
          (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out))))).st = true := by
  rw [loopProg2_run]; rfl

/-- **The two-source looped emitter's output.** -/
theorem loopProg2_output (body : List LInstr) (N a : ℕ) (out : List Bool) :
    (run (loopProg2Machine body) (lp2Clock body N a out.length)
      (init (loopProg2Machine body) (unaryD N ++ (unaryD a ++ (jT N 0 ++ encodeD out))))).tp
      = unaryD N ++ (unaryD a ++ (unaryD N ++ encodeD (out ++ loop2Out body a N))) := by
  rw [loopProg2_run]

/-! ## Polynomial clock bounds -/

theorem lp2SpRounds_le (N a L LM j J : ℕ) (hL : L ≤ LM) (hj : j ≤ J) :
    lp2SpRounds N a L j ≤ j * (4 * N + 2 * a + 2 * LM + 2 * J + 12) := by
  induction j with
  | zero => simp [lp2SpRounds]
  | succ j ih =>
    calc lp2SpRounds N a L (j + 1)
        = lp2SpRounds N a L j + (4 * N + 2 * a + 2 * L + 2 * j + 12) := rfl
      _ ≤ j * (4 * N + 2 * a + 2 * LM + 2 * J + 12)
          + (4 * N + 2 * a + 2 * LM + 2 * J + 12) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (j + 1) * (4 * N + 2 * a + 2 * LM + 2 * J + 12) := by ring

/-- The per-instruction cap. -/
def lp2Cap (N a LM : ℕ) : ℕ :=
  N * (4 * N + 2 * a + 2 * LM + 2 * N + 12) + a * (4 * N + 2 * a + 2 * LM + 2 * a + 12)
    + (10 * N + 4 * a + 2 * LM + 19) + (6 * N + 6 * a + 2 * LM + 17)
    + (4 * N + 2 * a + 2 * LM + 13)

theorem lp2InstrCost_le (body : List LInstr) (N a k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + N + 1) ≤ LM) :
    lp2InstrCost body N a k L n ≤ lp2Cap N a LM := by
  have hlen : (prog2OutN body a k n).length ≤ body.length * (a + N + 1) :=
    le_trans (prog2OutN_length_le body a k n) (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n .spliceJ with
  | bit b =>
    simp only [lp2InstrCost, hp, lp2Cap]
    omega
  | spliceA =>
    have h1 := lp2SpRounds_le N a (L + (prog2OutN body a k n).length) LM a a
      (by omega) (le_refl a)
    simp only [lp2InstrCost, hp, lp2aCost, lp2Cap]
    omega
  | spliceJ =>
    have h1 := lp2SpRounds_le N a (L + (prog2OutN body a k n).length) LM k N
      (by omega) (by omega)
    have h2 : k * (4 * N + 2 * a + 2 * LM + 2 * N + 12)
        ≤ N * (4 * N + 2 * a + 2 * LM + 2 * N + 12) := Nat.mul_le_mul_right _ (by omega)
    simp only [lp2InstrCost, hp, lp2jCost, lp2Cap]
    omega

theorem lp2SegN_le (body : List LInstr) (N a k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + N + 1) ≤ LM) :
    lp2SegN body N a k L n ≤ n * lp2Cap N a LM := by
  induction n with
  | zero => simp [lp2SegN]
  | succ n ih =>
    calc lp2SegN body N a k L (n + 1)
        = lp2SegN body N a k L n + lp2InstrCost body N a k L n := rfl
      _ ≤ n * lp2Cap N a LM + lp2Cap N a LM :=
          Nat.add_le_add (ih (by omega)) (lp2InstrCost_le body N a k L n LM hk (by omega) hL)
      _ = (n + 1) * lp2Cap N a LM := by ring

theorem loop2OutN_length_le (body : List LInstr) (N a k : ℕ) (hk : k ≤ N) :
    (loop2OutN body a k).length ≤ k * (body.length * (a + N + 1)) := by
  induction k with
  | zero => simp [loop2OutN]
  | succ k ih =>
    rw [show loop2OutN body a (k + 1) = loop2OutN body a k ++ prog2Out body a k from rfl,
      List.length_append]
    have hone : (prog2Out body a k).length ≤ body.length * (a + N + 1) := by
      show (prog2OutN body a k body.length).length ≤ _
      exact le_trans (prog2OutN_length_le body a k body.length)
        (Nat.mul_le_mul_left _ (by omega))
    calc (loop2OutN body a k).length + (prog2Out body a k).length
        ≤ k * (body.length * (a + N + 1)) + body.length * (a + N + 1) :=
          Nat.add_le_add (ih (by omega)) hone
      _ = (k + 1) * (body.length * (a + N + 1)) := by ring

theorem lp2RoundCost_le (body : List LInstr) (N a k L LM : ℕ) (hk : k < N)
    (hL : L + body.length * (a + N + 1) ≤ LM) :
    lp2RoundCost body N a k L ≤ body.length * lp2Cap N a LM + (6 * N + 2 * a + 11) := by
  have h := lp2SegN_le body N a k L body.length LM hk (le_refl _) hL
  simp only [lp2RoundCost]
  omega

/-- **The loop clock is polynomial**: `N` rounds times the segment cap, plus the finale. -/
theorem lp2Clock_le (body : List LInstr) (N a Lout : ℕ) :
    lp2Clock body N a Lout
      ≤ N * (body.length
            * lp2Cap N a (Lout + N * (body.length * (a + N + 1)) + body.length * (a + N + 1))
          + (6 * N + 2 * a + 11)) + (4 * N + 4) := by
  have hrounds : ∀ k, k ≤ N → lp2ClockN body N a Lout k
      ≤ k * (body.length
            * lp2Cap N a (Lout + N * (body.length * (a + N + 1)) + body.length * (a + N + 1))
          + (6 * N + 2 * a + 11)) := by
    intro k hk
    induction k with
    | zero => simp [lp2ClockN]
    | succ k ih =>
      have hLk : (Lout + (loop2OutN body a k).length) + body.length * (a + N + 1)
          ≤ Lout + N * (body.length * (a + N + 1)) + body.length * (a + N + 1) := by
        have h1 : (loop2OutN body a k).length ≤ k * (body.length * (a + N + 1)) :=
          loop2OutN_length_le body N a k (by omega)
        have h2 : k * (body.length * (a + N + 1)) ≤ N * (body.length * (a + N + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      calc lp2ClockN body N a Lout (k + 1)
          = lp2ClockN body N a Lout k
              + lp2RoundCost body N a k (Lout + (loop2OutN body a k).length) := rfl
        _ ≤ k * (body.length * lp2Cap N a (Lout + N * (body.length * (a + N + 1))
                + body.length * (a + N + 1)) + (6 * N + 2 * a + 11))
            + (body.length * lp2Cap N a (Lout + N * (body.length * (a + N + 1))
                + body.length * (a + N + 1)) + (6 * N + 2 * a + 11)) :=
            Nat.add_le_add (ih (by omega))
              (lp2RoundCost_le body N a k (Lout + (loop2OutN body a k).length) _
                (by omega) hLk)
        _ = (k + 1) * (body.length * lp2Cap N a (Lout + N * (body.length * (a + N + 1))
                + body.length * (a + N + 1)) + (6 * N + 2 * a + 11)) := by ring
  have h := hrounds N (le_refl N)
  simp only [lp2Clock]
  omega

/-! ## THE FIRST LOOPED FAMILY: the head one-hot at-least-one

`encodeClause'_atLeastOne_head` pins the clause at time `t` to
`encodeNat (P+1) ++ (for p in 0..P: encodeNat t · encodeNat p · encodeNat 1 · [true])`.  The
per-iteration stream is a five-instruction body; the loop runs `N := P+1` rounds with source `a := t`. -/

/-- The head at-least-one clause's per-iteration body. -/
def aloHeadBody : List LInstr := [.spliceA, .spliceJ, .bit true, .bit false, .bit true]

/-- Its round-`p` denotation is exactly the clause's per-`p` literal stream. -/
theorem aloHead_prog2Out (t p : ℕ) :
    prog2Out aloHeadBody t p = encodeNat t ++ (encodeNat p ++ (encodeNat 1 ++ [true])) := by
  show prog2OutN aloHeadBody t p 5 = _
  simp [prog2OutN, instr2Out, aloHeadBody, encodeNat, List.append_assoc]

/-- **The clause factors through the loop denotation.** -/
theorem aloHead_split (t P : ℕ) :
    encodeClause' (atLeastOne ((List.range (P + 1)).map (headVar t)))
      = encodeNat (P + 1) ++ loop2Out aloHeadBody t (P + 1) := by
  rw [encodeClause'_atLeastOne_head, loop2Out_eq_flatten]
  congr 2
  apply List.map_congr_left
  intro p hp
  exact (aloHead_prog2Out t p).symm

/-- **THE FIRST LOOPED FAMILY EMITTER.**  With the clause's count block already on the output, running
`loopProg2Machine aloHeadBody` (bound `P+1`, source `t`) completes **exactly** the head one-hot
at-least-one clause's coordinate encoding — `t` read from the source region, `p` from the live variable,
all counters restored. -/
theorem aloHead_family_run (t P : ℕ) (out : List Bool) :
    run (loopProg2Machine aloHeadBody)
      (lp2Clock aloHeadBody (P + 1) t (out ++ encodeNat (P + 1)).length)
      (init (loopProg2Machine aloHeadBody)
        (unaryD (P + 1) ++ (unaryD t ++ (jT (P + 1) 0
          ++ encodeD (out ++ encodeNat (P + 1))))))
      = ⟨(78, ⟨0, Nat.succ_pos _⟩, false), 2 * (P + 1) + 1,
          unaryD (P + 1) ++ (unaryD t ++ (unaryD (P + 1) ++ encodeD (out
            ++ encodeClause' (atLeastOne ((List.range (P + 1)).map (headVar t))))))⟩ := by
  rw [loopProg2_run, aloHead_split, List.append_assoc]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2