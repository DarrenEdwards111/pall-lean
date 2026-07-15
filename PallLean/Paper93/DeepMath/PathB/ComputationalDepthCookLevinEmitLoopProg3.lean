import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitFamilyBodies

/-!
# Cook–Levin M2 emitter — the triple-source looped emitter, and the at-most-one pair bodies

The last machine mechanism of the emitter toolkit: the at-most-one pair families quantify over pairs
`(i, j)`, `i < j` — per outer index `i`, an inner run over `j = i+1..P` needs **two static sources**
(`t` and `i`) besides the live variable.  Two observations keep the machine small:

* **open splices subsume closed ones**: `encodeNat v = 1^v ++ [false]`, so a splice emitting only the
  `1^v` block (`.spAo`/`.spCo`/`.spJo`) followed by `.bit false` gives the closed `encodeNat`; the
  machine needs **no closing-`false` paths at all** — a splice track is find/mark/seek/snoc cycles
  ending directly in the heal walk;
* **the fused splice**: `[.spCo, .bit true, .spJo, .bit false]` emits `1^c · 1 · 1^k · 0 =
  encodeNat (c + 1 + k)` — the pair's second coordinate `j = i + 1 + d` splices with **no third live
  variable and no subtraction**, from the static `i` and the live `d`.

`loopProg3Machine body` runs `for k in 0..N-1: execute body` on the layout
`cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out)))`.  **Top theorem**
(`loopProg3_run`): self-halting at the explicit polynomial clock with the three-source denotation
appended, bound healed, both sources untouched, variable saturated.  **The at-most-one pair bodies**:
`amoPairHeadBody`/`amoPairStateBody` emit `encodeClause'` of the pair `(i, i+1+d)` per round
(`encodeClause'_amoPair_head/_state` consumed via the fused splice), and
`amoPairHead_family_run`/`amoPairState_family_run` run one inner row of the triangular family —
`(i, j)` for `j = i+1..i+R` — in a single machine run.  The outer `i`-chaining (rows are separate runs,
every region restored) is the sequencing layer's, with the other families.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat encodeNat_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies

/-! ## The triple-source instruction set and its denotation -/

/-- A triple-source emitter instruction: a fixed bit, or an **open** splice (the `1^v` block only) of
the first source, second source, or live variable. -/
inductive L3Instr where
  | bit (b : Bool)
  | spAo
  | spCo
  | spJo
deriving DecidableEq

def L3Instr.bitVal : L3Instr → Bool
  | .bit b => b
  | _ => false

/-- One instruction's output at source values `a, c`, round index `k`. -/
def instr3Out (a c k : ℕ) : L3Instr → List Bool
  | .bit b => [b]
  | .spAo => List.replicate a true
  | .spCo => List.replicate c true
  | .spJo => List.replicate k true

def prog3OutN (body : List L3Instr) (a c k : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => prog3OutN body a c k n ++ instr3Out a c k (body.getD n .spJo)

def prog3Out (body : List L3Instr) (a c k : ℕ) : List Bool := prog3OutN body a c k body.length

def loop3OutN (body : List L3Instr) (a c : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => loop3OutN body a c k ++ prog3Out body a c k

def loop3Out (body : List L3Instr) (a c N : ℕ) : List Bool := loop3OutN body a c N

theorem loop3Out_eq_flatten (body : List L3Instr) (a c N : ℕ) :
    loop3Out body a c N = ((List.range N).map (fun k => prog3Out body a c k)).flatten := by
  show loop3OutN body a c N = _
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show loop3OutN body a c (N + 1) = loop3OutN body a c N ++ prog3Out body a c N from rfl,
      ih, List.range_succ, List.map_append, List.flatten_append]
    simp

/-! ### The `prog3Out` homomorphism algebra -/

def bitsI3 (l : List Bool) : List L3Instr := l.map .bit

theorem prog3Out_eq_flatten (body : List L3Instr) (a c k : ℕ) :
    prog3Out body a c k = (body.map (instr3Out a c k)).flatten := by
  show prog3OutN body a c k body.length = _
  suffices h : ∀ n, n ≤ body.length →
      prog3OutN body a c k n = ((body.take n).map (instr3Out a c k)).flatten by
    rw [h body.length (le_refl _), List.take_length]
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show prog3OutN body a c k (n + 1)
        = prog3OutN body a c k n ++ instr3Out a c k (body.getD n .spJo) from rfl,
      ih (by omega), take_snoc_getD body .spJo n (by omega), List.map_append,
      List.flatten_append]
    simp

theorem prog3Out_append (b1 b2 : List L3Instr) (a c k : ℕ) :
    prog3Out (b1 ++ b2) a c k = prog3Out b1 a c k ++ prog3Out b2 a c k := by
  simp [prog3Out_eq_flatten, List.map_append]

theorem prog3Out_bits (l : List Bool) (a c k : ℕ) : prog3Out (bitsI3 l) a c k = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [show bitsI3 (b :: bs) = [.bit b] ++ bitsI3 bs from rfl, prog3Out_append, ih]
    rfl

/-! ### The closed and fused splice segments -/

/-- Closed splice of the first source: `encodeNat a`. -/
def sA : List L3Instr := [.spAo, .bit false]

/-- Closed splice of the second source: `encodeNat c`. -/
def sC : List L3Instr := [.spCo, .bit false]

/-- Closed splice of the live variable: `encodeNat k`. -/
def sJ : List L3Instr := [.spJo, .bit false]

/-- **The fused splice**: `encodeNat (c + 1 + k)` — the pair's second coordinate. -/
def sCJ : List L3Instr := [.spCo, .bit true, .spJo, .bit false]

theorem prog3Out_sA (a c k : ℕ) : prog3Out sA a c k = encodeNat a := by
  simp [sA, prog3Out_eq_flatten, instr3Out, encodeNat]

theorem prog3Out_sC (a c k : ℕ) : prog3Out sC a c k = encodeNat c := by
  simp [sC, prog3Out_eq_flatten, instr3Out, encodeNat]

theorem prog3Out_sJ (a c k : ℕ) : prog3Out sJ a c k = encodeNat k := by
  simp [sJ, prog3Out_eq_flatten, instr3Out, encodeNat]

theorem prog3Out_sCJ (a c k : ℕ) : prog3Out sCJ a c k = encodeNat (c + 1 + k) := by
  simp only [sCJ, prog3Out_eq_flatten, List.map_cons, List.map_nil, instr3Out,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show c + 1 + k = c + (1 + k) from by omega]
  show _ = List.replicate (c + (1 + k)) true ++ [false]
  rw [List.replicate_add, List.replicate_add]
  simp

/-! ## The four-region lift layer -/

theorem liftJ3 (A B C X : List Bool) {qa qb qc p : ℕ} (ha : A.length = qa)
    (hb : B.length = qb) (hc : C.length = qc) {w : Bool} (h : X.getD p false = w) :
    (A ++ (B ++ (C ++ X))).getD (qa + (qb + (qc + p))) false = w := by
  exact liftJ A _ ha (liftJ2 B C X hb hc h)

theorem writeAt_append_right3 (A B C X : List Bool) (qa qb qc p : ℕ) (w : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hp : p < X.length) :
    writeAt (A ++ (B ++ (C ++ X))) (qa + (qb + (qc + p))) w
      = A ++ (B ++ (C ++ writeAt X p w)) := by
  rw [writeAt_append_right A _ qa (qb + (qc + p)) w ha
      (by simp only [List.length_append]; omega),
    writeAt_append_right2 B C X qb qc p w hb hc hp]

theorem preD4_data_eq (A B C D out : List Bool) (q i : ℕ)
    (hq : A.length + B.length + C.length + D.length = q) (h : i < out.length) :
    (A ++ (B ++ (C ++ (D ++ encodeD out)))).getD (q + 2 * i) false
      = (A ++ (B ++ (C ++ (D ++ encodeD out)))).getD (q + 2 * i + 1) false := by
  have := preD_data_eq (A ++ (B ++ (C ++ D))) out q i
    (by simp only [List.length_append]; omega) h
  simpa [List.append_assoc] using this

theorem preD4_mark_lo (A B C D out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length = q) :
    (A ++ (B ++ (C ++ (D ++ encodeD out)))).getD (q + 2 * out.length) false = false := by
  have := preD_mark_lo (A ++ (B ++ (C ++ D))) out q (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem preD4_mark_hi (A B C D out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length = q) :
    (A ++ (B ++ (C ++ (D ++ encodeD out)))).getD (q + 2 * out.length + 1) false = true := by
  have := preD_mark_hi (A ++ (B ++ (C ++ D))) out q (by simp only [List.length_append]; omega)
  simpa [List.append_assoc] using this

theorem writes_snoc4 (A B C D out : List Bool) (q : ℕ)
    (hq : A.length + B.length + C.length + D.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ (D ++ encodeD out))))
        (q + 2 * out.length) b) (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false)
        (q + 2 * out.length + 3) true
      = A ++ (B ++ (C ++ (D ++ encodeD (out ++ [b])))) := by
  have h := writes_snoc (A ++ (B ++ (C ++ D))) out q
    (by simp only [List.length_append]; omega) b
  simpa [List.append_assoc] using h

theorem W4_append_right3 (A B C X : List Bool) (qa qb qc p : ℕ) (b1 b2 b3 b4 : Bool)
    (ha : A.length = qa) (hb : B.length = qb) (hc : C.length = qc) (hp : p + 3 < X.length) :
    writeAt (writeAt (writeAt (writeAt (A ++ (B ++ (C ++ X))) (qa + (qb + (qc + p))) b1)
        (qa + (qb + (qc + p)) + 1) b2) (qa + (qb + (qc + p)) + 2) b3)
        (qa + (qb + (qc + p)) + 3) b4
      = A ++ (B ++ (C ++ writeAt (writeAt (writeAt (writeAt X p b1) (p + 1) b2)
          (p + 2) b3) (p + 3) b4)) := by
  have hl1 : (writeAt X p b1).length = X.length := by
    rw [writeAt_of_lt b1 (by omega), List.length_set]
  have hl2 : (writeAt (writeAt X p b1) (p + 1) b2).length = X.length := by
    rw [writeAt_of_lt b2 (by omega), List.length_set, hl1]
  have hl3 : (writeAt (writeAt (writeAt X p b1) (p + 1) b2) (p + 2) b3).length = X.length := by
    rw [writeAt_of_lt b3 (by omega), List.length_set, hl2]
  rw [writeAt_append_right3 A B C X qa qb qc p b1 ha hb hc (by omega),
    show qa + (qb + (qc + p)) + 1 = qa + (qb + (qc + (p + 1))) from by omega,
    writeAt_append_right3 A B C _ qa qb qc (p + 1) b2 ha hb hc (by rw [hl1]; omega),
    show qa + (qb + (qc + p)) + 2 = qa + (qb + (qc + (p + 2))) from by omega,
    writeAt_append_right3 A B C _ qa qb qc (p + 2) b3 ha hb hc (by rw [hl2]; omega),
    show qa + (qb + (qc + p)) + 3 = qa + (qb + (qc + (p + 3))) from by omega,
    writeAt_append_right3 A B C _ qa qb qc (p + 3) b4 ha hb hc (by rw [hl3]; omega)]

/-! ## The machine

Control: `Fin 97 × Fin (|body|+1) × Bool`.  Phase groups: `0/1` the loop find, `2` the four-way
dispatch, `3–16` the append track (four boundary-event scans), `17–36` the open splice-A track
(find/mark in the first source, four-event seek, snoc-`true` cycles, then the heal walk — **no closing
`false`**), `37–58` the open splice-C track, `59–82` the open splice-J track, `83–93` the in-place
increment, `94/95` heal the bound, `96` = halt. -/

def loopProg3Machine (body : List L3Instr) : Machine where
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
       else (if b then ((94, ⟨0, Nat.succ_pos _⟩, s.2.2), none, 3)
             else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then
      (if s.2.1.val < body.length then
        (match body.getD s.2.1.val .spJo with
         | .bit _ => ((3, s.2.1, s.2.2), none, 2)
         | .spAo => ((17, s.2.1, s.2.2), none, 2)
         | .spCo => ((37, s.2.1, s.2.2), none, 2)
         | .spJo => ((59, s.2.1, s.2.2), none, 2))
       else ((83, s.2.1, s.2.2), none, 2))
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
       else (if b then ((33, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
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
    else if s.1 = 32 then ((17, s.2.1, s.2.2), some true, 3)
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
       else (if b then ((53, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
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
    else if s.1 = 52 then ((37, s.2.1, s.2.2), some true, 3)
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
       else (if b then ((75, s.2.1, s.2.2), none, 3) else ((96, s.2.1, s.2.2), none, 2)))
    else if s.1 = 67 then ((68, s.2.1, b), none, 1)
    else if s.1 = 68 then
      (if b = s.2.2 then ((67, s.2.1, s.2.2), none, 1) else ((69, s.2.1, s.2.2), none, 1))
    else if s.1 = 69 then ((70, s.2.1, b), none, 1)
    else if s.1 = 70 then
      (if b = s.2.2 then ((69, s.2.1, s.2.2), none, 1) else ((71, s.2.1, s.2.2), none, 0))
    else if s.1 = 71 then ((72, s.2.1, s.2.2), some true, 1)
    else if s.1 = 72 then ((73, s.2.1, s.2.2), some true, 1)
    else if s.1 = 73 then ((74, s.2.1, s.2.2), some false, 1)
    else if s.1 = 74 then ((59, s.2.1, s.2.2), some true, 3)
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
    else if s.1 = 93 then ((0, ⟨0, Nat.succ_pos _⟩, false), some true, 3)
    else if s.1 = 94 then ((95, s.2.1, b), none, 1)
    else if s.1 = 95 then
      (if s.2.2 then
        (if b then ((96, s.2.1, false), none, 2) else ((94, s.2.1, true), some true, 1))
       else (if b then ((96, s.2.1, false), none, 2) else ((96, s.2.1, false), none, 2)))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_lp3 (body : List L3Instr) (t : List Bool) :
    init (loopProg3Machine body) t = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, t⟩ := rfl

/-! ### Dispatch step lemmas -/

section Steps
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem l3_dispatch_bit {b : Bool} (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .bit b) :
    run (loopProg3Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .bit b := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3Machine, moveHead, h, hp']

theorem l3_dispatch_spAo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spAo) :
    run (loopProg3Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(17, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spAo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3Machine, moveHead, h, hp']

theorem l3_dispatch_spCo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spCo) :
    run (loopProg3Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(37, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spCo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3Machine, moveHead, h, hp']

theorem l3_dispatch_spJo (h : idx.val < body.length)
    (hp : body.getD idx.val .spJo = .spJo) :
    run (loopProg3Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(59, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  have hp' : body[(idx : ℕ)]'h = .spJo := by
    rwa [List.getD_eq_getElem body .spJo h] at hp
  simp [step, loopProg3Machine, moveHead, h, hp']

theorem l3_dispatch_incr (h : ¬(idx.val < body.length)) :
    run (loopProg3Machine body) 1 ⟨(2, idx, s), p, T⟩ = ⟨(83, idx, s), p, T⟩ := by
  rw [run_succ, run_zero]
  simp [step, loopProg3Machine, moveHead, h]

end Steps

/-! ### The generated pair-step layer -/

section Steps3
variable {body : List L3Instr} {idx : Fin (body.length + 1)} {s : Bool} {p : ℕ}
  {T : List Bool}

theorem l3_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(94, ⟨0, Nat.succ_pos _⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(0, idx, s), p, T⟩
      = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipB1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(3, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossB1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(3, idx, s), p, T⟩ = ⟨(5, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipA1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(17, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(17, idx, s), p, T⟩ = ⟨(19, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(17, idx, s), p, T⟩
      = ⟨(18, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphA1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(33, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(33, idx, s), p, T⟩ = ⟨(35, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(33, idx, s), p, T⟩
      = ⟨(34, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipC1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(37, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(37, idx, s), p, T⟩ = ⟨(39, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(37, idx, s), p, T⟩
      = ⟨(38, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipC2 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(39, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(39, idx, s), p, T⟩ = ⟨(41, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(39, idx, s), p, T⟩
      = ⟨(40, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphC1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(53, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshC1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(53, idx, s), p, T⟩ = ⟨(55, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(53, idx, s), p, T⟩
      = ⟨(54, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphC2 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(55, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshC2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(55, idx, s), p, T⟩ = ⟨(57, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(55, idx, s), p, T⟩
      = ⟨(56, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipJr1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(59, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossJr1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(59, idx, s), p, T⟩ = ⟨(61, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(59, idx, s), p, T⟩
      = ⟨(60, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipJr2 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(61, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossJr2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(61, idx, s), p, T⟩ = ⟨(63, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(61, idx, s), p, T⟩
      = ⟨(62, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipJr3 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(63, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossJr3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(63, idx, s), p, T⟩ = ⟨(65, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(63, idx, s), p, T⟩
      = ⟨(64, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphJ1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(75, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshJ1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(75, idx, s), p, T⟩ = ⟨(77, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(75, idx, s), p, T⟩
      = ⟨(76, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphJ2 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(77, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshJ2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(77, idx, s), p, T⟩ = ⟨(79, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(77, idx, s), p, T⟩
      = ⟨(78, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skiphJ3 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(79, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crosshJ3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(79, idx, s), p, T⟩ = ⟨(81, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(79, idx, s), p, T⟩
      = ⟨(80, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipi1 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(83, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossi1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(83, idx, s), p, T⟩ = ⟨(85, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(83, idx, s), p, T⟩
      = ⟨(84, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipi2 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(85, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossi2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(85, idx, s), p, T⟩ = ⟨(87, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(85, idx, s), p, T⟩
      = ⟨(86, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipi3 (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(87, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_crossi3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(87, idx, s), p, T⟩ = ⟨(89, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(87, idx, s), p, T⟩
      = ⟨(88, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanB2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(5, idx, s), p, T⟩
      = ⟨(5, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanB3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(7, idx, s), p, T⟩
      = ⟨(7, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanB4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(9, idx, s), p, T⟩
      = ⟨(9, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanB5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(11, idx, s), p, T⟩
      = ⟨(11, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanA2 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(21, idx, s), p, T⟩
      = ⟨(21, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanA3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(23, idx, s), p, T⟩
      = ⟨(23, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanA4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(25, idx, s), p, T⟩
      = ⟨(25, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanA5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(27, idx, s), p, T⟩
      = ⟨(27, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanC3 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(43, idx, s), p, T⟩
      = ⟨(43, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanC4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(45, idx, s), p, T⟩
      = ⟨(45, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanC5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(47, idx, s), p, T⟩
      = ⟨(47, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanJ4 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(67, idx, s), p, T⟩
      = ⟨(67, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_scanJ5 (h : T.getD p false = T.getD (p + 1) false) :
    run (loopProg3Machine body) 2 ⟨(69, idx, s), p, T⟩
      = ⟨(69, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_crossSB2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(5, idx, s), p, T⟩ = ⟨(7, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(5, idx, s), p, T⟩
      = ⟨(6, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSB3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(7, idx, s), p, T⟩ = ⟨(9, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSB4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(9, idx, s), p, T⟩ = ⟨(11, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(9, idx, s), p, T⟩
      = ⟨(10, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSA2 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(21, idx, s), p, T⟩ = ⟨(23, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(21, idx, s), p, T⟩
      = ⟨(22, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSA3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(23, idx, s), p, T⟩ = ⟨(25, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(23, idx, s), p, T⟩
      = ⟨(24, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSA4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(25, idx, s), p, T⟩ = ⟨(27, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(25, idx, s), p, T⟩
      = ⟨(26, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSC3 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(43, idx, s), p, T⟩ = ⟨(45, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(43, idx, s), p, T⟩
      = ⟨(44, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSC4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(45, idx, s), p, T⟩ = ⟨(47, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(45, idx, s), p, T⟩
      = ⟨(46, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_crossSJ4 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(67, idx, s), p, T⟩ = ⟨(69, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(67, idx, s), p, T⟩
      = ⟨(68, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2']

theorem l3_detectB5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(11, idx, s), p, T⟩ = ⟨(13, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(11, idx, s), p, T⟩
      = ⟨(12, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l3_detectA5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(27, idx, s), p, T⟩ = ⟨(29, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(27, idx, s), p, T⟩
      = ⟨(28, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l3_detectC5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(47, idx, s), p, T⟩ = ⟨(49, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(47, idx, s), p, T⟩
      = ⟨(48, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l3_detectJ5 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(69, idx, s), p, T⟩ = ⟨(71, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(69, idx, s), p, T⟩
      = ⟨(70, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, loopProg3Machine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem l3_skipAm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(19, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_markA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(19, idx, s), p, T⟩
      = ⟨(21, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneA (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(19, idx, s), p, T⟩ = ⟨(33, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(19, idx, s), p, T⟩
      = ⟨(20, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipCm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(41, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_markC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(41, idx, s), p, T⟩
      = ⟨(43, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneC (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(41, idx, s), p, T⟩ = ⟨(53, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(41, idx, s), p, T⟩
      = ⟨(42, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_skipJm (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(65, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_markJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(65, idx, s), p, T⟩
      = ⟨(67, idx, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneJ (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(65, idx, s), p, T⟩ = ⟨(75, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(65, idx, s), p, T⟩
      = ⟨(66, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_healA (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(35, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneHealA (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(35, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(35, idx, s), p, T⟩
      = ⟨(36, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2, h]

theorem l3_healC (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(57, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneHealC (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(57, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(57, idx, s), p, T⟩
      = ⟨(58, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2, h]

theorem l3_healJ (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(81, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneHealJ (h : idx.val + 1 < body.length + 1)
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(81, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(81, idx, s), p, T⟩
      = ⟨(82, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2, h]

theorem l3_four_TA :
    run (loopProg3Machine body) 4 ⟨(29, idx, s), p, T⟩
      = ⟨(17, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3Machine body) ⟨(29, idx, s), p, T⟩
      = ⟨(30, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3Machine body) ⟨(30, idx, s), p', T'⟩
      = ⟨(31, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3Machine body) ⟨(31, idx, s), p', T'⟩
      = ⟨(32, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3Machine body) ⟨(32, idx, s), p', T'⟩
      = ⟨(17, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem l3_four_TC :
    run (loopProg3Machine body) 4 ⟨(49, idx, s), p, T⟩
      = ⟨(37, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3Machine body) ⟨(49, idx, s), p, T⟩
      = ⟨(50, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3Machine body) ⟨(50, idx, s), p', T'⟩
      = ⟨(51, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3Machine body) ⟨(51, idx, s), p', T'⟩
      = ⟨(52, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3Machine body) ⟨(52, idx, s), p', T'⟩
      = ⟨(37, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

theorem l3_four_TJ :
    run (loopProg3Machine body) 4 ⟨(71, idx, s), p, T⟩
      = ⟨(59, idx, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3Machine body) ⟨(71, idx, s), p, T⟩
      = ⟨(72, idx, s), p + 1, writeAt T p true⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3Machine body) ⟨(72, idx, s), p', T'⟩
      = ⟨(73, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3Machine body) ⟨(73, idx, s), p', T'⟩
      = ⟨(74, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3Machine body) ⟨(74, idx, s), p', T'⟩
      = ⟨(59, idx, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e1, e2, e3, e4]

/-- The append snoc: the instruction's bit doubled plus the closing marker; advance. -/
theorem l3_four_bit (h : idx.val + 1 < body.length + 1) :
    run (loopProg3Machine body) 4 ⟨(13, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (body.getD idx.val .spJo).bitVal)
            (p + 1) (body.getD idx.val .spJo).bitVal) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e1 : step (loopProg3Machine body) ⟨(13, idx, s), p, T⟩
      = ⟨(14, idx, s), p + 1, writeAt T p (body.getD idx.val .spJo).bitVal⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  have e2 : ∀ p' T', step (loopProg3Machine body) ⟨(14, idx, s), p', T'⟩
      = ⟨(15, idx, s), p' + 1, writeAt T' p' (body.getD idx.val .spJo).bitVal⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e3 : ∀ p' T', step (loopProg3Machine body) ⟨(15, idx, s), p', T'⟩
      = ⟨(16, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e4 : ∀ p' T', step (loopProg3Machine body) ⟨(16, idx, s), p', T'⟩
      = ⟨(2, ⟨idx.val + 1, h⟩, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp [step, loopProg3Machine, moveHead, h]
  rw [e1, e2, e3, e4]

theorem l3_walkI (h1 : T.getD p false = true) :
    run (loopProg3Machine body) 2 ⟨(89, idx, s), p, T⟩ = ⟨(89, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(89, idx, s), p, T⟩
      = ⟨(90, idx, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg3Machine, moveHead, h1']
  rw [e0]
  simp only [step, loopProg3Machine, moveHead]; rfl

theorem l3_four_incr (h1 : T.getD p false = false) :
    run (loopProg3Machine body) 4 ⟨(89, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e89 : step (loopProg3Machine body) ⟨(89, idx, s), p, T⟩
      = ⟨(91, idx, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, loopProg3Machine, moveHead, h1']
  have e91 : ∀ p' T', step (loopProg3Machine body) ⟨(91, idx, s), p', T'⟩
      = ⟨(92, idx, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e92 : ∀ p' T', step (loopProg3Machine body) ⟨(92, idx, s), p', T'⟩
      = ⟨(93, idx, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  have e93 : ∀ p' T', step (loopProg3Machine body) ⟨(93, idx, s), p', T'⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e89, e91, e92, e93]

theorem l3_healB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopProg3Machine body) 2 ⟨(94, idx, s), p, T⟩
      = ⟨(94, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

theorem l3_doneFin (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopProg3Machine body) 2 ⟨(94, idx, s), p, T⟩ = ⟨(96, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step (loopProg3Machine body) ⟨(94, idx, s), p, T⟩
      = ⟨(95, idx, T.getD p false), p + 1, T⟩ := by
    simp only [step, loopProg3Machine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, loopProg3Machine, moveHead, h2]

end Steps3

/-! ### Scan run-invariants -/

theorem l3_skipBs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3Machine body) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipB hk.1 hk.2]
    rfl

theorem l3_skipB1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(3, idx, s), q, T⟩
      = ⟨(3, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipB1 (h k (by omega))]
    rfl

theorem l3_skipA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(17, idx, s), q, T⟩
      = ⟨(17, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipA1 (h k (by omega))]
    rfl

theorem l3_skiphA1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(33, idx, s), q, T⟩
      = ⟨(33, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphA1 (h k (by omega))]
    rfl

theorem l3_skipC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(37, idx, s), q, T⟩
      = ⟨(37, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipC1 (h k (by omega))]
    rfl

theorem l3_skipC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(39, idx, s), q, T⟩
      = ⟨(39, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipC2 (h k (by omega))]
    rfl

theorem l3_skiphC1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(53, idx, s), q, T⟩
      = ⟨(53, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphC1 (h k (by omega))]
    rfl

theorem l3_skiphC2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(55, idx, s), q, T⟩
      = ⟨(55, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphC2 (h k (by omega))]
    rfl

theorem l3_skipJr1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(59, idx, s), q, T⟩
      = ⟨(59, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipJr1 (h k (by omega))]
    rfl

theorem l3_skipJr2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(61, idx, s), q, T⟩
      = ⟨(61, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipJr2 (h k (by omega))]
    rfl

theorem l3_skipJr3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(63, idx, s), q, T⟩
      = ⟨(63, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipJr3 (h k (by omega))]
    rfl

theorem l3_skiphJ1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(75, idx, s), q, T⟩
      = ⟨(75, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphJ1 (h k (by omega))]
    rfl

theorem l3_skiphJ2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(77, idx, s), q, T⟩
      = ⟨(77, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphJ2 (h k (by omega))]
    rfl

theorem l3_skiphJ3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(79, idx, s), q, T⟩
      = ⟨(79, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skiphJ3 (h k (by omega))]
    rfl

theorem l3_skipi1s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(83, idx, s), q, T⟩
      = ⟨(83, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipi1 (h k (by omega))]
    rfl

theorem l3_skipi2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(85, idx, s), q, T⟩
      = ⟨(85, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipi2 (h k (by omega))]
    rfl

theorem l3_skipi3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(87, idx, s), q, T⟩
      = ⟨(87, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipi3 (h k (by omega))]
    rfl

theorem l3_scanB2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(5, idx, s), q, T⟩
      = ⟨(5, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanB2 (h k (by omega))]
    rfl

theorem l3_scanB3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(7, idx, s), q, T⟩
      = ⟨(7, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanB3 (h k (by omega))]
    rfl

theorem l3_scanB4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(9, idx, s), q, T⟩
      = ⟨(9, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanB4 (h k (by omega))]
    rfl

theorem l3_scanB5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(11, idx, s), q, T⟩
      = ⟨(11, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanB5 (h k (by omega))]
    rfl

theorem l3_scanA2s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(21, idx, s), q, T⟩
      = ⟨(21, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanA2 (h k (by omega))]
    rfl

theorem l3_scanA3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(23, idx, s), q, T⟩
      = ⟨(23, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanA3 (h k (by omega))]
    rfl

theorem l3_scanA4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(25, idx, s), q, T⟩
      = ⟨(25, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanA4 (h k (by omega))]
    rfl

theorem l3_scanA5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(27, idx, s), q, T⟩
      = ⟨(27, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanA5 (h k (by omega))]
    rfl

theorem l3_scanC3s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(43, idx, s), q, T⟩
      = ⟨(43, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanC3 (h k (by omega))]
    rfl

theorem l3_scanC4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(45, idx, s), q, T⟩
      = ⟨(45, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanC4 (h k (by omega))]
    rfl

theorem l3_scanC5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(47, idx, s), q, T⟩
      = ⟨(47, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanC5 (h k (by omega))]
    rfl

theorem l3_scanJ4s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(67, idx, s), q, T⟩
      = ⟨(67, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanJ4 (h k (by omega))]
    rfl

theorem l3_scanJ5s (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopProg3Machine body) (2 * k) ⟨(69, idx, s), q, T⟩
      = ⟨(69, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_scanJ5 (h k (by omega))]
    rfl

theorem l3_skipAms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3Machine body) (2 * k) ⟨(19, idx, s), q, T⟩
      = ⟨(19, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipAm hk.1 hk.2]
    rfl

theorem l3_skipCms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3Machine body) (2 * k) ⟨(41, idx, s), q, T⟩
      = ⟨(41, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipCm hk.1 hk.2]
    rfl

theorem l3_skipJms (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopProg3Machine body) (2 * k) ⟨(65, idx, s), q, T⟩
      = ⟨(65, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_skipJm hk.1 hk.2]
    rfl

theorem l3_walkIs (body : List L3Instr) (T : List Bool) (q k : ℕ)
    (idx : Fin (body.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run (loopProg3Machine body) (2 * k) ⟨(89, idx, s), q, T⟩
      = ⟨(89, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), l3_walkI (h k (by omega))]
    rfl

/-- The first-source heal (evolving `hlT`, one prefix). -/
theorem l3_healAs (body : List L3Instr) (P : List Bool) (N a : ℕ) (E : List Bool)
    (hP : P.length = 2 * N + 2) (idx : Fin (body.length + 1)) (s : Bool)
    (i : ℕ) (hi : i ≤ a) :
    run (loopProg3Machine body) (2 * i) ⟨(35, idx, s), 2 * N + 2, P ++ (hlT a 0 ++ E)⟩
      = ⟨(35, idx, if i = 0 then s else true), 2 * N + 2 + 2 * i, P ++ (hlT a i ++ E)⟩ := by
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
      l3_healA h1 h2, hw]
    rfl

/-- The second-source heal (evolving `hlT`, two prefixes). -/
theorem l3_healCs (body : List L3Instr) (P Q : List Bool) (N a c : ℕ) (E : List Bool)
    (hP : P.length = 2 * N + 2) (hQ : Q.length = 2 * a + 2) (idx : Fin (body.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ c) :
    run (loopProg3Machine body) (2 * i)
      ⟨(57, idx, s), 2 * N + 2 + 2 * a + 2, P ++ (Q ++ (hlT c 0 ++ E))⟩
      = ⟨(57, idx, if i = 0 then s else true), 2 * N + 2 + 2 * a + 2 + 2 * i,
          P ++ (Q ++ (hlT c i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (hlT c i ++ E))).getD (2 * N + 2 + 2 * a + 2 + 2 * i) false
        = true := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega]
      exact liftJ2 P Q _ hP hQ (hlE_pair_lo c i E (by omega))
    have h2 : (P ++ (Q ++ (hlT c i ++ E))).getD (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false
        = false := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 P Q _ hP hQ (hlE_pair_hi c i E (by omega))
    have hw : writeAt (P ++ (Q ++ (hlT c i ++ E))) (2 * N + 2 + 2 * a + 2 + 2 * i + 1) true
        = P ++ (Q ++ (hlT c (i + 1) ++ E)) := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega,
        writeAt_append_right2 P Q _ (2 * N + 2) (2 * a + 2) (2 * i + 1) true hP hQ
          (by rw [List.length_append, hlT_length c i (by omega)]; omega),
        hlT_heal c i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l3_healC h1 h2, hw]
    rfl

/-- The variable heal (evolving `jhT`, three prefixes). -/
theorem l3_healJs (body : List L3Instr) (P Q R : List Bool) (N a c k : ℕ) (E : List Bool)
    (hP : P.length = 2 * N + 2) (hQ : Q.length = 2 * a + 2) (hR : R.length = 2 * c + 2)
    (hk : k ≤ N) (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ k) :
    run (loopProg3Machine body) (2 * i)
      ⟨(81, idx, s), 2 * N + 2 + 2 * a + 2 + 2 * c + 2, P ++ (Q ++ (R ++ (jhT N k 0 ++ E)))⟩
      = ⟨(81, idx, if i = 0 then s else true), 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i,
          P ++ (Q ++ (R ++ (jhT N k i ++ E)))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (R ++ (jhT N k i ++ E)))).getD
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i) false = true := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i)) from by omega]
      exact liftJ3 P Q R _ hP hQ hR (jhE_pair_lo N k i E (by omega))
    have h2 : (P ++ (Q ++ (R ++ (jhT N k i ++ E)))).getD
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) false = false := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 P Q R _ hP hQ hR (jhE_pair_hi N k i E (by omega))
    have hw : writeAt (P ++ (Q ++ (R ++ (jhT N k i ++ E))))
        (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) true
        = P ++ (Q ++ (R ++ (jhT N k (i + 1) ++ E))) := by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))) from by omega,
        writeAt_append_right3 P Q R _ (2 * N + 2) (2 * a + 2) (2 * c + 2) (2 * i + 1) true
          hP hQ hR (by rw [List.length_append, jhT_length N k i (by omega) (by omega)]; omega),
        jhT_heal N k i E (by omega) (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l3_healJ h1 h2, hw]
    rfl

/-- The bound heal (the finale). -/
theorem l3_healBs (body : List L3Instr) (v : ℕ) (E : List Bool)
    (idx : Fin (body.length + 1)) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (loopProg3Machine body) (2 * i) ⟨(94, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(94, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      l3_healB (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The instruction lemmas

Round-`k` layout: `cntT N (k+1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))` — regions at
`[0, 2N+2)`, `[2N+2, 2N+2a+4)`, `[2N+2a+4, 2N+2a+2c+6)`, `[2N+2a+2c+6, 4N+2a+2c+8)`, output at
`4N+2a+2c+8`. -/

/-- **An append instruction**: dispatch, skip the bound, four boundary-event scans, snoc, advance. -/
theorem lp3_instr_bit (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) {b : Bool} (hp : body.getD idx.val .spJo = .bit b)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (4 * N + 2 * a + 2 * c + 2 * OUT.length + 15)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ [b]))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq4 : (cntT N (k + 1)).length + (unaryD a).length + (unaryD c).length + (jT N k).length
      = 4 * N + 2 * a + 2 * c + 8 := by
    rw [hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have b0 := l3_dispatch_bit (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) h hp
  have b1 := l3_skipB1s body
    (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at b1
  have b2 := l3_crossB1 (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N) (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have b3 := l3_scanB2s body
    (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) (2 * N + 2)
    a idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * i) false = true := by
        rw [← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_data a 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b4 := l3_crossSB2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
      (2 * N + 2) false a)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have b5 := l3_scanB3s body
    (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i)
            from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
            from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b6 := l3_crossSB3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
      (2 * N + 2 + 2 * a + 2) false c)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have b7 := l3_scanB4s body
    (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))) from by omega,
          ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have b8 := l3_crossSB4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have b9 := l3_scanB5s body
    (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) ((N - k) + OUT.length) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1)
            ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i))) from by omega,
            ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i) (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1)
            ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
          (4 * N + 2 * a + 2 * c + 8) (i - (N - k)) hq4 (by omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * ((N - k) + OUT.length)
      = 4 * N + 2 * a + 2 * c + 8 + 2 * OUT.length from by omega] at b9
  have b10 := l3_detectB5 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false ((N - k) + OUT.length))
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * OUT.length)
    (preD4_mark_lo (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
      (4 * N + 2 * a + 2 * c + 8) hq4)
    (preD4_mark_hi (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
      (4 * N + 2 * a + 2 * c + 8) hq4)
  have b11 := l3_four_bit (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) (by omega)
  rw [hp] at b11
  simp only [L3Instr.bitVal] at b11
  rw [writes_snoc4 (cntT N (k + 1)) (unaryD a) (unaryD c) (jT N k) OUT
    (4 * N + 2 * a + 2 * c + 8) hq4 b] at b11
  rw [show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 15
      = 1 + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + (2
          + (2 * ((N - k) + OUT.length) + (2 + 4)))))))))) from by omega,
    run_add, b0, run_add, b1, run_add, b2, run_add, b3, run_add, b4, run_add, b5,
    run_add, b6, run_add, b7, run_add, b8, run_add, b9, run_add, b10, b11]

/-! ### The shared splice sub-round clock -/

def lp3SpRounds (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => lp3SpRounds B i + (B + 2 * i)

/-! ### The open splice-A instruction -/

/-- One splice-A sub-round: mark the first source's pair `i`, seek out through the second source, the
variable, and the padding, emit a doubled `true`. -/
theorem lp3_spa_round (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k i : ℕ) (hi : i < a) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 14)
      ⟨(17, idx, s), 0, cntT N (k + 1)
        ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))⟩
      = ⟨(17, idx, false), 0, cntT N (k + 1)
          ++ (cntT a (i + 1) ++ (unaryD c ++ (jT N k
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (cntT a (i + 1)).length = 2 * a + 2 := cntT_length a (i + 1) (by omega)
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq4 : (cntT N (k + 1)).length + (cntT a (i + 1)).length + (unaryD c).length
      + (jT N k).length = 4 * N + 2 * a + 2 * c + 8 := by
    rw [hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s1 := l3_skipA1s body (cntT N (k + 1)
      ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) 0 N
    idx s (fun i' hi' => by simpa using cntE_lo N (k + 1) _ i' (by omega) hi')
  simp only [Nat.zero_add] at s1
  have s2 := l3_crossA1 (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have s3 := l3_skipAms body (cntT N (k + 1)
      ++ (cntT a i ++ (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * N + 2 + 2 * i' = 2 * N + 2 + (2 * i') from rfl]
      exact liftJ _ _ hR1 (cntE_mark_lo a i _ i' hi'), by
      rw [show 2 * N + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * i' + 1) from by omega]
      exact liftJ _ _ hR1 (cntE_mark_hi a i _ i' hi')⟩)
  have s4 := l3_markA (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * N + 2 + 2 * i)
    (T := cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
        exact liftJ _ _ hR1 (cntE_data a i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_data a i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1) ++ (cntT a i ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) (2 * N + 2 + 2 * i + 1) false
      = cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) := by
    rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (2 * i + 1) false hR1
        (by rw [List.length_append, cntT_length a i (by omega)]; omega),
      cntT_mark a i _ hi]
  rw [hw] at s4
  have s5 := l3_scanA2s body (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) (2 * N + 2 + 2 * i + 2)
    (a - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * i + 2 + 2 * i' = 2 * N + 2 + (2 * (i + 1) + 2 * i')
            from by omega]
        exact liftJ _ _ hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i') (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * i + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * (i + 1) + 2 * i' + 1)
            from by omega]
        exact liftJ _ _ hR1 (cntE_data a (i + 1) _ (2 * (i + 1) + 2 * i' + 1) (by omega)
          (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * i + 2 + 2 * (a - i - 1) = 2 * N + 2 + 2 * a from by omega] at s5
  have s6 := l3_crossSA2 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) (2 * N + 2 + 2 * i + 2)
      true (a - i - 1))
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (cntE_cm_lo a (i + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_cm_hi a (i + 1) _ (by omega)))
  have s7 := l3_scanA3s body (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) (2 * N + 2 + 2 * a + 2)
    c idx false
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' = 2 * N + 2 + (2 * a + 2 + 2 * i')
            from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i' + 1))
            from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s8 := l3_crossSA3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) (2 * N + 2 + 2 * a + 2)
      false c)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have s9 := l3_scanA4s body (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i'
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i')) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i' + 1))) from by omega,
          ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s10 := l3_crossSA4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have s11 := l3_scanA5s body (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i') false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i')))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i') (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i' + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) from by omega,
          show 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) + 1
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c) (jT N k)
          (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) (i' - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + i))
      = 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i) from by omega] at s11
  have hm1 := preD4_mark_lo (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4
  have hm2 := preD4_mark_hi (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4
  rw [hlen] at hm1 hm2
  have s12 := l3_detectA5 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false ((N - k) + (OUT.length + i)))
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc4 (cntT N (k + 1)) (cntT a (i + 1)) (unaryD c) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := l3_four_TA (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i))
    (T := cntT N (k + 1) ++ (cntT a (i + 1) ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
  rw [hsn] at s13
  rw [show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 14
      = 2 * N + (2 + (2 * i + (2 + (2 * (a - i - 1) + (2 + (2 * c + (2 + (2 * k
          + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4))))))))))) from by omega,
    run_add, s1, run_add, s2, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem lp3_spa_rounds (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ a) (s : Bool) :
    run (loopProg3Machine body) (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j)
      ⟨(17, idx, s), 0, cntT N (k + 1)
        ++ (cntT a 0 ++ (unaryD c ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(17, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (cntT a j ++ (unaryD c ++ (jT N k
            ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) (j + 1)
        = lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j
            + (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j) from rfl,
      show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j
        = 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 14 from by omega,
      run_add, ih (by omega), lp3_spa_round body idx N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

def lp3aCost (N a c L : ℕ) : ℕ :=
  1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * L + 14) a
    + ((2 * N + 2 * a + 4) + (2 * N + 2 * a + 4)))

/-- **An open splice-A instruction**: emit `1^a` from the first source (no closing `false`), heal it,
advance. -/
theorem lp3_instr_spAo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spAo)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (lp3aCost N a c OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have g0 := l3_dispatch_spAo (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) h hp
  have g1 := lp3_spa_rounds body idx N a c k hk OUT a (le_refl a) s
  have g2 := l3_skipA1s body (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))) 0 N idx
    (if a = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g2
  have g3 := l3_crossA1 (body := body) (idx := idx)
    (s := if N = 0 then (if a = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g4 := l3_skipAms body (cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))) (2 * N + 2) a idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl]
      exact liftJ _ _ hR1 (cntE_mark_lo a a _ i hi), by
      rw [show 2 * N + 2 + 2 * i + 1 = 2 * N + 2 + (2 * i + 1) from by omega]
      exact liftJ _ _ hR1 (cntE_mark_hi a a _ i hi)⟩)
  have g5 := l3_doneA (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (cntT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (cntE_cm_lo a a _ (le_refl a)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (cntE_cm_hi a a _ (le_refl a)))
  have g6 := l3_skiphA1s body (cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g6
  have g7 := l3_crosshA1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (hlT a 0 ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g8 := l3_healAs body (cntT N (k + 1)) N a
    (unaryD c ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))) hR1 idx false a
    (le_refl a)
  have g9 := l3_doneHealA (body := body) (idx := idx)
    (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (hlT a a ++ (unaryD c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate a true))))) (by omega)
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl]
        exact liftJ _ _ hR1 (hlE_cm_lo a _))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega]
        exact liftJ _ _ hR1 (hlE_cm_hi a _))
  rw [show lp3aCost N a c OUT.length
      = 1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) a
          + (2 * N + (2 + (2 * a + (2 + (2 * N + (2 + (2 * a + 2))))))))
      from by simp only [lp3aCost]; omega,
    run_add, g0, ← cntT_zero a, run_add, g1, run_add, g2, run_add, g3, run_add, g4,
    run_add, g5, ← hlT_zero a, run_add, g6, run_add, g7, run_add, g8, g9, hlT_last,
    cntT_zero a]

/-! ### The open splice-C instruction -/

theorem lp3_spc_round (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k i : ℕ) (hi : i < c) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 14)
      ⟨(37, idx, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))⟩
      = ⟨(37, idx, false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (cntT c (i + 1) ++ (jT N k
            ++ encodeD (OUT ++ List.replicate (i + 1) true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (cntT c (i + 1)).length = 2 * c + 2 := cntT_length c (i + 1) (by omega)
  have hq4 : (cntT N (k + 1)).length + (unaryD a).length + (cntT c (i + 1)).length
      + (jT N k).length = 4 * N + 2 * a + 2 * c + 8 := by
    rw [hR1, hQa, hQc, jT_length N k (by omega)]; omega
  have hlen : (OUT ++ List.replicate i true).length = OUT.length + i := by
    rw [List.length_append, List.length_replicate]
  have s1 := l3_skipC1s body (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))) 0 N
    idx s (fun i' hi' => by simpa using cntE_lo N (k + 1) _ i' (by omega) hi')
  simp only [Nat.zero_add] at s1
  have s2 := l3_crossC1 (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have s3 := l3_skipC2s body (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2) a idx false
    (fun i' hi' => by
      rw [show 2 * N + 2 + 2 * i' = 2 * N + 2 + (2 * i') from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i' (by omega) hi'))
  have s4 := l3_crossC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have s5 := l3_skipCms body (cntT N (k + 1)
      ++ (unaryD a ++ (cntT c i ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2) i idx false
    (fun i' hi' => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' = 2 * N + 2 + (2 * a + 2 + 2 * i')
          from by omega]
      exact liftJ2 _ _ _ hR1 hQa (cntE_mark_lo c i _ i' hi'), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i' + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i' + 1))
          from by omega]
      exact liftJ2 _ _ _ hR1 hQa (cntE_mark_hi c i _ i' hi')⟩)
  have s6 := l3_markC (body := body) (idx := idx) (s := if i = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * i)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa
          (cntE_data c i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1) ++ (unaryD a ++ (cntT c i
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * i + 1) false
      = cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
        from by omega,
      writeAt_append_right2 _ _ _ (2 * N + 2) (2 * a + 2) (2 * i + 1) false hR1 hQa
        (by rw [List.length_append, cntT_length c i (by omega)]; omega),
      cntT_mark c i _ hi]
  rw [hw] at s6
  have s7 := l3_scanC3s body (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * i + 2) (c - i - 1) idx true
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i'
            = 2 * N + 2 + (2 * a + 2 + (2 * (i + 1) + 2 * i')) from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_data c (i + 1) _ (2 * (i + 1) + 2 * i') (by omega)
          (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * i' + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * (i + 1) + 2 * i' + 1)) from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_data c (i + 1) _ (2 * (i + 1) + 2 * i' + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 2 + 2 * (c - i - 1)
      = 2 * N + 2 + 2 * a + 2 + 2 * c from by omega] at s7
  have s8 := l3_crossSC3 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * i + 2) true (c - i - 1))
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c (i + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c (i + 1) _ (by omega)))
  have s9 := l3_scanC4s body (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i' hi' => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i') false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i'
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i')) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i') (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
          ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i' + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i' + 1))) from by omega,
          ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k 0 _ (2 * i' + 1) (by omega) (by omega) (by omega))
      rw [e1, e2])
  have s10 := l3_crossSC4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2) false k)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega, ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega,
        ← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_hi N k 0 _ (by omega)))
  have s11 := l3_scanC5s body (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) ((N - k) + (OUT.length + i)) idx false
    (fun i' hi' => by
      rcases Nat.lt_or_ge i' (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i') false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i')))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i') (by omega)
            (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
            ++ (jT N k ++ encodeD (OUT ++ List.replicate i true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i' + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i' + 1)))
              from by omega, ← jsT_zero N k]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k 0 _ (2 * k + 2 + 2 * i' + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i'
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) from by omega,
          show 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) + 1
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i' - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT N (k + 1)) (unaryD a) (cntT c (i + 1)) (jT N k)
          (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) (i' - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + i))
      = 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i) from by omega] at s11
  have hm1 := preD4_mark_lo (cntT N (k + 1)) (unaryD a) (cntT c (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4
  have hm2 := preD4_mark_hi (cntT N (k + 1)) (unaryD a) (cntT c (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4
  rw [hlen] at hm1 hm2
  have s12 := l3_detectC5 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false ((N - k) + (OUT.length + i)))
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i)) hm1 hm2
  have hsn := writes_snoc4 (cntT N (k + 1)) (unaryD a) (cntT c (i + 1)) (jT N k)
    (OUT ++ List.replicate i true) (4 * N + 2 * a + 2 * c + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate i true ++ [true] : List Bool) = List.replicate (i + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := l3_four_TC (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + i))
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c (i + 1)
      ++ (jT N k ++ encodeD (OUT ++ List.replicate i true)))))
  rw [hsn] at s13
  rw [show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * i + 14
      = 2 * N + (2 + (2 * a + (2 + (2 * i + (2 + (2 * (c - i - 1) + (2 + (2 * k
          + (2 + (2 * ((N - k) + (OUT.length + i)) + (2 + 4))))))))))) from by omega,
    run_add, s1, run_add, s2, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem lp3_spc_rounds (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ c) (s : Bool) :
    run (loopProg3Machine body) (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j)
      ⟨(37, idx, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (cntT c 0 ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(37, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (cntT c j ++ (jT N k
            ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) (j + 1)
        = lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j
            + (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j) from rfl,
      show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j
        = 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 14 from by omega,
      run_add, ih (by omega), lp3_spc_round body idx N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

def lp3cCost (N a c L : ℕ) : ℕ :=
  1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * L + 14) c
    + ((2 * N + 2 * a + 2 * c + 6) + (2 * N + 2 * a + 2 * c + 6)))

/-- **An open splice-C instruction**: emit `1^c` from the second source, heal it, advance. -/
theorem lp3_instr_spCo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spCo)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (lp3cCost N a c OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have g0 := l3_dispatch_spCo (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) h hp
  have g1 := lp3_spc_rounds body idx N a c k hk OUT c (le_refl c) s
  have g2 := l3_skipC1s body (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) 0 N idx
    (if c = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g2
  have g3 := l3_crossC1 (body := body) (idx := idx)
    (s := if N = 0 then (if c = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g4 := l3_skipC2s body (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g5 := l3_crossC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g6 := l3_skipCms body (cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) (2 * N + 2 + 2 * a + 2)
    c idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega]
      exact liftJ2 _ _ _ hR1 hQa (cntE_mark_lo c c _ i hi), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i + 1 = 2 * N + 2 + (2 * a + 2 + (2 * i + 1))
          from by omega]
      exact liftJ2 _ _ _ hR1 hQa (cntE_mark_hi c c _ i hi)⟩)
  have g7 := l3_doneC (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (cntT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c c _ (le_refl c)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c c _ (le_refl c)))
  have g8 := l3_skiphC1s body (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g8
  have g9 := l3_crosshC1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g10 := l3_skiphC2s body (cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g11 := l3_crosshC2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (hlT c 0
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g12 := l3_healCs body (cntT N (k + 1)) (unaryD a) N a c
    (jT N k ++ encodeD (OUT ++ List.replicate c true)) hR1 hQa idx false c (le_refl c)
  have g13 := l3_doneHealC (body := body) (idx := idx)
    (s := if c = 0 then false else true) (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (hlT c c
      ++ (jT N k ++ encodeD (OUT ++ List.replicate c true))))) (by omega)
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (hlE_cm_lo c _))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega]
        exact liftJ2 _ _ _ hR1 hQa (hlE_cm_hi c _))
  rw [show lp3cCost N a c OUT.length
      = 1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) c
          + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * N + (2 + (2 * a + (2
            + (2 * c + 2))))))))))))
      from by simp only [lp3cCost]; omega,
    run_add, g0, ← cntT_zero c, run_add, g1, run_add, g2, run_add, g3, run_add, g4,
    run_add, g5, run_add, g6, run_add, g7, ← hlT_zero c, run_add, g8, run_add, g9,
    run_add, g10, run_add, g11, run_add, g12, g13, hlT_last, cntT_zero c]

/-! ### The open splice-J instruction -/

theorem lp3_spj_round (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k j' : ℕ) (hj : j' < k) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j' + 14)
      ⟨(59, idx, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))⟩
      = ⟨(59, idx, false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (unaryD c ++ (jsT N k (j' + 1)
            ++ encodeD (OUT ++ List.replicate (j' + 1) true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have hq4 : (cntT N (k + 1)).length + (unaryD a).length + (unaryD c).length
      + (jsT N k (j' + 1)).length = 4 * N + 2 * a + 2 * c + 8 := by
    rw [hR1, hQa, hQc, jsT_length N k (j' + 1) (by omega) (by omega)]; omega
  have hlen : (OUT ++ List.replicate j' true).length = OUT.length + j' := by
    rw [List.length_append, List.length_replicate]
  have s1 := l3_skipJr1s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))) 0 N idx s
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at s1
  have s2 := l3_crossJr1 (body := body) (idx := idx) (s := if N = 0 then s else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have s3 := l3_skipJr2s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true))))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have s4 := l3_crossJr2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have s5 := l3_skipJr3s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← cntT_zero c]
      exact liftJ2 _ _ _ hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have s6 := l3_crossJr3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have s7 := l3_skipJms body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) j' idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_mark_lo N k j' _ i hi), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_mark_hi N k j' _ i hi)⟩)
  have s8 := l3_markJ (body := body) (idx := idx) (s := if j' = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j')
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j'
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * j')) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k j' _ (2 * j') (by omega) (by omega) (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * j' + 1))) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc
          (jsE_data N k j' _ (2 * j' + 1) (by omega) (by omega) (by omega)))
  have hw : writeAt (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k j' ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1) false
      = cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))) := by
    rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 1
        = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * j' + 1))) from by omega,
      writeAt_append_right3 _ _ _ _ (2 * N + 2) (2 * a + 2) (2 * c + 2) (2 * j' + 1) false
        hR1 hQa hQc
        (by rw [List.length_append, jsT_length N k j' (by omega) (by omega)]; omega),
      jsT_mark N k j' _ hj (by omega)]
  rw [hw] at s8
  have s9 := l3_scanJ4s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2) (k - j' - 1) idx true
    (fun i hi => by
      have e1 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * (j' + 1) + 2 * i))) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i)
          (by omega) (by omega) (by omega))
      have e2 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
          ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
          (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i + 1) false = true := by
        rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * i + 1
            = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * (j' + 1) + 2 * i + 1)))
            from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_data N k (j' + 1) _ (2 * (j' + 1) + 2 * i + 1)
          (by omega) (by omega) (by omega))
      rw [e1, e2])
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2 + 2 * (k - j' - 1)
      = 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k from by omega] at s9
  have s10 := l3_crossSJ4 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * j' + 2) true (k - j' - 1))
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k (j' + 1) _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_hi N k (j' + 1) _ (by omega)))
  have s11 := l3_scanJ5s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) ((N - k) + (OUT.length + j')) idx false
    (fun i hi => by
      rcases Nat.lt_or_ge i (N - k) with hilt | hige
      · have e1 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i))) from by omega]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i)
            (by omega) (by omega) (by omega) (by omega))
        have e2 : (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true))))).getD
            (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1) false = false := by
          rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i + 1
              = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 2 + 2 * i + 1)))
              from by omega]
          exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_pad N k (j' + 1) _ (2 * k + 2 + 2 * i + 1)
            (by omega) (by omega) (by omega) (by omega))
        rw [e1, e2]
      · rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * i
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) from by omega,
          show 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) + 1
            = 4 * N + 2 * a + 2 * c + 8 + 2 * (i - (N - k)) + 1 from rfl]
        exact preD4_data_eq (cntT N (k + 1)) (unaryD a) (unaryD c) (jsT N k (j' + 1))
          (OUT ++ List.replicate j' true) (4 * N + 2 * a + 2 * c + 8) (i - (N - k)) hq4
          (by rw [List.length_append, List.length_replicate]; omega))
  rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2 + 2 * ((N - k) + (OUT.length + j'))
      = 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + j') from by omega] at s11
  have hm1 := preD4_mark_lo (cntT N (k + 1)) (unaryD a) (unaryD c) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 2 * c + 8) hq4
  have hm2 := preD4_mark_hi (cntT N (k + 1)) (unaryD a) (unaryD c) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 2 * c + 8) hq4
  rw [hlen] at hm1 hm2
  have s12 := l3_detectJ5 (body := body) (idx := idx)
    (s := storedD (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
      (2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 2) false ((N - k) + (OUT.length + j')))
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + j')) hm1 hm2
  have hsn := writes_snoc4 (cntT N (k + 1)) (unaryD a) (unaryD c) (jsT N k (j' + 1))
    (OUT ++ List.replicate j' true) (4 * N + 2 * a + 2 * c + 8) hq4 true
  rw [hlen, List.append_assoc,
    show (List.replicate j' true ++ [true] : List Bool) = List.replicate (j' + 1) true from by
      rw [← List.replicate_succ']] at hsn
  have s13 := l3_four_TJ (body := body) (idx := idx) (s := false)
    (p := 4 * N + 2 * a + 2 * c + 8 + 2 * (OUT.length + j'))
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k (j' + 1) ++ encodeD (OUT ++ List.replicate j' true)))))
  rw [hsn] at s13
  rw [show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j' + 14
      = 2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * j' + (2 + (2 * (k - j' - 1)
          + (2 + (2 * ((N - k) + (OUT.length + j')) + (2 + 4))))))))))) from by omega,
    run_add, s1, run_add, s2, run_add, s3, run_add, s4, run_add, s5, run_add, s6,
    run_add, s7, run_add, s8, run_add, s9, run_add, s10, run_add, s11, run_add, s12, s13]

theorem lp3_spj_rounds (body : List L3Instr) (idx : Fin (body.length + 1))
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (j : ℕ) (hj : j ≤ k) (s : Bool) :
    run (loopProg3Machine body) (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j)
      ⟨(59, idx, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jsT N k 0 ++ encodeD OUT)))⟩
      = ⟨(59, idx, if j = 0 then s else false), 0, cntT N (k + 1)
          ++ (unaryD a ++ (unaryD c ++ (jsT N k j
            ++ encodeD (OUT ++ List.replicate j true))))⟩ := by
  induction j with
  | zero => simp only [lp3SpRounds]; rw [run_zero]; simp
  | succ j ih =>
    rw [show lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) (j + 1)
        = lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) j
            + (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j) from rfl,
      show 4 * N + 2 * a + 2 * c + 2 * OUT.length + 14 + 2 * j
        = 4 * N + 2 * a + 2 * c + 2 * OUT.length + 2 * j + 14 from by omega,
      run_add, ih (by omega), lp3_spj_round body idx N a c k j (by omega) hk OUT _,
      if_neg (by omega)]

def lp3jCost (N a c k L : ℕ) : ℕ :=
  1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * L + 14) k
    + ((2 * N + 2 * a + 2 * c + 2 * k + 8) + (2 * N + 2 * a + 2 * c + 2 * k + 8)))

/-- **An open splice-J instruction**: emit `1^k` from the live variable, heal it, advance. -/
theorem lp3_instr_spJo (body : List L3Instr) (idx : Fin (body.length + 1))
    (h : idx.val < body.length) (hp : body.getD idx.val .spJo = .spJo)
    (N a c k : ℕ) (hk : k < N) (OUT : List Bool) (s : Bool) :
    run (loopProg3Machine body) (lp3jCost N a c k OUT.length)
      ⟨(2, idx, s), 0, cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (OUT ++ List.replicate k true))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have g0 := l3_dispatch_spJo (s := s) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD OUT)))) h hp
  have g1 := lp3_spj_rounds body idx N a c k hk OUT k (le_refl k) s
  have g2 := l3_skipJr1s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))) 0 N idx
    (if k = 0 then s else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g2
  have g3 := l3_crossJr1 (body := body) (idx := idx)
    (s := if N = 0 then (if k = 0 then s else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g4 := l3_skipJr2s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true))))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g5 := l3_crossJr2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g6 := l3_skipJr3s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← cntT_zero c]
      exact liftJ2 _ _ _ hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have g7 := l3_crossJr3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have g8 := l3_skipJms body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) k idx false
    (fun i hi => ⟨by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i)) from by omega]
      exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_mark_lo N k k _ i hi), by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * i + 1))) from by omega]
      exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_mark_hi N k k _ i hi)⟩)
  have g9 := l3_doneJ (body := body) (idx := idx) (s := if k = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jsT N k k ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k k _ (le_refl k)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_hi N k k _ (le_refl k)))
  have g10 := l3_skiphJ1s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))) 0 N idx false
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at g10
  have g11 := l3_crosshJ1 (body := body) (idx := idx) (s := if N = 0 then false else true)
    (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have g12 := l3_skiphJ2s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true))))) (2 * N + 2) a idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have g13 := l3_crosshJ2 (body := body) (idx := idx) (s := if a = 0 then false else true)
    (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have g14 := l3_skiphJ3s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))
    (2 * N + 2 + 2 * a + 2) c idx false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← cntT_zero c]
      exact liftJ2 _ _ _ hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have g15 := l3_crosshJ3 (body := body) (idx := idx) (s := if c = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k 0 ++ encodeD (OUT ++ List.replicate k true)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have g16 := l3_healJs body (cntT N (k + 1)) (unaryD a) (unaryD c) N a c k
    (encodeD (OUT ++ List.replicate k true)) hR1 hQa hQc (by omega) idx false k (le_refl k)
  have g17 := l3_doneHealJ (body := body) (idx := idx)
    (s := if k = 0 then false else true)
    (p := 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jhT N k k ++ encodeD (OUT ++ List.replicate k true))))) (by omega)
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jhE_m_lo N k _))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k + 1
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + (2 * k + 1))) from by omega]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jhE_m_hi N k _))
  rw [show lp3jCost N a c k OUT.length
      = 1 + (lp3SpRounds (4 * N + 2 * a + 2 * c + 2 * OUT.length + 14) k
          + (2 * N + (2 + (2 * a + (2 + (2 * c + (2 + (2 * k + (2 + (2 * N + (2 + (2 * a
            + (2 + (2 * c + (2 + (2 * k + 2))))))))))))))))
      from by simp only [lp3jCost]; omega,
    run_add, g0, ← jsT_zero, run_add, g1, run_add, g2, run_add, g3, run_add, g4,
    run_add, g5, run_add, g6, run_add, g7, run_add, g8, run_add, g9, ← jhT_zero,
    run_add, g10, run_add, g11, run_add, g12, run_add, g13, run_add, g14, run_add, g15,
    run_add, g16, g17, jhT_last, jsT_zero]

/-! ## The instruction segment, the round, and the loop -/

def lp3InstrCost (body : List L3Instr) (N a c k L : ℕ) (n : ℕ) : ℕ :=
  match body.getD n .spJo with
  | .bit _ => 4 * N + 2 * a + 2 * c + 2 * (L + (prog3OutN body a c k n).length) + 15
  | .spAo => lp3aCost N a c (L + (prog3OutN body a c k n).length)
  | .spCo => lp3cCost N a c (L + (prog3OutN body a c k n).length)
  | .spJo => lp3jCost N a c k (L + (prog3OutN body a c k n).length)

def lp3SegN (body : List L3Instr) (N a c k L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lp3SegN body N a c k L n + lp3InstrCost body N a c k L n

/-- **The segment invariant**: `n` instructions of round `k` executed. -/
theorem lp3_run_instrs (body : List L3Instr) (N a c k : ℕ) (hk : k < N)
    (out' : List Bool) (n : ℕ) (hn : n ≤ body.length) (s : Bool) :
    run (loopProg3Machine body) (lp3SegN body N a c k out'.length n)
      ⟨(2, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N (k + 1)
        ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out')))⟩
      = ⟨(2, ⟨n, by omega⟩, if n = 0 then s else false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k n))))⟩ := by
  induction n with
  | zero => simp only [lp3SegN]; rw [run_zero]; simp [prog3OutN]
  | succ n ih =>
    rw [show lp3SegN body N a c k out'.length (n + 1)
        = lp3SegN body N a c k out'.length n + lp3InstrCost body N a c k out'.length n
        from rfl,
      run_add, ih (by omega)]
    cases hp : body.getD n .spJo with
    | bit b =>
      have hin := lp3_instr_bit body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a c k hk (out' ++ prog3OutN body a c k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ [b] = prog3OutN body a c k (n + 1) from by
          simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3InstrCost, hp]
      rw [hin]
      simp
    | spAo =>
      have hin := lp3_instr_spAo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a c k hk (out' ++ prog3OutN body a c k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate a true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3InstrCost, hp]
      rw [hin]
      simp
    | spCo =>
      have hin := lp3_instr_spCo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a c k hk (out' ++ prog3OutN body a c k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate c true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3InstrCost, hp]
      rw [hin]
      simp
    | spJo =>
      have hin := lp3_instr_spJo body ⟨n, by omega⟩
        (show n < body.length from by omega) hp N a c k hk (out' ++ prog3OutN body a c k n)
        (if n = 0 then s else false)
      rw [List.length_append, List.append_assoc,
        show prog3OutN body a c k n ++ List.replicate k true = prog3OutN body a c k (n + 1)
          from by simp only [prog3OutN, hp]; rfl] at hin
      simp only [lp3InstrCost, hp]
      rw [hin]
      simp

def lp3RoundCost (body : List L3Instr) (N a c k L : ℕ) : ℕ :=
  (2 * k + 2) + (lp3SegN body N a c k L body.length + (2 * N + 2 * a + 2 * c + 2 * k + 11))

/-- **One loop round**: mark the bound's pair `k`, run the body (bits and open splices of `a`, `c`,
and the live value `k`), increment the variable in place. -/
theorem lp3_round (body : List L3Instr) (N a c k : ℕ) (hk : k < N) (out' : List Bool)
    (ptrIn : Fin (body.length + 1)) (s : Bool) :
    run (loopProg3Machine body) (lp3RoundCost body N a c k out'.length)
      ⟨(0, ptrIn, s), 0, cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out')))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT N (k + 1) ++ (unaryD a ++ (unaryD c ++ (jT N (k + 1)
            ++ encodeD (out' ++ prog3Out body a c k))))⟩ := by
  have hR1 : (cntT N (k + 1)).length = 2 * N + 2 := cntT_length N (k + 1) (by omega)
  have hQa : (unaryD a).length = 2 * a + 2 := unaryD_length a
  have hQc : (unaryD c).length = 2 * c + 2 := unaryD_length c
  have r1 := l3_skipBs body (cntT N k ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD out')))) 0 k ptrIn s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at r1
  have r2 := l3_markB (body := body) (idx := ptrIn) (s := if k = 0 then s else true)
    (p := 2 * k) (T := cntT N k ++ (unaryD a ++ (unaryD c ++ (jT N k ++ encodeD out'))))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hk] at r2
  have r3 := lp3_run_instrs body N a c k hk out' body.length (le_refl _) true
  have r4 := l3_dispatch_incr (body := body)
    (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if body.length = 0 then true else false) (p := 0)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (Nat.lt_irrefl _)
  have r5 := l3_skipi1s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))) 0 N
    ⟨body.length, Nat.lt_succ_self _⟩ (if body.length = 0 then true else false)
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at r5
  have r6 := l3_crossi1 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if N = 0 then (if body.length = 0 then true else false) else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  have r7 := l3_skipi2s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length))))) (2 * N + 2) a
    ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * i = 2 * N + 2 + (2 * i) from rfl, ← cntT_zero a]
      exact liftJ _ _ hR1 (cntE_lo a 0 _ i (by omega) hi))
  have r8 := l3_crossi2 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if a = 0 then false else true) (p := 2 * N + 2 + 2 * a)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (by rw [show 2 * N + 2 + 2 * a = 2 * N + 2 + (2 * a) from rfl, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_lo a 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 1 = 2 * N + 2 + (2 * a + 1) from by omega, ← cntT_zero a]
        exact liftJ _ _ hR1 (cntE_cm_hi a 0 _ (by omega)))
  have r9 := l3_skipi3s body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (2 * N + 2 + 2 * a + 2) c ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * i = 2 * N + 2 + (2 * a + 2 + 2 * i) from by omega,
        ← cntT_zero c]
      exact liftJ2 _ _ _ hR1 hQa (cntE_lo c 0 _ i (by omega) hi))
  have r10 := l3_crossi3 (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if c = 0 then false else true) (p := 2 * N + 2 + 2 * a + 2 + 2 * c)
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c = 2 * N + 2 + (2 * a + 2 + 2 * c)
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_lo c 0 _ (by omega)))
    (by rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 1 = 2 * N + 2 + (2 * a + 2 + (2 * c + 1))
          from by omega, ← cntT_zero c]
        exact liftJ2 _ _ _ hR1 hQa (cntE_cm_hi c 0 _ (by omega)))
  have r11 := l3_walkIs body (cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (2 * N + 2 + 2 * a + 2 + 2 * c + 2) k ⟨body.length, Nat.lt_succ_self _⟩ false
    (fun i hi => by
      rw [show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * i
          = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * i)) from by omega, ← jsT_zero N k]
      exact liftJ3 _ _ _ _ hR1 hQa hQc
        (jsE_data N k 0 _ (2 * i) (by omega) (by omega) (by omega)))
  have r12 := l3_four_incr (body := body) (idx := ⟨body.length, Nat.lt_succ_self _⟩)
    (s := if k = 0 then false else true)
    (p := 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)))
    (T := cntT N (k + 1) ++ (unaryD a ++ (unaryD c
      ++ (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)))))
    (by rw [← jsT_zero N k]
        exact liftJ3 _ _ _ _ hR1 hQa hQc (jsE_m_lo N k 0 _ (by omega)))
  rw [W4_append_right3 (cntT N (k + 1)) (unaryD a) (unaryD c)
      (jT N k ++ encodeD (out' ++ prog3OutN body a c k body.length)) (2 * N + 2)
      (2 * a + 2) (2 * c + 2) (2 * k) true true false true hR1 hQa hQc
      (by rw [List.length_append, jT_length N k (by omega)]; omega),
    jT_incr N k _ hk] at r12
  rw [show lp3RoundCost body N a c k out'.length
      = 2 * k + (2 + (lp3SegN body N a c k out'.length body.length + (1 + (2 * N + (2
          + (2 * a + (2 + (2 * c + (2 + (2 * k + 4))))))))))
      from by simp only [lp3RoundCost]; omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5, run_add, r6,
    run_add, r7, run_add, r8, run_add, r9, run_add, r10, run_add, r11,
    show 2 * N + 2 + 2 * a + 2 + 2 * c + 2 + 2 * k
      = 2 * N + 2 + (2 * a + 2 + (2 * c + 2 + 2 * k)) from by omega,
    r12, prog3Out]

def lp3ClockN (body : List L3Instr) (N a c Lout : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lp3ClockN body N a c Lout k
      + lp3RoundCost body N a c k (Lout + (loop3OutN body a c k).length)

/-- **The rounds invariant.** -/
theorem lp3_run_rounds (body : List L3Instr) (N a c : ℕ) (out : List Bool) (k : ℕ)
    (hk : k ≤ N) (s : Bool) :
    run (loopProg3Machine body) (lp3ClockN body N a c out.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N 0
        ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out)))⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT N k ++ (unaryD a ++ (unaryD c
            ++ (jT N k ++ encodeD (out ++ loop3OutN body a c k))))⟩ := by
  induction k with
  | zero => simp only [lp3ClockN]; rw [run_zero]; simp [loop3OutN]
  | succ k ih =>
    have hrd := lp3_round body N a c k (by omega) (out ++ loop3OutN body a c k)
      ⟨0, Nat.succ_pos _⟩ (if k = 0 then s else false)
    rw [List.length_append, List.append_assoc,
      show loop3OutN body a c k ++ prog3Out body a c k = loop3OutN body a c (k + 1)
        from rfl] at hrd
    rw [show lp3ClockN body N a c out.length (k + 1)
        = lp3ClockN body N a c out.length k
            + lp3RoundCost body N a c k (out.length + (loop3OutN body a c k).length)
        from rfl,
      run_add, ih (by omega), hrd, if_neg (by omega)]

def lp3Clock (body : List L3Instr) (N a c Lout : ℕ) : ℕ :=
  lp3ClockN body N a c Lout N + (2 * N + (2 + (2 * N + 2)))

/-- **THE TRIPLE-SOURCE LOOPED EMITTER RUNS TO COMPLETION.** -/
theorem loopProg3_run (body : List L3Instr) (N a c : ℕ) (out : List Bool) :
    run (loopProg3Machine body) (lp3Clock body N a c out.length)
      (init (loopProg3Machine body)
        (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out)))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 1,
          unaryD N ++ (unaryD a ++ (unaryD c
            ++ (unaryD N ++ encodeD (out ++ loop3Out body a c N))))⟩ := by
  rw [init_lp3]
  rw [show (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))) : List Bool)
      = cntT N 0 ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out))) from by
    rw [cntT_zero]]
  simp only [lp3Clock]
  have f1 := l3_skipBs body (cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))) 0 N
    ⟨0, Nat.succ_pos _⟩ false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := l3_doneB (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have f3 := l3_healBs body N (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N))))
    ⟨0, Nat.succ_pos _⟩ false N (le_refl N)
  have f4 := l3_doneFin (body := body) (idx := ⟨0, Nat.succ_pos _⟩)
    (s := if N = 0 then false else true) (p := 2 * N)
    (T := hlT N N ++ (unaryD a ++ (unaryD c
      ++ (jT N N ++ encodeD (out ++ loop3OutN body a c N)))))
    (hlE_cm_lo N _) (hlE_cm_hi N _)
  rw [run_add, lp3_run_rounds body N a c out N (le_refl N) false, ite_self,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last, jT_full,
    show loop3Out body a c N = loop3OutN body a c N from rfl]

theorem loopProg3_halted (body : List L3Instr) (N a c : ℕ) (out : List Bool) :
    (loopProg3Machine body).halt
      (run (loopProg3Machine body) (lp3Clock body N a c out.length)
        (init (loopProg3Machine body)
          (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out)))))).st = true := by
  rw [loopProg3_run]; rfl

theorem loopProg3_output (body : List L3Instr) (N a c : ℕ) (out : List Bool) :
    (run (loopProg3Machine body) (lp3Clock body N a c out.length)
      (init (loopProg3Machine body)
        (unaryD N ++ (unaryD a ++ (unaryD c ++ (jT N 0 ++ encodeD out)))))).tp
      = unaryD N ++ (unaryD a ++ (unaryD c
          ++ (unaryD N ++ encodeD (out ++ loop3Out body a c N)))) := by
  rw [loopProg3_run]

/-! ## Polynomial clock bounds -/

theorem prog3OutN_length_le (body : List L3Instr) (a c k n : ℕ) :
    (prog3OutN body a c k n).length ≤ n * (a + c + k + 1) := by
  induction n with
  | zero => simp [prog3OutN]
  | succ n ih =>
    rw [show prog3OutN body a c k (n + 1)
        = prog3OutN body a c k n ++ instr3Out a c k (body.getD n .spJo) from rfl,
      List.length_append]
    have hone : (instr3Out a c k (body.getD n .spJo)).length ≤ a + c + k + 1 := by
      cases body.getD n .spJo with
      | bit b => simp [instr3Out]
      | spAo => simp [instr3Out]; omega
      | spCo => simp [instr3Out]; omega
      | spJo => simp [instr3Out]; omega
    calc (prog3OutN body a c k n).length + (instr3Out a c k (body.getD n .spJo)).length
        ≤ n * (a + c + k + 1) + (a + c + k + 1) := Nat.add_le_add ih hone
      _ = (n + 1) * (a + c + k + 1) := by ring

theorem lp3SpRounds_le (B B' j J : ℕ) (hB : B ≤ B') (hj : j ≤ J) :
    lp3SpRounds B j ≤ j * (B' + 2 * J) := by
  induction j with
  | zero => simp [lp3SpRounds]
  | succ j ih =>
    calc lp3SpRounds B (j + 1) = lp3SpRounds B j + (B + 2 * j) := rfl
      _ ≤ j * (B' + 2 * J) + (B' + 2 * J) := Nat.add_le_add (ih (by omega)) (by omega)
      _ = (j + 1) * (B' + 2 * J) := by ring

/-- The per-instruction cap. -/
def lp3Cap (N a c LM : ℕ) : ℕ :=
  N * (4 * N + 2 * a + 2 * c + 2 * LM + 14 + 2 * N)
    + a * (4 * N + 2 * a + 2 * c + 2 * LM + 14 + 2 * a)
    + c * (4 * N + 2 * a + 2 * c + 2 * LM + 14 + 2 * c)
    + (8 * N + 4 * a + 4 * c + 17) + (4 * N + 4 * a + 4 * c + 13) + (4 * N + 4 * a + 9)
    + (4 * N + 2 * a + 2 * c + 2 * LM + 15)

theorem lp3InstrCost_le (body : List L3Instr) (N a c k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3InstrCost body N a c k L n ≤ lp3Cap N a c LM := by
  have hlen : (prog3OutN body a c k n).length ≤ body.length * (a + c + N + 1) :=
    le_trans (prog3OutN_length_le body a c k n) (Nat.mul_le_mul hn (by omega))
  cases hp : body.getD n .spJo with
  | bit b =>
    simp only [lp3InstrCost, hp, lp3Cap]
    omega
  | spAo =>
    have h1 := lp3SpRounds_le (4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 14)
      (4 * N + 2 * a + 2 * c + 2 * LM + 14) a a (by omega) (le_refl a)
    simp only [lp3InstrCost, hp, lp3aCost, lp3Cap]
    omega
  | spCo =>
    have h1 := lp3SpRounds_le (4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 14)
      (4 * N + 2 * a + 2 * c + 2 * LM + 14) c c (by omega) (le_refl c)
    simp only [lp3InstrCost, hp, lp3cCost, lp3Cap]
    omega
  | spJo =>
    have h1 := lp3SpRounds_le (4 * N + 2 * a + 2 * c
        + 2 * (L + (prog3OutN body a c k n).length) + 14)
      (4 * N + 2 * a + 2 * c + 2 * LM + 14) k N (by omega) (by omega)
    have h2 : k * (4 * N + 2 * a + 2 * c + 2 * LM + 14 + 2 * N)
        ≤ N * (4 * N + 2 * a + 2 * c + 2 * LM + 14 + 2 * N) :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [lp3InstrCost, hp, lp3jCost, lp3Cap]
    omega

theorem lp3SegN_le (body : List L3Instr) (N a c k L n LM : ℕ) (hk : k < N)
    (hn : n ≤ body.length) (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3SegN body N a c k L n ≤ n * lp3Cap N a c LM := by
  induction n with
  | zero => simp [lp3SegN]
  | succ n ih =>
    calc lp3SegN body N a c k L (n + 1)
        = lp3SegN body N a c k L n + lp3InstrCost body N a c k L n := rfl
      _ ≤ n * lp3Cap N a c LM + lp3Cap N a c LM :=
          Nat.add_le_add (ih (by omega))
            (lp3InstrCost_le body N a c k L n LM hk (by omega) hL)
      _ = (n + 1) * lp3Cap N a c LM := by ring

theorem loop3OutN_length_le (body : List L3Instr) (N a c k : ℕ) (hk : k ≤ N) :
    (loop3OutN body a c k).length ≤ k * (body.length * (a + c + N + 1)) := by
  induction k with
  | zero => simp [loop3OutN]
  | succ k ih =>
    rw [show loop3OutN body a c (k + 1) = loop3OutN body a c k ++ prog3Out body a c k
        from rfl, List.length_append]
    have hone : (prog3Out body a c k).length ≤ body.length * (a + c + N + 1) := by
      show (prog3OutN body a c k body.length).length ≤ _
      exact le_trans (prog3OutN_length_le body a c k body.length)
        (Nat.mul_le_mul_left _ (by omega))
    calc (loop3OutN body a c k).length + (prog3Out body a c k).length
        ≤ k * (body.length * (a + c + N + 1)) + body.length * (a + c + N + 1) :=
          Nat.add_le_add (ih (by omega)) hone
      _ = (k + 1) * (body.length * (a + c + N + 1)) := by ring

theorem lp3RoundCost_le (body : List L3Instr) (N a c k L LM : ℕ) (hk : k < N)
    (hL : L + body.length * (a + c + N + 1) ≤ LM) :
    lp3RoundCost body N a c k L
      ≤ body.length * lp3Cap N a c LM + (6 * N + 2 * a + 2 * c + 15) := by
  have h := lp3SegN_le body N a c k L body.length LM hk (le_refl _) hL
  simp only [lp3RoundCost]
  omega

/-- **The loop clock is polynomial.** -/
theorem lp3Clock_le (body : List L3Instr) (N a c Lout : ℕ) :
    lp3Clock body N a c Lout
      ≤ N * (body.length * lp3Cap N a c (Lout + N * (body.length * (a + c + N + 1))
            + body.length * (a + c + N + 1)) + (6 * N + 2 * a + 2 * c + 15))
        + (4 * N + 4) := by
  have hrounds : ∀ k, k ≤ N → lp3ClockN body N a c Lout k
      ≤ k * (body.length * lp3Cap N a c (Lout + N * (body.length * (a + c + N + 1))
            + body.length * (a + c + N + 1)) + (6 * N + 2 * a + 2 * c + 15)) := by
    intro k hk
    induction k with
    | zero => simp [lp3ClockN]
    | succ k ih =>
      have hLk : (Lout + (loop3OutN body a c k).length) + body.length * (a + c + N + 1)
          ≤ Lout + N * (body.length * (a + c + N + 1)) + body.length * (a + c + N + 1) := by
        have h1 : (loop3OutN body a c k).length ≤ k * (body.length * (a + c + N + 1)) :=
          loop3OutN_length_le body N a c k (by omega)
        have h2 : k * (body.length * (a + c + N + 1))
            ≤ N * (body.length * (a + c + N + 1)) := Nat.mul_le_mul_right _ (by omega)
        omega
      calc lp3ClockN body N a c Lout (k + 1)
          = lp3ClockN body N a c Lout k
              + lp3RoundCost body N a c k (Lout + (loop3OutN body a c k).length) := rfl
        _ ≤ k * (body.length * lp3Cap N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1)) + (6 * N + 2 * a + 2 * c + 15))
            + (body.length * lp3Cap N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1)) + (6 * N + 2 * a + 2 * c + 15)) :=
            Nat.add_le_add (ih (by omega))
              (lp3RoundCost_le body N a c k (Lout + (loop3OutN body a c k).length) _
                (by omega) hLk)
        _ = (k + 1) * (body.length * lp3Cap N a c (Lout + N * (body.length * (a + c + N + 1))
                + body.length * (a + c + N + 1)) + (6 * N + 2 * a + 2 * c + 15)) := by ring
  have h := hrounds N (le_refl N)
  simp only [lp3Clock]
  omega

/-! ## THE AT-MOST-ONE PAIR BODIES

`atMostOne`'s stream is triangular: for `i` ascending, pairs `(i, j)` with `j = i+1..P`.  One inner
row at fixed `(t, i)` is a loop over `d` with `j = i + 1 + d` — the fused splice.  Sources:
`a := t`, `c := i`, live `d`. -/

def amoPairHeadBody : List L3Instr :=
  bitsI3 [true, true, false] ++ (sA ++ (sC ++ (bitsI3 [true, false] ++ (bitsI3 [false]
    ++ (sA ++ (sCJ ++ (bitsI3 [true, false] ++ bitsI3 [false])))))))

def amoPairStateBody : List L3Instr :=
  bitsI3 [true, true, false] ++ (sA ++ (sC ++ (bitsI3 [true, true, false] ++ (bitsI3 [false]
    ++ (sA ++ (sCJ ++ (bitsI3 [true, true, false] ++ bitsI3 [false])))))))

/-- **The head pair clause factors**: round `d` of the `(t, i)` row emits the pair `(i, i+1+d)`. -/
theorem amoPairHead_prog3Out (t i d : ℕ) :
    prog3Out amoPairHeadBody t i d
      = encodeClause' [(headVar t i, false), (headVar t (i + 1 + d), false)] := by
  rw [encodeClause'_amoPair_head, amoPairHeadBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sC, prog3Out_sCJ]
  simp [encodeNat, List.append_assoc]

theorem amoPairState_prog3Out (t i d : ℕ) :
    prog3Out amoPairStateBody t i d
      = encodeClause' [(stateVar t i, false), (stateVar t (i + 1 + d), false)] := by
  rw [encodeClause'_amoPair_state, amoPairStateBody]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sC, prog3Out_sCJ]
  simp [encodeNat, List.append_assoc]

/-- One row of the head at-most-one triangle factors through the loop denotation. -/
theorem amoPairHead_split (t i R : ℕ) :
    loop3Out amoPairHeadBody t i R
      = ((List.range R).map (fun d =>
          encodeClause' [(headVar t i, false), (headVar t (i + 1 + d), false)])).flatten := by
  rw [loop3Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun d _ => amoPairHead_prog3Out t i d))

theorem amoPairState_split (t i R : ℕ) :
    loop3Out amoPairStateBody t i R
      = ((List.range R).map (fun d =>
          encodeClause' [(stateVar t i, false), (stateVar t (i + 1 + d), false)])).flatten := by
  rw [loop3Out_eq_flatten]
  exact congrArg List.flatten (List.map_congr_left (fun d _ => amoPairState_prog3Out t i d))

/-- **THE AT-MOST-ONE PAIR ROW EMITTER** (head one-hot): one machine run emits the whole row
`(i, j)` for `j = i+1..i+R` of the triangular family at time `t` — every counter restored, so the
rows chain at the sequencing layer. -/
theorem amoPairHead_family_run (t i R : ℕ) (out : List Bool) :
    run (loopProg3Machine amoPairHeadBody) (lp3Clock amoPairHeadBody R t i out.length)
      (init (loopProg3Machine amoPairHeadBody)
        (unaryD R ++ (unaryD t ++ (unaryD i ++ (jT R 0 ++ encodeD out)))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * R + 1,
          unaryD R ++ (unaryD t ++ (unaryD i ++ (unaryD R ++ encodeD (out
            ++ ((List.range R).map (fun d =>
                encodeClause' [(headVar t i, false),
                  (headVar t (i + 1 + d), false)])).flatten))))⟩ := by
  rw [loopProg3_run, amoPairHead_split]

theorem amoPairState_family_run (t i R : ℕ) (out : List Bool) :
    run (loopProg3Machine amoPairStateBody) (lp3Clock amoPairStateBody R t i out.length)
      (init (loopProg3Machine amoPairStateBody)
        (unaryD R ++ (unaryD t ++ (unaryD i ++ (jT R 0 ++ encodeD out)))))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false), 2 * R + 1,
          unaryD R ++ (unaryD t ++ (unaryD i ++ (unaryD R ++ encodeD (out
            ++ ((List.range R).map (fun d =>
                encodeClause' [(stateVar t i, false),
                  (stateVar t (i + 1 + d), false)])).flatten))))⟩ := by
  rw [loopProg3_run, amoPairState_split]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3