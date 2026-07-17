import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorph

/-!
# Cook–Levin M2 emitter — arming morph brick M2: THE SUBTRACT PASS

The first morph walk.  On the morph's input tape the machine alternately marks one pair
of region 2 (`unaryD (P+1)`, the cell bound) and visits one unit of region 3
(`xVis x m`, the cursored input), each round returning to the origin, until region 3's
terminal `01` is hit.  Exit: region 2 = `cntT (P+1) (n+1)` (its **unmarked remainder is
exactly `B`** — the quantity the later passes transcribe; `P+1−(n+1) = B` by
`P = n + B`), region 3 all-visited, everything else untouched.

Donor: `compareMachine` (CounterCompare) — the alternating two-counter marker — extended
by the passive region-1 crossing (states 0/1) and the 4-cell `xVis` unit walk
(states 6–9) in place of the flat `B`-counter phase.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph

/-! ## The subtract tape -/

/-- The subtract pass's tape: the passive grand region, the cell bound with `jA` pairs
marked, the input with `m` units visited, and an untouched suffix `E`
(right-associated for positional reasoning). -/
def subT (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) : List Bool :=
  List.replicate (8 * B + 16) true ++ ([false, true]
    ++ (markedD jA ++ (List.replicate (2 * (P + 1 - jA)) true ++ ([false, true]
    ++ (xVis x m ++ E)))))

/-- The unprocessed subtract tape is the morph input's region form. -/
theorem subT_zero (B P : ℕ) (x : List Bool) (E : List Bool) :
    subT B P 0 x 0 E
      = cntT (4 * B + 8) 0 ++ (cntT (P + 1) 0 ++ (xVis x 0 ++ E)) := by
  rw [subT, show 8 * B + 16 = 2 * (4 * B + 8) from by ring]
  simp [cntT, markedD, List.append_assoc]

/-- The subtract tape as the morph's input. -/
theorem subT_morphIn (B P : ℕ) (x s : List Bool) :
    subT B P 0 x 0 (unaryD (P + 1) ++ encodeD s) = morphIn B P x s := by
  rw [subT_zero, cntT_zero, cntT_zero, morphIn, cntT_zero]

theorem subT_length (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).length = 8 * B + 2 * P + 4 * x.length + 24 + E.length := by
  simp only [subT, List.length_append, List.length_replicate, markedD_length,
    List.length_cons, List.length_nil, xVis_length]
  omega

/-! ## The `getD` suite -/

theorem subT_getD_R1data (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (c : ℕ) (hc : c < 8 * B + 16) :
    (subT B P jA x m E).getD c false = true := by
  rw [subT, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem subT_getD_R1end_lo (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) :
    (subT B P jA x m E).getD (8 * B + 16) false = false := by
  rw [subT, show 8 * B + 16 = 8 * B + 16 + 0 from by omega,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem subT_getD_R1end_hi (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) :
    (subT B P jA x m E).getD (8 * B + 17) false = true := by
  rw [subT, show 8 * B + 17 = 8 * B + 16 + 1 from by omega,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- Reading region 2 and beyond: peel the passive region. -/
theorem subT_getD_R2 (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (c : ℕ) :
    (subT B P jA x m E).getD (8 * B + 18 + c) false
      = (markedD jA ++ (List.replicate (2 * (P + 1 - jA)) true ++ ([false, true]
          ++ (xVis x m ++ E)))).getD c false := by
  rw [subT, show 8 * B + 18 + c = 8 * B + 16 + (2 + c) from by omega,
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem subT_getD_R2mark_lo (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (i : ℕ) (h : i < jA) :
    (subT B P jA x m E).getD (8 * B + 18 + 2 * i) false = true := by
  rw [subT_getD_R2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jA i h

theorem subT_getD_R2mark_hi (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (i : ℕ) (h : i < jA) :
    (subT B P jA x m E).getD (8 * B + 18 + (2 * i + 1)) false = false := by
  rw [subT_getD_R2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jA i h

theorem subT_getD_R2data (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (c : ℕ) (hjA : jA ≤ P + 1) (h1 : 2 * jA ≤ c) (h2 : c < 2 * P + 2) :
    (subT B P jA x m E).getD (8 * B + 18 + c) false = true := by
  rw [subT_getD_R2, show c = 2 * jA + (c - 2 * jA) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem subT_getD_R2end_lo (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).getD (8 * B + 18 + (2 * P + 2)) false = false := by
  rw [subT_getD_R2, show 2 * P + 2 = 2 * jA + (2 * (P + 1 - jA) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem subT_getD_R2end_hi (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).getD (8 * B + 18 + (2 * P + 3)) false = true := by
  rw [subT_getD_R2, show 2 * P + 3 = 2 * jA + (2 * (P + 1 - jA) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- Reading region 3 and beyond: peel everything before the input. -/
theorem subT_getD_R3 (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (c : ℕ)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + c) false
      = (xVis x m ++ E).getD c false := by
  rw [subT, show 8 * B + 2 * P + 22 + c
      = 8 * B + 16 + (2 + (2 * jA + (2 * (P + 1 - jA) + (2 + c)))) from by omega,
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

/-! ## The write lemmas -/

/-- Marking region 2's next data pair. -/
theorem subT_markA (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA < P + 1) :
    writeAt (subT B P jA x m E) (8 * B + 18 + (2 * jA + 1)) false
      = subT B P (jA + 1) x m E := by
  rw [writeAt_of_lt false (by
      rw [subT_length B P jA x m E (by omega)]; omega), subT,
    show 8 * B + 18 + (2 * jA + 1) = 8 * B + 16 + (2 + (2 * jA + 1)) from by omega,
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (markedD_length jA),
    show List.replicate (2 * (P + 1 - jA)) true
      = true :: true :: List.replicate (2 * (P + 1 - jA - 1)) true from by
        rw [show 2 * (P + 1 - jA) = 2 * (P + 1 - jA - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [subT, ← markedD_snoc, show P + 1 - (jA + 1) = P + 1 - jA - 1 from by omega]
  simp [List.append_assoc]

/-- Visiting region 3's next unit. -/
theorem subT_markB (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) (hm : m < x.length) :
    writeAt (subT B P jA x m E) (8 * B + 2 * P + 22 + (4 * m + 3)) false
      = subT B P jA x (m + 1) E := by
  rw [writeAt_of_lt false (by
      rw [subT_length B P jA x m E hjA]; omega), subT,
    show 8 * B + 2 * P + 22 + (4 * m + 3)
      = 8 * B + 16 + (2 + (2 * jA + (2 * (P + 1 - jA) + (2 + (4 * m + 3))))) from by omega,
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (markedD_length jA),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  rw [subT, show (xVis x m ++ E).set (4 * m + 3) false
      = writeAt (xVis x m ++ E) (4 * m + 3) false from by
    rw [writeAt_of_lt false (by
      rw [List.length_append, xVis_length]; omega)]]
  rw [xVis_mark x m E hm]

/-! ## The subtract machine

Control: `State = Fin 12 × Bool` (stored low cell).  Phases: `0/1` cross the passive
grand region (skip `11`, boundary `01` ⇒ find), `2/3` find in region 2 (skip `10`, mark
`11` ⇒ seek, boundary ⇒ dead), `4/5` seek across region 2's data to its boundary, `6/7`
region 3 value pair (equal pair ⇒ cursor, terminal `01` ⇒ **done**), `8/9` region 3
cursor pair (`10` visited ⇒ next unit, `11` unvisited ⇒ visit and **reset** for the next
round), `10` = done halt, `11` = dead halt. -/

def subMachine : Machine where
  State := Fin 12 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 10) || decide (s.1 = 11)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((0, s.2), none, 1) else ((11, s.2), none, 2))
       else (if b then ((2, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then (if b then ((4, s.2), some false, 1) else ((2, s.2), none, 1))
       else ((11, s.2), none, 2))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then (if b then ((4, s.2), none, 1) else ((11, s.2), none, 2))
       else (if b then ((6, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if s.2 then (if b then ((8, s.2), none, 1) else ((11, s.2), none, 2))
       else (if b then ((10, s.2), none, 2) else ((8, s.2), none, 1)))
    else if s.1 = 8 then ((9, b), none, 1)
    else if s.1 = 9 then
      (if s.2 then (if b then ((0, s.2), some false, 3) else ((6, s.2), none, 1))
       else ((11, s.2), none, 2))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 10)

theorem init_sub (x : List Bool) : init subMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_s0 {s : Bool} {p : ℕ} {T : List Bool} :
    step subMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, subMachine, moveHead]; rfl

theorem step_s1_skip {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s1_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(1, false), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s2 {s : Bool} {p : ℕ} {T : List Bool} :
    step subMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, subMachine, moveHead]; rfl

theorem step_s3_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step subMachine ⟨(3, true), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s3_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(3, true), p, T⟩ = ⟨(4, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s4 {s : Bool} {p : ℕ} {T : List Bool} :
    step subMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
  simp only [step, subMachine, moveHead]; rfl

theorem step_s5_data {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(5, true), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s5_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(5, false), p, T⟩ = ⟨(6, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s6 {s : Bool} {p : ℕ} {T : List Bool} :
    step subMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
  simp only [step, subMachine, moveHead]; rfl

theorem step_s7_valT {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(7, true), p, T⟩ = ⟨(8, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s7_valF {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step subMachine ⟨(7, false), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s7_term {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(7, false), p, T⟩ = ⟨(10, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s8 {s : Bool} {p : ℕ} {T : List Bool} :
    step subMachine ⟨(8, s), p, T⟩ = ⟨(9, T.getD p false), p + 1, T⟩ := by
  simp only [step, subMachine, moveHead]; rfl

theorem step_s9_vis {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step subMachine ⟨(9, true), p, T⟩ = ⟨(6, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

theorem step_s9_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step subMachine ⟨(9, true), p, T⟩ = ⟨(0, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, subMachine, moveHead, h]

/-! ### Pair- and unit-step lemmas -/

/-- Skip a `11` pair of the passive grand region. -/
theorem run_two_skipR1 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s0, h1, step_s1_skip h2]

/-- Cross the grand region's `01` boundary into the find phase. -/
theorem run_two_crossR1 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s0, h1, step_s1_cross h2]

/-- Skip a `10` processed pair in the find phase. -/
theorem run_two_skipM {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run subMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s2, h1, step_s3_skip h2]

/-- Mark a `11` data pair in the find phase and enter the seek. -/
theorem run_two_markA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_s2, h1, step_s3_mark h2]

/-- Seek across a `11` data pair. -/
theorem run_two_seek {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s4, h1, step_s5_data h2]

/-- Cross region 2's `01` boundary into the input region. -/
theorem run_two_crossR2 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s4, h1, step_s5_cross h2]

/-- Skip a visited unit (`b b 1 0`) of the input region. -/
theorem run_four_skipU {s : Bool} {p : ℕ} {T : List Bool}
    (hv : T.getD (p + 1) false = T.getD p false)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = false) :
    run subMachine 4 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_s6]
  cases hb : T.getD p false with
  | true =>
    rw [hb] at hv
    rw [step_s7_valT hv, step_s8, h3, step_s9_vis h4]
  | false =>
    rw [hb] at hv
    rw [step_s7_valF hv, step_s8, h3, step_s9_vis h4]

/-- Visit the next unvisited unit (`b b 1 1 ↦ b b 1 0`) and reset for the next round. -/
theorem run_four_visitU {s : Bool} {p : ℕ} {T : List Bool}
    (hv : T.getD (p + 1) false = T.getD p false)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run subMachine 4 ⟨(6, s), p, T⟩ = ⟨(0, true), 0, writeAt T (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_s6]
  cases hb : T.getD p false with
  | true =>
    rw [hb] at hv
    rw [step_s7_valT hv, step_s8, h3, step_s9_mark h4]
  | false =>
    rw [hb] at hv
    rw [step_s7_valF hv, step_s8, h3, step_s9_mark h4]

/-- Hit the input region's terminal `01`: **done**. -/
theorem run_two_term {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run subMachine 2 ⟨(6, s), p, T⟩ = ⟨(10, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s6, h1, step_s7_term h2]

/-! ### Scan run-invariants -/

/-- Skip `k` grand pairs. -/
theorem run_skipR1 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run subMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipR1 hk.1 hk.2]
    rfl

/-- Skip `k` processed pairs in the find phase. -/
theorem run_skipM (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run subMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipM hk.1 hk.2]
    rfl

/-- Seek across `k` data pairs. -/
theorem run_seekK (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run subMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seek hk.1 hk.2]
    rfl

/-- Skip `k` visited units of the input region. -/
theorem run_skipU (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 4 * i + 1) false = T.getD (q + 4 * i) false
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = false) :
    run subMachine (4 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_four_skipU hk.1 hk.2.1 hk.2.2]
    rfl

/-! ### Region-3 reads at walk positions -/

theorem subT_getD_unit_lo (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (i : ℕ)
    (hjA : jA ≤ P + 1) (hi : i < x.length) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * i) false = x.getD i false :=
  (subT_getD_R3 B P jA x m E (4 * i) hjA).trans (xVisE_val_lo x m i E hi)

theorem subT_getD_unit_hi (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (i : ℕ)
    (hjA : jA ≤ P + 1) (hi : i < x.length) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * i + 1) false = x.getD i false := by
  have h := (subT_getD_R3 B P jA x m E (4 * i + 1) hjA).trans (xVisE_val_hi x m i E hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 1) = 8 * B + 2 * P + 22 + 4 * i + 1
    from by omega] at h

theorem subT_getD_unit_cur (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (i : ℕ)
    (hjA : jA ≤ P + 1) (hi : i < x.length) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * i + 2) false = true := by
  have h := (subT_getD_R3 B P jA x m E (4 * i + 2) hjA).trans (xVisE_cur_lo x m i E hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 2) = 8 * B + 2 * P + 22 + 4 * i + 2
    from by omega] at h

theorem subT_getD_unit_vis (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (i : ℕ)
    (hjA : jA ≤ P + 1) (hv : i < m) (hi : i < x.length) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * i + 3) false = false := by
  have h := (subT_getD_R3 B P jA x m E (4 * i + 3) hjA).trans
    (xVisE_cur_hi_vis x m i E hv hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 3) = 8 * B + 2 * P + 22 + 4 * i + 3
    from by omega] at h

theorem subT_getD_unit_unvis (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool) (i : ℕ)
    (hjA : jA ≤ P + 1) (hv : m ≤ i) (hi : i < x.length) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * i + 3) false = true := by
  have h := (subT_getD_R3 B P jA x m E (4 * i + 3) hjA).trans
    (xVisE_cur_hi_unvis x m i E hv hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 3) = 8 * B + 2 * P + 22 + 4 * i + 3
    from by omega] at h

theorem subT_getD_term_lo (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * x.length) false = false :=
  (subT_getD_R3 B P jA x m E (4 * x.length) hjA).trans (xVisE_term_lo x m E)

theorem subT_getD_term_hi (B P jA : ℕ) (x : List Bool) (m : ℕ) (E : List Bool)
    (hjA : jA ≤ P + 1) :
    (subT B P jA x m E).getD (8 * B + 2 * P + 22 + 4 * x.length + 1) false = true := by
  have h := (subT_getD_R3 B P jA x m E (4 * x.length + 1) hjA).trans
    (xVisE_term_hi x m E)
  rwa [show 8 * B + 2 * P + 22 + (4 * x.length + 1)
    = 8 * B + 2 * P + 22 + 4 * x.length + 1 from by omega] at h

/-! ## The round invariant -/

/-- **One full round.**  From the origin on `subT B P m x m E`, `8B + 2P + 4m + 26`
steps mark region 2's pair `m`, visit region 3's unit `m`, and return to the origin. -/
theorem sub_round (B P : ℕ) (x : List Bool) (E : List Bool) (m : ℕ) (s : Bool)
    (hm : m < x.length) (hmP : m < P + 1) :
    run subMachine (8 * B + 2 * P + 4 * m + 26) ⟨(0, s), 0, subT B P m x m E⟩
      = ⟨(0, true), 0, subT B P (m + 1) x (m + 1) E⟩ := by
  -- Stage 1: cross the grand region's pairs.
  have st1 := run_skipR1 (subT B P m x m E) 0 (4 * B + 8) s (fun i hi =>
    ⟨by simpa using subT_getD_R1data B P m x m E (2 * i) (by omega),
     by simpa using subT_getD_R1data B P m x m E (2 * i + 1) (by omega)⟩)
  simp only [Nat.zero_add] at st1
  rw [if_neg (by omega), show 2 * (4 * B + 8) = 8 * B + 16 from by ring] at st1
  -- Stage 2: cross the grand boundary.
  have h2hi := subT_getD_R1end_hi B P m x m E
  rw [show 8 * B + 17 = 8 * B + 16 + 1 from by omega] at h2hi
  have st2 := run_two_crossR1 (s := true) (p := 8 * B + 16) (T := subT B P m x m E)
    (subT_getD_R1end_lo B P m x m E) h2hi
  rw [show 8 * B + 16 + 2 = 8 * B + 18 from by omega] at st2
  -- Stage 3: skip the `m` processed pairs of region 2.
  have st3 := run_skipM (subT B P m x m E) (8 * B + 18) m false (fun i hi =>
    ⟨subT_getD_R2mark_lo B P m x m E i hi, by
      have h := subT_getD_R2mark_hi B P m x m E i hi
      rwa [show 8 * B + 18 + (2 * i + 1) = 8 * B + 18 + 2 * i + 1 from by omega] at h⟩)
  -- Stage 4: mark region 2's pair `m`.
  have h4hi : (subT B P m x m E).getD (8 * B + 18 + 2 * m + 1) false = true := by
    have h := subT_getD_R2data B P m x m E (2 * m + 1) (by omega) (by omega) (by omega)
    rwa [show 8 * B + 18 + (2 * m + 1) = 8 * B + 18 + 2 * m + 1 from by omega] at h
  have st4 := run_two_markA (s := if m = 0 then false else true) (p := 8 * B + 18 + 2 * m)
    (T := subT B P m x m E)
    (subT_getD_R2data B P m x m E (2 * m) (by omega) (by omega) (by omega)) h4hi
  rw [show 8 * B + 18 + 2 * m + 1 = 8 * B + 18 + (2 * m + 1) from by omega,
    subT_markA B P m x m E hmP] at st4
  -- Stage 5: seek across region 2's remaining data.
  have st5 := run_seekK (subT B P (m + 1) x m E) (8 * B + 18 + 2 * m + 2) (P - m) true
    (fun i hi => ⟨by
      have h := subT_getD_R2data B P (m + 1) x m E (2 * m + 2 + 2 * i) (by omega)
        (by omega) (by omega)
      rwa [show 8 * B + 18 + (2 * m + 2 + 2 * i) = 8 * B + 18 + 2 * m + 2 + 2 * i
        from by omega] at h, by
      have h := subT_getD_R2data B P (m + 1) x m E (2 * m + 2 + 2 * i + 1) (by omega)
        (by omega) (by omega)
      rwa [show 8 * B + 18 + (2 * m + 2 + 2 * i + 1) = 8 * B + 18 + 2 * m + 2 + 2 * i + 1
        from by omega] at h⟩)
  rw [show 8 * B + 18 + 2 * m + 2 + 2 * (P - m) = 8 * B + 2 * P + 20 from by omega] at st5
  simp only [ite_self] at st5
  -- Stage 6: cross region 2's boundary.
  have h6lo := subT_getD_R2end_lo B P (m + 1) x m E (by omega)
  rw [show 8 * B + 18 + (2 * P + 2) = 8 * B + 2 * P + 20 from by omega] at h6lo
  have h6hi := subT_getD_R2end_hi B P (m + 1) x m E (by omega)
  rw [show 8 * B + 18 + (2 * P + 3) = 8 * B + 2 * P + 20 + 1 from by omega] at h6hi
  have st6 := run_two_crossR2 (s := true) (p := 8 * B + 2 * P + 20)
    (T := subT B P (m + 1) x m E) h6lo h6hi
  rw [show 8 * B + 2 * P + 20 + 2 = 8 * B + 2 * P + 22 from by omega] at st6
  -- Stage 7: skip the `m` visited units.
  have st7 := run_skipU (subT B P (m + 1) x m E) (8 * B + 2 * P + 22) m false
    (fun i hi => ⟨
      (subT_getD_unit_hi B P (m + 1) x m E i (by omega) (by omega)).trans
        (subT_getD_unit_lo B P (m + 1) x m E i (by omega) (by omega)).symm,
      subT_getD_unit_cur B P (m + 1) x m E i (by omega) (by omega),
      subT_getD_unit_vis B P (m + 1) x m E i (by omega) hi (by omega)⟩)
  -- Stage 8: visit unit `m` and reset.
  have st8 := run_four_visitU (s := if m = 0 then false else true)
    (p := 8 * B + 2 * P + 22 + 4 * m) (T := subT B P (m + 1) x m E)
    ((subT_getD_unit_hi B P (m + 1) x m E m (by omega) hm).trans
      (subT_getD_unit_lo B P (m + 1) x m E m (by omega) hm).symm)
    (subT_getD_unit_cur B P (m + 1) x m E m (by omega) hm)
    (subT_getD_unit_unvis B P (m + 1) x m E m (by omega) (le_refl m) hm)
  rw [show 8 * B + 2 * P + 22 + 4 * m + 3 = 8 * B + 2 * P + 22 + (4 * m + 3)
      from by omega,
    subT_markB B P (m + 1) x m E (by omega) hm] at st8
  -- Assemble the round.
  rw [show 8 * B + 2 * P + 4 * m + 26
      = 8 * B + 16 + (2 + (2 * m + (2 + (2 * (P - m) + (2 + (4 * m + 4))))))
      from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    show 4 * m + 4 = 4 * m + 4 from rfl, run_add, st7, st8]

/-! ## The rounds and the endgame -/

/-- The cumulative clock of the first `k` rounds. -/
def subRounds (B P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => subRounds B P k + (8 * B + 2 * P + 4 * k + 26)

/-- **Rounds invariant.** -/
theorem sub_rounds (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k ≤ x.length) (hkP : k ≤ P + 1) (s : Bool) :
    run subMachine (subRounds B P k) ⟨(0, s), 0, subT B P 0 x 0 E⟩
      = ⟨(0, if k = 0 then s else true), 0, subT B P k x k E⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show subRounds B P (k + 1) = subRounds B P k + (8 * B + 2 * P + 4 * k + 26)
        from rfl,
      run_add, ih (by omega) (by omega), sub_round B P x E k _ (by omega) (by omega),
      if_neg (by omega)]

/-- The subtract pass's exact clock. -/
def subClock (B P n : ℕ) : ℕ := subRounds B P n + (8 * B + 2 * P + 4 * n + 24)

/-- **THE SUBTRACT PASS RUNS.**  From the origin on the unprocessed tape, the machine
marks region 2 once per input unit plus once more (the failed find of the last sweep),
visits every input unit, and halts DONE at region 3's terminal: region 2's **unmarked
remainder is exactly `P - x.length`** (`= B` at the morph parameters). -/
theorem subMachine_run (B P : ℕ) (x : List Bool) (E : List Bool) (hn : x.length ≤ P) :
    run subMachine (subClock B P x.length) (init subMachine (subT B P 0 x 0 E))
      = ⟨(10, false), 8 * B + 2 * P + 22 + 4 * x.length + 1,
          subT B P (x.length + 1) x x.length E⟩ := by
  rw [init_sub, subClock, run_add,
    sub_rounds B P x E x.length (le_refl _) (by omega) false]
  -- Stage 1: cross the grand region.
  have st1 := run_skipR1 (subT B P x.length x x.length E) 0 (4 * B + 8)
    (if x.length = 0 then false else true) (fun i hi =>
    ⟨by simpa using subT_getD_R1data B P x.length x x.length E (2 * i) (by omega),
     by simpa using subT_getD_R1data B P x.length x x.length E (2 * i + 1) (by omega)⟩)
  simp only [Nat.zero_add] at st1
  rw [if_neg (show ¬(4 * B + 8 = 0) from by omega),
    show 2 * (4 * B + 8) = 8 * B + 16 from by ring] at st1
  -- Stage 2: cross the grand boundary.
  have h2hi := subT_getD_R1end_hi B P x.length x x.length E
  rw [show 8 * B + 17 = 8 * B + 16 + 1 from by omega] at h2hi
  have st2 := run_two_crossR1 (s := true) (p := 8 * B + 16)
    (T := subT B P x.length x x.length E)
    (subT_getD_R1end_lo B P x.length x x.length E) h2hi
  rw [show 8 * B + 16 + 2 = 8 * B + 18 from by omega] at st2
  -- Stage 3: skip the processed pairs.
  have st3 := run_skipM (subT B P x.length x x.length E) (8 * B + 18) x.length false
    (fun i hi =>
    ⟨subT_getD_R2mark_lo B P x.length x x.length E i hi, by
      have h := subT_getD_R2mark_hi B P x.length x x.length E i hi
      rwa [show 8 * B + 18 + (2 * i + 1) = 8 * B + 18 + 2 * i + 1 from by omega] at h⟩)
  -- Stage 4: mark region 2's pair `x.length`.
  have h4hi : (subT B P x.length x x.length E).getD
      (8 * B + 18 + 2 * x.length + 1) false = true := by
    have h := subT_getD_R2data B P x.length x x.length E (2 * x.length + 1) (by omega)
      (by omega) (by omega)
    rwa [show 8 * B + 18 + (2 * x.length + 1) = 8 * B + 18 + 2 * x.length + 1
      from by omega] at h
  have st4 := run_two_markA (s := if x.length = 0 then false else true)
    (p := 8 * B + 18 + 2 * x.length) (T := subT B P x.length x x.length E)
    (subT_getD_R2data B P x.length x x.length E (2 * x.length) (by omega) (by omega)
      (by omega)) h4hi
  rw [show 8 * B + 18 + 2 * x.length + 1 = 8 * B + 18 + (2 * x.length + 1) from by omega,
    subT_markA B P x.length x x.length E (by omega)] at st4
  -- Stage 5: seek across the remaining data.
  have st5 := run_seekK (subT B P (x.length + 1) x x.length E)
    (8 * B + 18 + 2 * x.length + 2) (P - x.length) true
    (fun i hi => ⟨by
      have h := subT_getD_R2data B P (x.length + 1) x x.length E
        (2 * x.length + 2 + 2 * i) (by omega) (by omega) (by omega)
      rwa [show 8 * B + 18 + (2 * x.length + 2 + 2 * i)
        = 8 * B + 18 + 2 * x.length + 2 + 2 * i from by omega] at h, by
      have h := subT_getD_R2data B P (x.length + 1) x x.length E
        (2 * x.length + 2 + 2 * i + 1) (by omega) (by omega) (by omega)
      rwa [show 8 * B + 18 + (2 * x.length + 2 + 2 * i + 1)
        = 8 * B + 18 + 2 * x.length + 2 + 2 * i + 1 from by omega] at h⟩)
  rw [show 8 * B + 18 + 2 * x.length + 2 + 2 * (P - x.length) = 8 * B + 2 * P + 20
    from by omega] at st5
  simp only [ite_self] at st5
  -- Stage 6: cross region 2's boundary.
  have h6lo := subT_getD_R2end_lo B P (x.length + 1) x x.length E (by omega)
  rw [show 8 * B + 18 + (2 * P + 2) = 8 * B + 2 * P + 20 from by omega] at h6lo
  have h6hi := subT_getD_R2end_hi B P (x.length + 1) x x.length E (by omega)
  rw [show 8 * B + 18 + (2 * P + 3) = 8 * B + 2 * P + 20 + 1 from by omega] at h6hi
  have st6 := run_two_crossR2 (s := true) (p := 8 * B + 2 * P + 20)
    (T := subT B P (x.length + 1) x x.length E) h6lo h6hi
  rw [show 8 * B + 2 * P + 20 + 2 = 8 * B + 2 * P + 22 from by omega] at st6
  -- Stage 7: skip all visited units.
  have st7 := run_skipU (subT B P (x.length + 1) x x.length E) (8 * B + 2 * P + 22)
    x.length false (fun i hi => ⟨
      (subT_getD_unit_hi B P (x.length + 1) x x.length E i (by omega) hi).trans
        (subT_getD_unit_lo B P (x.length + 1) x x.length E i (by omega) hi).symm,
      subT_getD_unit_cur B P (x.length + 1) x x.length E i (by omega) hi,
      subT_getD_unit_vis B P (x.length + 1) x x.length E i (by omega) hi hi⟩)
  -- Stage 8: hit the terminal.
  have st8 := run_two_term (s := if x.length = 0 then false else true)
    (p := 8 * B + 2 * P + 22 + 4 * x.length)
    (T := subT B P (x.length + 1) x x.length E)
    (subT_getD_term_lo B P (x.length + 1) x x.length E (by omega))
    (subT_getD_term_hi B P (x.length + 1) x x.length E (by omega))
  -- Assemble the endgame.
  rw [show 8 * B + 2 * P + 4 * x.length + 24
      = 8 * B + 16
        + (2 + (2 * x.length + (2 + (2 * (P - x.length) + (2 + (4 * x.length + 2))))))
      from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, st8]

/-- The done state halts. -/
theorem subMachine_halt10 : subMachine.halt ((10 : Fin 12), false) = true := rfl

/-- **The subtract pass at the morph's input**: region 2's unmarked remainder is `B`. -/
theorem subMachine_run_morphIn (B P : ℕ) (x s : List Bool) (hn : x.length ≤ P) :
    run subMachine (subClock B P x.length) (init subMachine (morphIn B P x s))
      = ⟨(10, false), 8 * B + 2 * P + 22 + 4 * x.length + 1,
          subT B P (x.length + 1) x x.length (unaryD (P + 1) ++ encodeD s)⟩ := by
  rw [← subT_morphIn]
  exact subMachine_run B P x (unaryD (P + 1) ++ encodeD s) hn

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub
