import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT1

/-!
# Cook–Levin M2 emitter — arming morph brick M4: THE UNIFORMIZER SWEEP

One linear sweep that heals the whole dead field `[2B+2, 8B+2P+20)` — brick M3's junk,
the old region-1 boundary, and the spent region 2 — to all-true.  After it the tape is
`unaryD B ++ 1^{6B+2P+18} ++ 01 ++ xVis ++ E`: a uniform true-field between `T1`'s
marker and region 2's old boundary, so the next target (`T2 = unaryD P`) is an exact
replay of brick M3's discipline (all-true field, count against a source, ONE marker
write) — no mixed-content frontier tracking anywhere downstream.

The sweep: cross `T1` (content-blind), skip the junk (already true, no writes), erase
the old `01` (one write at its low cell), heal region 2's `10 ↦ 11` pair by pair, and
halt at the SECOND surviving `0`-low — region 2's old boundary, kept as the field's
delimiter.  No rounds, no counting: `8B + 2P + 21` steps flat.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1

/-! ## The sweep's tape descriptors -/

/-- Mid-heal: the old boundary erased, `i` of region 2's marks healed. -/
def fillH (B P i : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (6 * B + 16 + 2 * i) true
    ++ (markedD (P + 1 - i) ++ ([false, true]
    ++ (xVis x x.length ++ E))))

/-- The sweep's exit: one uniform true-field behind region 2's old boundary. -/
def fillOut (B P : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (6 * B + 2 * P + 18) true ++ ([false, true]
    ++ (xVis x x.length ++ E)))

/-- Fully healed is the exit. -/
theorem fillH_out (B P : ℕ) (x : List Bool) (E : List Bool) :
    fillH B P (P + 1) x E = fillOut B P x E := by
  rw [fillH, fillOut, Nat.sub_self,
    show 6 * B + 16 + 2 * (P + 1) = 6 * B + 2 * P + 18 from by omega]
  rfl

/-! ## The `getD` suite on the entry tape -/

theorem t1Out_getD_T1lo (B P : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hi : i < B) :
    (t1Out B P x E).getD (2 * i) false = true := by
  rw [t1Out, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t1Out_getD_T1mark (B P : ℕ) (x : List Bool) (E : List Bool) :
    (t1Out B P x E).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (List.replicate (6 * B + 14) true ++ ([false, true]
      ++ (markedD (P + 1) ++ ([false, true] ++ (xVis x x.length ++ E))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t1Out, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading past `T1`. -/
theorem t1Out_getD_rest (B P : ℕ) (x : List Bool) (E : List Bool) (c : ℕ) :
    (t1Out B P x E).getD (2 * B + 2 + c) false
      = (List.replicate (6 * B + 14) true ++ ([false, true]
          ++ (markedD (P + 1) ++ ([false, true]
          ++ (xVis x x.length ++ E))))).getD c false := by
  rw [t1Out, show 2 * B + 2 + c = 2 * B + 2 + c from rfl,
    getD_append_left_length' _ _ (unaryD_length B)]

theorem t1Out_getD_junk_lo (B P : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hi : i < 3 * B + 7) :
    (t1Out B P x E).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t1Out_getD_rest, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t1Out_getD_junk_hi (B P : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hi : i < 3 * B + 7) :
    (t1Out B P x E).getD (2 * B + 2 + 2 * i + 1) false = true := by
  have h := t1Out_getD_rest B P x E (2 * i + 1)
  rw [show 2 * B + 2 + (2 * i + 1) = 2 * B + 2 + 2 * i + 1 from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t1Out_getD_oldFT_lo (B P : ℕ) (x : List Bool) (E : List Bool) :
    (t1Out B P x E).getD (8 * B + 16) false = false := by
  have h := t1Out_getD_rest B P x E (6 * B + 14)
  rw [show 2 * B + 2 + (6 * B + 14) = 8 * B + 16 from by omega] at h
  rw [h, show (6 * B + 14 : ℕ) = 6 * B + 14 + 0 from by omega,
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ## The write lemmas -/

/-- Erasing the old boundary's `0` merges the junk into one true-field. -/
theorem t1Out_erase (B P : ℕ) (x : List Bool) (E : List Bool) :
    writeAt (t1Out B P x E) (8 * B + 16) true = fillH B P 0 x E := by
  rw [writeAt_of_lt true (by
      simp only [t1Out, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t1Out,
    show 8 * B + 16 = 2 * B + 2 + (6 * B + 14 + 0) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate]
  rw [fillH, Nat.sub_zero, show 6 * B + 16 + 2 * 0 = 6 * B + 14 + 1 + 1 from by omega,
    List.replicate_succ' (n := 6 * B + 14 + 1), List.replicate_succ' (n := 6 * B + 14)]
  simp [List.append_assoc]

/-- Healing one of region 2's marks. -/
theorem fillH_heal (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P + 1) :
    writeAt (fillH B P i x E) (8 * B + 18 + 2 * i + 1) true = fillH B P (i + 1) x E := by
  rw [writeAt_of_lt true (by
      simp only [fillH, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), fillH,
    show 8 * B + 18 + 2 * i + 1 = 2 * B + 2 + (6 * B + 16 + 2 * i + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [fillH, show P + 1 - (i + 1) = P + 1 - i - 1 from by omega,
    show 6 * B + 16 + 2 * (i + 1) = 6 * B + 16 + 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 6 * B + 16 + 2 * i + 1),
    List.replicate_succ' (n := 6 * B + 16 + 2 * i)]
  simp

/-! ### Heal-walk reads -/

theorem fillH_getD_lo (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P + 1) :
    (fillH B P i x E).getD (8 * B + 18 + 2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (6 * B + 16 + 2 * i) true)
    (markedD (P + 1 - i) ++ ([false, true] ++ (xVis x x.length ++ E)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [fillH, show 8 * B + 18 + 2 * i = 2 * B + 2 + (6 * B + 16 + 2 * i) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem fillH_getD_hi (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P + 1) :
    (fillH B P i x E).getD (8 * B + 18 + 2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (6 * B + 16 + 2 * i) true)
    (markedD (P + 1 - i) ++ ([false, true] ++ (xVis x x.length ++ E)))
    List.length_replicate 1 false
  rw [fillH, show 8 * B + 18 + 2 * i + 1
      = 2 * B + 2 + (6 * B + 16 + 2 * i + 1) from by omega,
    getD_append_left_length' _ _ (unaryD_length B),
    show (6 * B + 16 + 2 * i + 1 : ℕ) = 6 * B + 16 + 2 * i + 1 from rfl, h,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem fillH_getD_done (B P : ℕ) (x : List Bool) (E : List Bool) :
    (fillH B P (P + 1) x E).getD (8 * B + 2 * P + 20) false = false := by
  have h := getD_append_left_length' (List.replicate (6 * B + 16 + 2 * (P + 1)) true)
    (markedD (P + 1 - (P + 1)) ++ ([false, true] ++ (xVis x x.length ++ E)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [fillH, show 8 * B + 2 * P + 20
      = 2 * B + 2 + (6 * B + 16 + 2 * (P + 1)) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h, Nat.sub_self]
  rfl

/-! ## The uniformizer machine

Control: `State = Fin 10 × Bool`.  Phases: `0/1` cross `T1` (low `1` skip; low `0` =
`T1`'s marker ⇒ cross via `2`), `3/4` first sweep (skip `11` junk; low `0` = the old
boundary ⇒ ERASE its low and pass via `5`), `6/7` second sweep (skip is dead here — heal
`10 ↦ 11`; low `0` = region 2's old boundary ⇒ **done**), `8` done, `9` dead. -/

def fillMachine : Machine where
  State := Fin 10 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 8) || decide (s.1 = 9)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, b), none, 1) else ((2, b), none, 1))
    else if s.1 = 1 then ((0, s.2), none, 1)
    else if s.1 = 2 then ((3, s.2), none, 1)
    else if s.1 = 3 then (if b then ((4, b), none, 1) else ((5, b), some true, 1))
    else if s.1 = 4 then
      (if b then ((3, s.2), none, 1) else ((3, s.2), some true, 1))
    else if s.1 = 5 then ((6, s.2), none, 1)
    else if s.1 = 6 then (if b then ((7, b), none, 1) else ((8, b), none, 2))
    else if s.1 = 7 then
      (if b then ((6, s.2), none, 1) else ((6, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 8)

theorem init_fill (x : List Bool) : init fillMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_f0_T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step fillMachine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f0_F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step fillMachine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f1 {s : Bool} {p : ℕ} {T : List Bool} :
    step fillMachine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, fillMachine, moveHead]; rfl

theorem step_f2 {s : Bool} {p : ℕ} {T : List Bool} :
    step fillMachine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, fillMachine, moveHead]; rfl

theorem step_f3_T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step fillMachine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f3_erase {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step fillMachine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f4_T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step fillMachine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f5 {s : Bool} {p : ℕ} {T : List Bool} :
    step fillMachine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, fillMachine, moveHead]; rfl

theorem step_f6_T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step fillMachine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f6_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step fillMachine ⟨(6, s), p, T⟩ = ⟨(8, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

theorem step_f7_heal {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step fillMachine ⟨(7, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, fillMachine, moveHead, h]

/-! ### Composites and walks -/

theorem fillrun_two_skipT1 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) :
    run fillMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_f0_T h1, step_f1]

theorem fillrun_two_crossT1 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) :
    run fillMachine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_f0_F h1, step_f2]

theorem fillrun_two_junk {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run fillMachine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_f3_T h1, step_f4_T h2]

theorem fillrun_two_erase {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) :
    run fillMachine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, writeAt T p true⟩ := by
  rw [run_succ, run_succ, run_zero, step_f3_erase h1, step_f5]

theorem fillrun_two_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run fillMachine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_f6_T h1, step_f7_heal h2]

theorem fillrun_one_done {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    run fillMachine 1 ⟨(6, s), p, T⟩ = ⟨(8, false), p, T⟩ := by
  rw [run_succ, run_zero, step_f6_done h]

theorem fillrun_skipT1K (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run fillMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), fillrun_two_skipT1 (h k (by omega))]
    rfl

theorem fillrun_junkK (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = true) :
    run fillMachine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), fillrun_two_junk hk.1 hk.2]
    rfl

/-- The heal sweep, tape evolving. -/
theorem fillrun_heal (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P + 1 →
    run fillMachine (2 * k) ⟨(6, s), 8 * B + 18 + 2 * i, fillH B P i x E⟩
      = ⟨(6, if k = 0 then s else true), 8 * B + 18 + 2 * (i + k),
          fillH B P (i + k) x E⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      fillrun_two_heal (fillH_getD_lo B P i x E (by omega))
        (fillH_getD_hi B P i x E (by omega)),
      fillH_heal B P i x E (by omega),
      show 8 * B + 18 + 2 * i + 2 = 8 * B + 18 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The sweep's clock and run -/

/-- The uniformizer's exact clock: one linear sweep. -/
def fillClock (B P : ℕ) : ℕ := 8 * B + 2 * P + 21

/-- **THE UNIFORMIZER RUNS**: from brick M3's exit, one sweep heals the whole dead field
to true, leaving `unaryD B ++ 1^{6B+2P+18} ++ 01 ++ xVis ++ E`. -/
theorem fillMachine_run (B P : ℕ) (x : List Bool) (E : List Bool) :
    run fillMachine (fillClock B P) (init fillMachine (t1Out B P x E))
      = ⟨(8, false), 8 * B + 2 * P + 20, fillOut B P x E⟩ := by
  rw [init_fill]
  -- Stage 1: cross T1's pairs.
  have st1 := fillrun_skipT1K (t1Out B P x E) 0 B false (fun i hi => by
    simpa using t1Out_getD_T1lo B P x E i hi)
  simp only [Nat.zero_add] at st1
  -- Stage 2: cross T1's marker.
  have st2 := fillrun_two_crossT1 (s := if B = 0 then false else true) (p := 2 * B)
    (T := t1Out B P x E) (t1Out_getD_T1mark B P x E)
  rw [show 2 * B + 2 = 2 * B + 2 from rfl] at st2
  -- Stage 3: skip the junk.
  have st3 := fillrun_junkK (t1Out B P x E) (2 * B + 2) (3 * B + 7) false
    (fun i hi => ⟨t1Out_getD_junk_lo B P x E i hi, t1Out_getD_junk_hi B P x E i hi⟩)
  rw [show 2 * B + 2 + 2 * (3 * B + 7) = 8 * B + 16 from by omega] at st3
  -- Stage 4: erase the old boundary.
  have st4 := fillrun_two_erase (s := if 3 * B + 7 = 0 then false else true)
    (p := 8 * B + 16) (T := t1Out B P x E) (t1Out_getD_oldFT_lo B P x E)
  rw [t1Out_erase B P x E, show 8 * B + 16 + 2 = 8 * B + 18 from by omega] at st4
  -- Stage 5: heal region 2's marks.
  have st5 := fillrun_heal B P x E (P + 1) 0 false (by omega)
  rw [show 8 * B + 18 + 2 * 0 = 8 * B + 18 from by omega,
    show (0 + (P + 1) : ℕ) = P + 1 from by omega,
    show 8 * B + 18 + 2 * (P + 1) = 8 * B + 2 * P + 20 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at st5
  -- Stage 6: region 2's old boundary: DONE.
  have st6 := fillrun_one_done (s := true) (p := 8 * B + 2 * P + 20)
    (T := fillH B P (P + 1) x E) (fillH_getD_done B P x E)
  -- Assemble.
  rw [show fillClock B P = 2 * B + (2 + (2 * (3 * B + 7) + (2 + (2 * (P + 1) + 1))))
      from by rw [fillClock]; omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, st6,
    fillH_out B P x E]

/-- The done state halts. -/
theorem fillMachine_halt8 : fillMachine.halt ((8 : Fin 10), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill
