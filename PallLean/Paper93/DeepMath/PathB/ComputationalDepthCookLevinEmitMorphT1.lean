import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphSub

/-!
# Cook–Levin M2 emitter — arming morph brick M3: THE FIRST TRANSCRIPTION WRITE (`T1`)

Writes the six-region target's first region, `unaryD B`, over the morph prefix's front.
The front of region 1's pair-field is all-true, so the T-span needs no writes: the pass
1:1-transcribes region 2's unmarked remainder (= `B`, brick M2's exit) into fresh front
marks — the `cntT` source discipline applied to region 1 itself — then places the `01`
marker at position `2B` (one write) and heals the front marks in a single sweep.  Exit
prefix: `unaryD B` verbatim; region 2 fully marked (spent); everything right untouched.

Round `j`: cross region 1's pair-field content-blind (marked and unmarked pairs both
have a true low cell), consume remainder pair `j` (mark), reset, mark front pair `j`,
reset.  Endgame: the find hits region 2's boundary (remainder spent after `B` rounds),
resets, seeks the first unmarked front pair (position `2B`), steps left, writes the
marker's `0`, resets, and heals: `10 ↦ 11` left-to-right until the written `0`: DONE.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub

/-! ## The pass's tape descriptors -/

/-- Mid-round: `jF` front pairs and `jR` region-2 pairs marked. -/
def t1T (B P jF jR : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  markedD jF ++ (List.replicate (2 * (4 * B + 8 - jF)) true ++ ([false, true]
    ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true ++ ([false, true]
    ++ (xVis x x.length ++ E))))))

/-- The unprocessed pass tape is brick M2's exit. -/
theorem t1T_zero (B P : ℕ) (x : List Bool) (E : List Bool) :
    t1T B P 0 (x.length + 1) x E = subT B P (x.length + 1) x x.length E := by
  rw [t1T, subT, xVis_saturate x x.length (le_refl _),
    show 2 * (4 * B + 8 - 0) = 8 * B + 16 from by omega]
  rfl

/-- Post-marker, `i` front pairs healed. -/
def t1H (B P i : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  List.replicate (2 * i) true ++ (markedD (B - i) ++ (false
    :: (List.replicate (6 * B + 15) true ++ ([false, true]
    ++ (markedD (P + 1) ++ ([false, true]
    ++ (xVis x x.length ++ E)))))))

/-- The pass's exit: the six-region target's first region, done. -/
def t1Out (B P : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (6 * B + 14) true ++ ([false, true]
    ++ (markedD (P + 1) ++ ([false, true]
    ++ (xVis x x.length ++ E)))))

/-- The fully-healed tape is the exit. -/
theorem t1H_out (B P : ℕ) (x : List Bool) (E : List Bool) :
    t1H B P B x E = t1Out B P x E := by
  rw [t1H, t1Out, Nat.sub_self, unaryD_eq,
    show (6 * B + 15 : ℕ) = 6 * B + 14 + 1 from by omega, List.replicate_succ]
  simp [markedD, List.append_assoc]

/-! ## The `getD` suite -/

/-- Region 1's pair-field low cells are true, marked or not. -/
theorem t1T_getD_R1lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 4 * B + 8) (hi : i < 4 * B + 8) :
    (t1T B P jF jR x E).getD (2 * i) false = true := by
  rcases lt_or_ge i jF with h | h
  · rw [t1T, List.getD_append (h := by rw [markedD_length]; omega)]
    exact markedD_getD_lo jF i h
  · rw [t1T, show 2 * i = 2 * jF + (2 * i - 2 * jF) from by omega,
      getD_append_left_length' _ _ (markedD_length jF),
      List.getD_append (h := by rw [List.length_replicate]; omega)]
    exact List.getD_replicate _ (h := by omega)

/-- A marked front pair's high cell. -/
theorem t1T_getD_R1mark_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (h : i < jF) :
    (t1T B P jF jR x E).getD (2 * i + 1) false = false := by
  rw [t1T, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jF i h

/-- An unmarked front pair's high cell. -/
theorem t1T_getD_R1data_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ i) (hi : i < 4 * B + 8) :
    (t1T B P jF jR x E).getD (2 * i + 1) false = true := by
  rw [t1T, show 2 * i + 1 = 2 * jF + (2 * i + 1 - 2 * jF) from by omega,
    getD_append_left_length' _ _ (markedD_length jF),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t1T_getD_R1end_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 4 * B + 8) :
    (t1T B P jF jR x E).getD (8 * B + 16) false = false := by
  rw [t1T, show 8 * B + 16 = 2 * jF + (2 * (4 * B + 8 - jF) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jF),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem t1T_getD_R1end_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 4 * B + 8) :
    (t1T B P jF jR x E).getD (8 * B + 17) false = true := by
  rw [t1T, show 8 * B + 17 = 2 * jF + (2 * (4 * B + 8 - jF) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jF),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-- Reading region 2 and beyond. -/
theorem t1T_getD_R2 (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 4 * B + 8) :
    (t1T B P jF jR x E).getD (8 * B + 18 + c) false
      = (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true ++ ([false, true]
          ++ (xVis x x.length ++ E)))).getD c false := by
  rw [t1T, show 8 * B + 18 + c = 2 * jF + (2 * (4 * B + 8 - jF) + (2 + c)) from by omega,
    getD_append_left_length' _ _ (markedD_length jF),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t1T_getD_R2mark_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 4 * B + 8) (h : i < jR) :
    (t1T B P jF jR x E).getD (8 * B + 18 + 2 * i) false = true := by
  rw [t1T_getD_R2 B P jF jR x E _ hjF,
    List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jR i h

theorem t1T_getD_R2mark_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 4 * B + 8) (h : i < jR) :
    (t1T B P jF jR x E).getD (8 * B + 18 + 2 * i + 1) false = false := by
  have h2 := t1T_getD_R2 B P jF jR x E (2 * i + 1) hjF
  rw [show 8 * B + 18 + (2 * i + 1) = 8 * B + 18 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jR i h

theorem t1T_getD_R2data (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 4 * B + 8) (hjR : jR ≤ P + 1) (h1 : 2 * jR ≤ c) (h2 : c < 2 * P + 2) :
    (t1T B P jF jR x E).getD (8 * B + 18 + c) false = true := by
  rw [t1T_getD_R2 B P jF jR x E _ hjF, show c = 2 * jR + (c - 2 * jR) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t1T_getD_R2end_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 4 * B + 8) (hjR : jR ≤ P + 1) :
    (t1T B P jF jR x E).getD (8 * B + 18 + (2 * P + 2)) false = false := by
  rw [t1T_getD_R2 B P jF jR x E _ hjF,
    show 2 * P + 2 = 2 * jR + (2 * (P + 1 - jR) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem t1T_getD_R2end_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 4 * B + 8) (hjR : jR ≤ P + 1) :
    (t1T B P jF jR x E).getD (8 * B + 18 + (2 * P + 3)) false = true := by
  rw [t1T_getD_R2 B P jF jR x E _ hjF,
    show 2 * P + 3 = 2 * jR + (2 * (P + 1 - jR) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ## The write lemmas -/

/-- Consume the remainder's next pair. -/
theorem t1T_markR2 (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 4 * B + 8) (hjR : jR < P + 1) :
    writeAt (t1T B P jF jR x E) (8 * B + 18 + (2 * jR + 1)) false
      = t1T B P jF (jR + 1) x E := by
  rw [writeAt_of_lt false (by
      simp only [t1T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length]
      omega), t1T,
    show 8 * B + 18 + (2 * jR + 1)
      = 2 * jF + (2 * (4 * B + 8 - jF) + (2 + (2 * jR + 1))) from by omega,
    set_append_left_length' _ _ (markedD_length jF),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (markedD_length jR),
    show List.replicate (2 * (P + 1 - jR)) true
      = true :: true :: List.replicate (2 * (P + 1 - jR - 1)) true from by
        rw [show 2 * (P + 1 - jR) = 2 * (P + 1 - jR - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t1T, ← markedD_snoc, show P + 1 - (jR + 1) = P + 1 - jR - 1 from by omega]
  simp [List.append_assoc]

/-- Mark the next front pair. -/
theorem t1T_markF (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF < 4 * B + 8) :
    writeAt (t1T B P jF jR x E) (2 * jF + 1) false = t1T B P (jF + 1) jR x E := by
  rw [writeAt_of_lt false (by
      simp only [t1T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length]
      omega), t1T,
    set_append_left_length' _ _ (markedD_length jF),
    show List.replicate (2 * (4 * B + 8 - jF)) true
      = true :: true :: List.replicate (2 * (4 * B + 8 - jF - 1)) true from by
        rw [show 2 * (4 * B + 8 - jF) = 2 * (4 * B + 8 - jF - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t1T, ← markedD_snoc, show 4 * B + 8 - (jF + 1) = 4 * B + 8 - jF - 1 from by omega]
  simp [List.append_assoc]

/-- Place `T1`'s marker `0` at position `2B` (front fully marked, remainder spent). -/
theorem t1T_marker (B P : ℕ) (x : List Bool) (E : List Bool) :
    writeAt (t1T B P B (P + 1) x E) (2 * B) false = t1H B P 0 x E := by
  rw [writeAt_of_lt false (by
      simp only [t1T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length]
      omega), t1T,
    show 2 * B = 2 * B + 0 from by omega,
    set_append_left_length' _ _ (markedD_length B),
    show List.replicate (2 * (4 * B + 8 - B)) true
      = true :: List.replicate (6 * B + 15) true from by
        rw [show 2 * (4 * B + 8 - B) = 6 * B + 15 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_zero]
  rw [t1H, Nat.sub_zero,
    show (2 * 0 : ℕ) = 0 from by omega, List.replicate_zero,
    show 2 * (P + 1 - (P + 1)) = 0 from by omega, List.replicate_zero]
  simp

/-- Heal one front pair. -/
theorem t1H_heal (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < B) :
    writeAt (t1H B P i x E) (2 * i + 1) true = t1H B P (i + 1) x E := by
  rw [writeAt_of_lt true (by
      simp only [t1H, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length]
      omega), t1H,
    show 2 * i + 1 = 2 * i + 1 from rfl,
    set_append_left_length' _ _ List.length_replicate,
    show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
      rw [show B - i = B - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t1H, show B - (i + 1) = B - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ### Heal-walk reads -/

theorem t1H_getD_lo (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < B) :
    (t1H B P i x E).getD (2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (B - i) ++ (false :: (List.replicate (6 * B + 15) true ++ ([false, true]
      ++ (markedD (P + 1) ++ ([false, true] ++ (xVis x x.length ++ E)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t1H, h, show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
    rw [show B - i = B - i - 1 + 1 from by omega]
    rfl]
  rfl

theorem t1H_getD_hi (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < B) :
    (t1H B P i x E).getD (2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (B - i) ++ (false :: (List.replicate (6 * B + 15) true ++ ([false, true]
      ++ (markedD (P + 1) ++ ([false, true] ++ (xVis x x.length ++ E)))))))
    List.length_replicate 1 false
  rw [t1H, h, show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
    rw [show B - i = B - i - 1 + 1 from by omega]
    rfl]
  rfl

theorem t1H_getD_done (B P : ℕ) (x : List Bool) (E : List Bool) :
    (t1H B P B x E).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    (markedD (B - B) ++ (false :: (List.replicate (6 * B + 15) true ++ ([false, true]
      ++ (markedD (P + 1) ++ ([false, true] ++ (xVis x x.length ++ E)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t1H, h, Nat.sub_self]
  rfl

/-! ## The transcription machine

Control: `State = Fin 13 × Bool`.  Phases: `0/1` cross region 1's pair-field
(content-blind: marked and unmarked lows are true; boundary `01` ⇒ find), `2/3` find in
region 2 (skip `10`, mark `11` ⇒ **reset** to the front-find, boundary `01` ⇒ **reset**
to the marker phase), `4/5` front-find (skip `10`, mark `11` ⇒ **reset**, next round),
`6/7` marker-find (skip `10`, at `11` step **left**), `8` write the marker's `0` and
reset, `9/10` heal sweep (`10 ↦ 11`; low `0` ⇒ **done**), `11` done, `12` dead. -/

def t1Machine : Machine where
  State := Fin 13 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 11) || decide (s.1 = 12)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then ((0, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((12, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then (if b then ((4, s.2), some false, 3) else ((2, s.2), none, 1))
       else (if b then ((6, s.2), none, 3) else ((12, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then (if b then ((0, s.2), some false, 3) else ((4, s.2), none, 1))
       else ((12, s.2), none, 2))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if s.2 then (if b then ((8, s.2), none, 0) else ((6, s.2), none, 1))
       else ((12, s.2), none, 2))
    else if s.1 = 8 then ((9, s.2), some false, 3)
    else if s.1 = 9 then
      (if b then ((10, b), none, 1) else ((11, s.2), none, 2))
    else if s.1 = 10 then
      (if b then ((12, s.2), none, 2) else ((9, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 11)

theorem init_t1 (x : List Bool) : init t1Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_t0 {s : Bool} {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t1_skip {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t1_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(1, false), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t3_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t1Machine ⟨(3, true), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t3_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(3, true), p, T⟩ = ⟨(4, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t3_bound {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(3, false), p, T⟩ = ⟨(6, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t5_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t1Machine ⟨(5, true), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t5_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(5, true), p, T⟩ = ⟨(0, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t6 {s : Bool} {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t7_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t1Machine ⟨(7, true), p, T⟩ = ⟨(6, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t7_found {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(7, true), p, T⟩ = ⟨(8, true), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t8 {s : Bool} {p : ℕ} {T : List Bool} :
    step t1Machine ⟨(8, s), p, T⟩ = ⟨(9, s), 0, writeAt T p false⟩ := by
  simp only [step, t1Machine, moveHead]; rfl

theorem step_t9_go {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t1Machine ⟨(9, s), p, T⟩ = ⟨(10, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t9_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t1Machine ⟨(9, s), p, T⟩ = ⟨(11, s), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

theorem step_t10_heal {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t1Machine ⟨(10, true), p, T⟩ = ⟨(9, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t1Machine, moveHead, h]

/-! ### Pair-step lemmas -/

theorem t1run_two_skipAny {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) :
    run t1Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t0, h1, step_t1_skip]

theorem t1run_two_cross {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t1Machine 2 ⟨(0, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t0, h1, step_t1_cross h2]

theorem t1run_two_skipTF2 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t1Machine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t2, h1, step_t3_skip h2]

theorem t1run_two_markR2 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t1Machine 2 ⟨(2, s), p, T⟩ = ⟨(4, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_t2, h1, step_t3_mark h2]

theorem t1run_two_bound {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t1Machine 2 ⟨(2, s), p, T⟩ = ⟨(6, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t2, h1, step_t3_bound h2]

theorem t1run_two_skipTF4 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t1Machine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t4, h1, step_t5_skip h2]

theorem t1run_two_markF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t1Machine 2 ⟨(4, s), p, T⟩ = ⟨(0, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_t4, h1, step_t5_mark h2]

theorem t1run_two_skipTF6 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t1Machine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_t6, h1, step_t7_skip h2]

theorem t1run_three_marker {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t1Machine 3 ⟨(6, s), p, T⟩ = ⟨(9, true), 0, writeAt T p false⟩ := by
  rw [run_succ, run_succ, run_succ, run_zero, step_t6, h1, step_t7_found h2,
    show p + 1 - 1 = p from by omega, step_t8]

theorem t1run_two_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t1Machine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_t9_go h1, step_t10_heal h2]

theorem t1run_one_done {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = false) :
    run t1Machine 1 ⟨(9, s), p, T⟩ = ⟨(11, s), p, T⟩ := by
  rw [run_succ, run_zero, step_t9_done h]

/-! ### Scan run-invariants -/

theorem t1run_skipAnyK (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t1Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), t1run_two_skipAny (h k (by omega))]
    rfl

theorem t1run_skipTF2K (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t1Machine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), t1run_two_skipTF2 hk.1 hk.2]
    rfl

theorem t1run_skipTF4K (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t1Machine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), t1run_two_skipTF4 hk.1 hk.2]
    rfl

theorem t1run_skipTF6K (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t1Machine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), t1run_two_skipTF6 hk.1 hk.2]
    rfl

/-- The heal sweep: `k` pairs from pair `i`, tape evolving. -/
theorem t1run_heal (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ B →
    run t1Machine (2 * k) ⟨(9, s), 2 * i, t1H B P i x E⟩
      = ⟨(9, if k = 0 then s else true), 2 * (i + k), t1H B P (i + k) x E⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    have hlo := t1H_getD_lo B P i x E (by omega)
    have hhi := t1H_getD_hi B P i x E (by omega)
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      t1run_two_heal hlo hhi, t1H_heal B P i x E (by omega),
      show 2 * i + 2 = 2 * (i + 1) from by ring, ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The round invariant -/

/-- **One transcription round**: consume remainder pair `j`, mark front pair `j`. -/
theorem t1_round (B P : ℕ) (x : List Bool) (E : List Bool) (j : ℕ) (s : Bool)
    (hj : j < B) (hP : P = x.length + B) :
    run t1Machine (8 * B + 2 * x.length + 4 * j + 24)
      ⟨(0, s), 0, t1T B P j (x.length + 1 + j) x E⟩
      = ⟨(0, true), 0, t1T B P (j + 1) (x.length + 1 + j + 1) x E⟩ := by
  -- Stage 1: cross region 1's pair-field.
  have st1 := t1run_skipAnyK (t1T B P j (x.length + 1 + j) x E) 0 (4 * B + 8) s
    (fun i hi => by
      simpa using t1T_getD_R1lo B P j (x.length + 1 + j) x E i (by omega) hi)
  simp only [Nat.zero_add] at st1
  rw [if_neg (show ¬(4 * B + 8 = 0) from by omega),
    show 2 * (4 * B + 8) = 8 * B + 16 from by ring] at st1
  -- Stage 2: cross the boundary.
  have h2hi := t1T_getD_R1end_hi B P j (x.length + 1 + j) x E (by omega)
  rw [show 8 * B + 17 = 8 * B + 16 + 1 from by omega] at h2hi
  have st2 := t1run_two_cross (s := true) (p := 8 * B + 16)
    (T := t1T B P j (x.length + 1 + j) x E)
    (t1T_getD_R1end_lo B P j (x.length + 1 + j) x E (by omega)) h2hi
  rw [show 8 * B + 16 + 2 = 8 * B + 18 from by omega] at st2
  -- Stage 3: skip region 2's marked pairs.
  have st3 := t1run_skipTF2K (t1T B P j (x.length + 1 + j) x E) (8 * B + 18)
    (x.length + 1 + j) false (fun i hi =>
    ⟨t1T_getD_R2mark_lo B P j (x.length + 1 + j) x E i (by omega) hi,
     t1T_getD_R2mark_hi B P j (x.length + 1 + j) x E i (by omega) hi⟩)
  -- Stage 4: consume remainder pair `j` (reset).
  have h4hi : (t1T B P j (x.length + 1 + j) x E).getD
      (8 * B + 18 + 2 * (x.length + 1 + j) + 1) false = true := by
    have h := t1T_getD_R2data B P j (x.length + 1 + j) x E (2 * (x.length + 1 + j) + 1)
      (by omega) (by omega) (by omega) (by omega)
    rwa [show 8 * B + 18 + (2 * (x.length + 1 + j) + 1)
      = 8 * B + 18 + 2 * (x.length + 1 + j) + 1 from by omega] at h
  have st4 := t1run_two_markR2 (s := if x.length + 1 + j = 0 then false else true)
    (p := 8 * B + 18 + 2 * (x.length + 1 + j)) (T := t1T B P j (x.length + 1 + j) x E)
    (t1T_getD_R2data B P j (x.length + 1 + j) x E (2 * (x.length + 1 + j)) (by omega)
      (by omega) (by omega) (by omega)) h4hi
  rw [show 8 * B + 18 + 2 * (x.length + 1 + j) + 1
      = 8 * B + 18 + (2 * (x.length + 1 + j) + 1) from by omega,
    t1T_markR2 B P j (x.length + 1 + j) x E (by omega) (by omega)] at st4
  -- Stage 5: skip the `j` front marks.
  have st5 := t1run_skipTF4K (t1T B P j (x.length + 1 + j + 1) x E) 0 j true
    (fun i hi => ⟨by
      simpa using t1T_getD_R1lo B P j (x.length + 1 + j + 1) x E i (by omega) (by omega),
      by simpa using t1T_getD_R1mark_hi B P j (x.length + 1 + j + 1) x E i hi⟩)
  simp only [Nat.zero_add, ite_self] at st5
  -- Stage 6: mark front pair `j` (reset).
  have st6 := t1run_two_markF (s := true) (p := 2 * j)
    (T := t1T B P j (x.length + 1 + j + 1) x E)
    (t1T_getD_R1lo B P j (x.length + 1 + j + 1) x E j (by omega) (by omega))
    (t1T_getD_R1data_hi B P j (x.length + 1 + j + 1) x E j (le_refl _) (by omega))
  rw [t1T_markF B P j (x.length + 1 + j + 1) x E (by omega)] at st6
  -- Assemble.
  rw [show 8 * B + 2 * x.length + 4 * j + 24
      = 8 * B + 16 + (2 + (2 * (x.length + 1 + j) + (2 + (2 * j + 2)))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, st6]

/-! ## The rounds and the endgame -/

/-- The cumulative clock of the first `k` rounds. -/
def t1Rounds (B n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t1Rounds B n k + (8 * B + 2 * n + 4 * k + 24)

theorem t1_rounds (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ B) (hP : P = x.length + B) :
    run t1Machine (t1Rounds B x.length k) ⟨(0, s), 0, t1T B P 0 (x.length + 1) x E⟩
      = ⟨(0, if k = 0 then s else true), 0, t1T B P k (x.length + 1 + k) x E⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show t1Rounds B x.length (k + 1)
        = t1Rounds B x.length k + (8 * B + 2 * x.length + 4 * k + 24) from rfl,
      run_add, ih (by omega), t1_round B P x E k _ (by omega) hP,
      if_neg (by omega), show x.length + 1 + (k + 1) = x.length + 1 + k + 1 from by omega]

/-- The pass's exact clock. -/
def t1Clock (B P n : ℕ) : ℕ := t1Rounds B n B + (12 * B + 2 * P + 26)

/-- **THE FIRST TRANSCRIPTION WRITE RUNS**: from brick M2's exit, the pass halts DONE at
head `2B` with the six-region target's first region, `unaryD B`, written verbatim at the
front. -/
theorem t1Machine_run (B P : ℕ) (x : List Bool) (E : List Bool)
    (hP : P = x.length + B) :
    run t1Machine (t1Clock B P x.length)
      (init t1Machine (subT B P (x.length + 1) x x.length E))
      = ⟨(11, true), 2 * B, t1Out B P x E⟩ := by
  rw [init_t1, ← t1T_zero, t1Clock, run_add,
    t1_rounds B P x E B false (le_refl _) hP,
    show x.length + 1 + B = P + 1 from by omega]
  -- Stage 1: cross region 1's pair-field.
  have st1 := t1run_skipAnyK (t1T B P B (P + 1) x E) 0 (4 * B + 8)
    (if B = 0 then false else true) (fun i hi => by
      simpa using t1T_getD_R1lo B P B (P + 1) x E i (by omega) hi)
  simp only [Nat.zero_add] at st1
  rw [if_neg (show ¬(4 * B + 8 = 0) from by omega),
    show 2 * (4 * B + 8) = 8 * B + 16 from by ring] at st1
  -- Stage 2: cross the boundary.
  have h2hi := t1T_getD_R1end_hi B P B (P + 1) x E (by omega)
  rw [show 8 * B + 17 = 8 * B + 16 + 1 from by omega] at h2hi
  have st2 := t1run_two_cross (s := true) (p := 8 * B + 16) (T := t1T B P B (P + 1) x E)
    (t1T_getD_R1end_lo B P B (P + 1) x E (by omega)) h2hi
  rw [show 8 * B + 16 + 2 = 8 * B + 18 from by omega] at st2
  -- Stage 3: skip region 2's `P+1` marks.
  have st3 := t1run_skipTF2K (t1T B P B (P + 1) x E) (8 * B + 18) (P + 1) false
    (fun i hi =>
    ⟨t1T_getD_R2mark_lo B P B (P + 1) x E i (by omega) hi,
     t1T_getD_R2mark_hi B P B (P + 1) x E i (by omega) hi⟩)
  rw [show 8 * B + 18 + 2 * (P + 1) = 8 * B + 18 + (2 * P + 2) from by omega] at st3
  -- Stage 4: the remainder is spent — hit the boundary (reset).
  have h4hi := t1T_getD_R2end_hi B P B (P + 1) x E (by omega) (le_refl _)
  rw [show 8 * B + 18 + (2 * P + 3) = 8 * B + 18 + (2 * P + 2) + 1 from by omega] at h4hi
  have st4 := t1run_two_bound (s := if P + 1 = 0 then false else true)
    (p := 8 * B + 18 + (2 * P + 2)) (T := t1T B P B (P + 1) x E)
    (t1T_getD_R2end_lo B P B (P + 1) x E (by omega) (le_refl _)) h4hi
  -- Stage 5: seek the first unmarked front pair.
  have st5 := t1run_skipTF6K (t1T B P B (P + 1) x E) 0 B false
    (fun i hi => ⟨by
      simpa using t1T_getD_R1lo B P B (P + 1) x E i (by omega) (by omega),
      by simpa using t1T_getD_R1mark_hi B P B (P + 1) x E i hi⟩)
  simp only [Nat.zero_add] at st5
  -- Stage 6: place the marker and reset.
  have st6 := t1run_three_marker (s := if B = 0 then false else true) (p := 2 * B)
    (T := t1T B P B (P + 1) x E)
    (t1T_getD_R1lo B P B (P + 1) x E B (by omega) (by omega))
    (t1T_getD_R1data_hi B P B (P + 1) x E B (le_refl _) (by omega))
  rw [t1T_marker B P x E] at st6
  -- Stage 7: heal the front marks.
  have st7 := t1run_heal B P x E B 0 true (by omega)
  rw [show (2 * 0 : ℕ) = 0 from by omega, show (0 + B : ℕ) = B from by omega,
    ite_self] at st7
  -- Stage 8: read the marker's `0`: DONE.
  have st8 := t1run_one_done (s := true) (p := 2 * B) (T := t1H B P B x E)
    (t1H_getD_done B P x E)
  -- Assemble the endgame.
  rw [show 12 * B + 2 * P + 26
      = 8 * B + 16 + (2 + (2 * (P + 1) + (2 + (2 * B + (3 + (2 * B + 1)))))) from by
        omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, st8, t1H_out B P x E]

/-- The done state halts. -/
theorem t1Machine_halt11 : t1Machine.halt ((11 : Fin 13), true) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1
