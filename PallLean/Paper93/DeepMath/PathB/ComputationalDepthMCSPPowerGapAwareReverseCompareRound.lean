import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPPowerGapAwareReverseCompareMachine

/-!
# MCSP verifier: one complete physical reverse-comparator round

This file transports the ordinary comparator's scan invariants onto the exact
retained-gap tape and composes one destructive round.  The only clock change is
the tagged `01 00` crossing: four transitions instead of the ordinary two,
hence exactly `+2` per round.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareCompareHomeMachine
open PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareMachine

/-! ## Work-counter structure -/

theorem workD_getD_mark_lo (a j i : ℕ) (hi : i < j) :
    (workD a j).getD (2 * i) false = true := by
  unfold workD
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo j i hi

theorem workD_getD_mark_hi (a j i : ℕ) (hi : i < j) :
    (workD a j).getD (2 * i + 1) false = false := by
  unfold workD
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi j i hi

theorem workD_getD_data (a j c : ℕ) (hj : j ≤ a)
    (hlo : 2 * j ≤ c) (hhi : c < 2 * a) :
    (workD a j).getD c false = true := by
  unfold workD
  simp only [List.append_assoc]
  rw [show c = 2 * j + (c - 2 * j) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem workD_getD_end_lo (a j : ℕ) (hj : j ≤ a) :
    (workD a j).getD (2 * a) false = false := by
  unfold workD
  simp only [List.append_assoc]
  rw [show 2 * a = 2 * j + (2 * (a - j) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem workD_getD_end_hi (a j : ℕ) (hj : j ≤ a) :
    (workD a j).getD (2 * a + 1) false = true := by
  unfold workD
  simp only [List.append_assoc]
  rw [show 2 * a + 1 =
      2 * j + (2 * (a - j) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem workD_mark (a j : ℕ) (hj : j < a) :
    writeAt (workD a j) (2 * j + 1) false = workD a (j + 1) := by
  rw [writeAt_of_lt false (by rw [workD_length a j (by omega)]; omega)]
  unfold workD
  simp only [List.append_assoc]
  rw [set_append_left_length' _ _ (markedD_length j),
    show 2 * (a - j) = 2 * (a - j - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show a - j - 1 = a - (j + 1) from by omega]

/-! ## Exact reads and writes on the physical descriptor -/

theorem reverseT_getD_Amark_lo (a b jA jB i : ℕ) (rest : List Bool)
    (hi : i < jA) :
    (reversePhysicalTape a b jA jB rest).getD (2 * i) false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [List.getD_append (h := by
    simp [workD, markedD_length]; omega)]
  exact workD_getD_mark_lo a jA i hi

theorem reverseT_getD_Amark_hi (a b jA jB i : ℕ) (rest : List Bool)
    (hi : i < jA) :
    (reversePhysicalTape a b jA jB rest).getD (2 * i + 1) false = false := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [List.getD_append (h := by
    simp [workD, markedD_length]; omega)]
  exact workD_getD_mark_hi a jA i hi

theorem reverseT_getD_Adata (a b jA jB c : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hlo : 2 * jA ≤ c) (hhi : c < 2 * a) :
    (reversePhysicalTape a b jA jB rest).getD c false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [workD_length a jA hjA]; omega)]
  exact workD_getD_data a jA c hjA hlo hhi

theorem reverseT_getD_Aend_lo (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) :
    (reversePhysicalTape a b jA jB rest).getD (2 * a) false = false := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [workD_length a jA hjA]; omega)]
  exact workD_getD_end_lo a jA hjA

theorem reverseT_getD_Aend_hi (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) :
    (reversePhysicalTape a b jA jB rest).getD (2 * a + 1) false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [workD_length a jA hjA]; omega)]
  exact workD_getD_end_hi a jA hjA

theorem reverseT_getD_Bmark_lo (a b jA jB i : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hi : i < jB) :
    (reversePhysicalTape a b jA jB rest).getD
        (2 * a + 4 + 2 * i) false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * i =
      (2 * a + 2) + (2 + 2 * i) by omega,
    getD_append_left_length' _ _ (workD_length a jA hjA),
    getD_append_left_length' _ _
      (show ([false, false] : List Bool).length = 2 from rfl)]
  rw [List.getD_append (h := by
    simp [workD, markedD_length]; omega)]
  exact workD_getD_mark_lo b jB i hi

theorem reverseT_getD_Bmark_hi (a b jA jB i : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hi : i < jB) :
    (reversePhysicalTape a b jA jB rest).getD
        (2 * a + 4 + 2 * i + 1) false = false := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * i + 1 =
      (2 * a + 2) + (2 + (2 * i + 1)) by omega,
    getD_append_left_length' _ _ (workD_length a jA hjA),
    getD_append_left_length' _ _
      (show ([false, false] : List Bool).length = 2 from rfl)]
  rw [List.getD_append (h := by
    simp [workD, markedD_length]; omega)]
  exact workD_getD_mark_hi b jB i hi

theorem reverseT_getD_Bdata (a b jA jB c : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hjB : jB ≤ b)
    (hlo : 2 * jB ≤ c) (hhi : c < 2 * b) :
    (reversePhysicalTape a b jA jB rest).getD
        (2 * a + 4 + c) false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + c =
      (2 * a + 2) + (2 + c) by omega,
    getD_append_left_length' _ _ (workD_length a jA hjA),
    getD_append_left_length' _ _
      (show ([false, false] : List Bool).length = 2 from rfl)]
  rw [List.getD_append (h := by
    rw [workD_length b jB hjB]; omega)]
  exact workD_getD_data b jB c hjB hlo hhi

theorem reverseT_getD_Bend_lo (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hjB : jB ≤ b) :
    (reversePhysicalTape a b jA jB rest).getD
        (2 * a + 4 + 2 * b) false = false := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * b =
      (2 * a + 2) + (2 + 2 * b) by omega,
    getD_append_left_length' _ _ (workD_length a jA hjA),
    getD_append_left_length' _ _
      (show ([false, false] : List Bool).length = 2 from rfl)]
  rw [List.getD_append (h := by
    rw [workD_length b jB hjB]; omega)]
  exact workD_getD_end_lo b jB hjB

theorem reverseT_getD_Bend_hi (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hjB : jB ≤ b) :
    (reversePhysicalTape a b jA jB rest).getD
        (2 * a + 4 + 2 * b + 1) false = true := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * b + 1 =
      (2 * a + 2) + (2 + (2 * b + 1)) by omega,
    getD_append_left_length' _ _ (workD_length a jA hjA),
    getD_append_left_length' _ _
      (show ([false, false] : List Bool).length = 2 from rfl)]
  rw [List.getD_append (h := by
    rw [workD_length b jB hjB]; omega)]
  exact workD_getD_end_hi b jB hjB

private theorem writeAt_inside_left (A R : List Bool) (p : ℕ)
    (w : Bool) (hp : p < A.length) :
    writeAt (A ++ R) p w = writeAt A p w ++ R := by
  rw [writeAt_of_lt w (by simp; omega), writeAt_of_lt w hp,
    List.set_append_left _ _ hp]

private theorem writeAt_inside_right (P X : List Bool) (p : ℕ)
    (w : Bool) (hp : p < X.length) :
    writeAt (P ++ X) (P.length + p) w = P ++ writeAt X p w := by
  rw [writeAt_of_lt w (by simp; omega), writeAt_of_lt w hp,
    set_append_left_length]

theorem reverseT_markA (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA < a) (hjB : jB ≤ b) :
    writeAt (reversePhysicalTape a b jA jB rest)
      (2 * jA + 1) false =
        reversePhysicalTape a b (jA + 1) jB rest := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [writeAt_inside_left (workD a jA)
      ([false, false] ++ (workD b jB ++ rest))
      (2 * jA + 1) false
      (by rw [workD_length a jA (by omega)]; omega),
    workD_mark a jA hjA]

theorem reverseT_markB (a b jA jB : ℕ) (rest : List Bool)
    (hjA : jA ≤ a) (hjB : jB < b) :
    writeAt (reversePhysicalTape a b jA jB rest)
      (2 * a + 4 + 2 * jB + 1) false =
        reversePhysicalTape a b jA (jB + 1) rest := by
  unfold reversePhysicalTape compareHomeTape
  simp only [List.append_assoc]
  rw [show 2 * a + 4 + 2 * jB + 1 =
      (workD a jA).length + (2 + (2 * jB + 1)) by
        rw [workD_length a jA hjA]; omega,
    writeAt_inside_right (workD a jA)
      ([false, false] ++ (workD b jB ++ rest))
      (2 + (2 * jB + 1)) false
      (by simp [workD_length b jB (by omega)]; omega),
    show 2 + (2 * jB + 1) =
      ([false, false] : List Bool).length + (2 * jB + 1) from rfl,
    writeAt_inside_right [false, false] (workD b jB ++ rest)
      (2 * jB + 1) false
      (by simp [workD_length b jB (by omega)]; omega),
    writeAt_inside_left (workD b jB) rest (2 * jB + 1) false
      (by rw [workD_length b jB (by omega)]; omega),
    workD_mark b jB hjB]

/-! ## Generic physical scan runs -/

private theorem getD_boundary (P : List Bool) (b : Bool) (R : List Bool) :
    (P ++ b :: R).getD P.length false = b := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem run_reverse_two_skipA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run reverseCompareMachine 2 ⟨.cmp 0 s, p, T⟩ =
      ⟨.cmp 0 true, p + 2, T⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 0 s, p, T⟩) = _
  rw [step_reverse_c0, h1, step_reverse_c1_skip h2]

theorem run_reverse_two_markA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run reverseCompareMachine 2 ⟨.cmp 0 s, p, T⟩ =
      ⟨.cmp 2 true, p + 2, writeAt T (p + 1) false⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 0 s, p, T⟩) = _
  rw [step_reverse_c0, h1, step_reverse_c1_mark h2]

theorem run_reverse_two_seek {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run reverseCompareMachine 2 ⟨.cmp 2 s, p, T⟩ =
      ⟨.cmp 2 true, p + 2, T⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 2 s, p, T⟩) = _
  rw [step_reverse_c2, h1, step_reverse_c3_data h2]

theorem run_reverse_four_cross (P R : List Bool) :
    run reverseCompareMachine 4
      ⟨.cmp 2 true, P.length,
        P ++ false :: true :: false :: false :: R⟩ =
      ⟨.cmp 4 false, P.length + 4,
        P ++ false :: true :: false :: false :: R⟩ := by
  rw [show 4 = 1 + 3 by omega, run_add]
  change run reverseCompareMachine 3
    (step reverseCompareMachine
      ⟨.cmp 2 true, P.length,
        P ++ false :: true :: false :: false :: R⟩) = _
  rw [step_reverse_c2, getD_boundary]
  rw [show P ++ false :: true :: false :: false :: R =
      (P ++ [false]) ++ true :: false :: false :: R by simp]
  simpa using run_reverse_crossGap (P ++ [false]) R

theorem run_reverse_two_skipB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run reverseCompareMachine 2 ⟨.cmp 4 s, p, T⟩ =
      ⟨.cmp 4 true, p + 2, T⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 4 s, p, T⟩) = _
  rw [step_reverse_c4, h1, step_reverse_c5_skip h2]

theorem run_reverse_two_markB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run reverseCompareMachine 2 ⟨.cmp 4 s, p, T⟩ =
      ⟨.cmp 0 true, 0, writeAt T (p + 1) false⟩ := by
  rw [show 2 = 1 + 1 by omega, run_add]
  change step reverseCompareMachine
    (step reverseCompareMachine ⟨.cmp 4 s, p, T⟩) = _
  rw [step_reverse_c4, h1, step_reverse_c5_mark h2]

theorem run_reverse_skipA (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = false) :
    run reverseCompareMachine (2 * k) ⟨.cmp 0 s, q, T⟩ =
      ⟨.cmp 0 (if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, run_add,
        ih (fun i hi => h i (by omega)), run_reverse_two_skipA hk.1 hk.2]
      rfl

theorem run_reverse_seek (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = true) :
    run reverseCompareMachine (2 * k) ⟨.cmp 2 s, q, T⟩ =
      ⟨.cmp 2 (if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, run_add,
        ih (fun i hi => h i (by omega)), run_reverse_two_seek hk.1 hk.2]
      rfl

theorem run_reverse_skipB (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧
      T.getD (q + 2 * i + 1) false = false) :
    run reverseCompareMachine (2 * k) ⟨.cmp 4 s, q, T⟩ =
      ⟨.cmp 4 (if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := h k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, run_add,
        ih (fun i hi => h i (by omega)), run_reverse_two_skipB hk.1 hk.2]
      rfl

/-! ## One complete physical round -/

def reverseRoundClock (a j : ℕ) : ℕ := 2 * a + 2 * j + 6

theorem run_reverse_round (a b j : ℕ) (rest : List Bool)
    (hja : j < a) (hjb : j < b) (s : Bool) :
    run reverseCompareMachine (reverseRoundClock a j)
      ⟨.cmp 0 s, 0, reversePhysicalTape a b j j rest⟩ =
      ⟨.cmp 0 true, 0,
        reversePhysicalTape a b (j + 1) (j + 1) rest⟩ := by
  have st1 := run_reverse_skipA (reversePhysicalTape a b j j rest)
    0 j s (fun i hi =>
      ⟨by simpa using reverseT_getD_Amark_lo a b j j i rest hi,
       by simpa using reverseT_getD_Amark_hi a b j j i rest hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_reverse_two_markA
    (s := if j = 0 then s else true) (p := 2 * j)
    (T := reversePhysicalTape a b j j rest)
    (reverseT_getD_Adata a b j j (2 * j) rest (by omega) (by omega) (by omega))
    (reverseT_getD_Adata a b j j (2 * j + 1) rest (by omega) (by omega) (by omega))
  rw [reverseT_markA a b j j rest hja (by omega)] at st2
  have st3 := run_reverse_seek
    (reversePhysicalTape a b (j + 1) j rest)
    (2 * j + 2) (a - j - 1) true (fun i hi =>
      ⟨reverseT_getD_Adata a b (j + 1) j
          (2 * j + 2 + 2 * i) rest (by omega) (by omega) (by omega),
       reverseT_getD_Adata a b (j + 1) j
          (2 * j + 2 + 2 * i + 1) rest (by omega) (by omega) (by omega)⟩)
  rw [show 2 * j + 2 + 2 * (a - j - 1) = 2 * a from by omega] at st3
  simp only [ite_self] at st3
  let Apre : List Bool :=
    markedD (j + 1) ++ List.replicate (2 * (a - (j + 1))) true
  have hApre : Apre.length = 2 * a := by
    simp [Apre, markedD_length]
    omega
  have st4raw := run_reverse_four_cross Apre
    (workD b j ++ rest)
  have st4 : run reverseCompareMachine 4
      ⟨.cmp 2 true, 2 * a,
        reversePhysicalTape a b (j + 1) j rest⟩ =
      ⟨.cmp 4 false, 2 * a + 4,
        reversePhysicalTape a b (j + 1) j rest⟩ := by
    convert st4raw using 1 <;>
      simp [Apre, reversePhysicalTape, compareHomeTape, workD,
        List.append_assoc, hApre] <;> omega
  have st5 := run_reverse_skipB
    (reversePhysicalTape a b (j + 1) j rest)
    (2 * a + 4) j false (fun i hi =>
      ⟨reverseT_getD_Bmark_lo a b (j + 1) j i rest (by omega) hi,
       reverseT_getD_Bmark_hi a b (j + 1) j i rest (by omega) hi⟩)
  have st6 := run_reverse_two_markB
    (s := if j = 0 then false else true)
    (p := 2 * a + 4 + 2 * j)
    (T := reversePhysicalTape a b (j + 1) j rest)
    (reverseT_getD_Bdata a b (j + 1) j (2 * j) rest
      (by omega) (by omega) (by omega) (by omega))
    (reverseT_getD_Bdata a b (j + 1) j (2 * j + 1) rest
      (by omega) (by omega) (by omega) (by omega))
  rw [reverseT_markB a b (j + 1) j rest (by omega) hjb] at st6
  unfold reverseRoundClock
  rw [show 2 * a + 2 * j + 6 =
      2 * j + (2 + (2 * (a - j - 1) + (4 + (2 * j + 2))))
        from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4,
    run_add, st5, st6]

end PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound.workD_mark
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound.reverseT_markA
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound.reverseT_markB
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPPowerGapAwareReverseCompareRound.run_reverse_round
