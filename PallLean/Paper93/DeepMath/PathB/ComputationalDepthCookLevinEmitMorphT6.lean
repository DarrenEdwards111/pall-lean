import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT5

/-!
# Cook–Levin M2 emitter — arming morph brick M9: THE `T6` FILL (the last pass)

`T6`'s capacity span (`P+2` zero-pairs behind its placed marker), by the zero-fill
fabric with a MODIFIED ENDGAME ADVANCE: its third write is `0` instead of `1` — no new
frontier is planted, the erased frontier and the two fresh zeros complete the fill in
place, and nothing beyond the target is ever touched.  The exit is the COMPLETE
six-region morph prefix, flush against the output region.

New crossing: after `T5`'s live pair and marker, `T5`'s own zero-fill is skipped by
high-cell check with the exit event being `T6`'s marker (both fill pairs and the marker
have a false low; the marker's true high is the event).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT6

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT5

/-! ## The descriptor family -/

/-- Mid-pass: `jS` source pairs marked, `jW` zero-fill advances done. -/
def t6T (B P jS jW : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
    ++ ([false, true]
    ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))))

/-- Mid-advance. -/
def t6A (B P jS jW : ℕ) (u v : Bool) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
    ++ ([false, true]
    ++ (List.replicate (2 * jW + 2) false ++ (u :: v :: rest)))))))))

/-- Post-endgame, pre-heal: the fill complete. -/
def t6M (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD P ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
    ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest)))))))

/-- Mid-heal: `i` source marks healed. -/
def t6H (B P i : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (2 * i) true ++ (markedD (P - i) ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
    ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest))))))))

/-- The exit: THE COMPLETE SIX-REGION MORPH PREFIX. -/
def t6Out (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (jT (P + 2) 1 ++ (jT (P + 2) 0 ++ rest)))))

theorem t6M_H (B P : ℕ) (rest : List Bool) : t6M B P rest = t6H B P 0 rest := rfl

theorem t6H_out (B P : ℕ) (rest : List Bool) : t6H B P P rest = t6Out B P rest := by
  have hj6 : jT (P + 2) 0 = [false, true] ++ List.replicate (2 * P + 4) false := by
    rw [jT, show 2 * (P + 2 - 0) = 2 * P + 4 from by omega]
    rfl
  rw [t6H, t6Out, Nat.sub_self, unaryD_eq P, hj6]
  simp [markedD]

/-- **The exit is the morph's target.** -/
theorem t6Out_morphOut (B P : ℕ) (s : List Bool) :
    t6Out B P (encodeD s)
      = PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph.morphOut B P s := rfl

/-! ## The `getD` suite -/

theorem t6T_getD_T1lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (hi : i < B) :
    (t6T B P jS jW rest).getD (2 * i) false = true := by
  rw [t6T, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_T1FT (B P jS jW : ℕ) (rest : List Bool) :
    (t6T B P jS jW rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true
      ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
      ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t6T, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading the source and beyond. -/
theorem t6T_getD_S (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) :
    (t6T B P jS jW rest).getD (2 * B + 2 + c) false
      = (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
        ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
        ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))))).getD
          c false := by
  rw [t6T, getD_append_left_length' _ _ (unaryD_length B)]

theorem t6T_getD_Smark_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t6T B P jS jW rest).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t6T_getD_S, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jS i h

theorem t6T_getD_Smark_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t6T B P jS jW rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h2 := t6T_getD_S B P jS jW rest (2 * i + 1)
  rw [show 2 * B + 2 + (2 * i + 1) = 2 * B + 2 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jS i h

theorem t6T_getD_Sdata (B P jS jW : ℕ) (rest : List Bool) (c : ℕ)
    (hjS : jS ≤ P) (h1 : 2 * jS ≤ c) (h2 : c < 2 * P) :
    (t6T B P jS jW rest).getD (2 * B + 2 + c) false = true := by
  rw [t6T_getD_S, show c = 2 * jS + (c - 2 * jS) from by omega,
    getD_append_left_length' _ _ (markedD_length jS),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_SFT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h2 := getD_append_left_length' (markedD jS)
    (List.replicate (2 * (P - jS)) true ++ ([false, true]
      ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
      ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))))
    (markedD_length jS) (2 * P - 2 * jS) false
  rw [show 2 * jS + (2 * P - 2 * jS) = 2 * P from by omega] at h2
  have h3 := getD_append_left_length' (List.replicate (2 * (P - jS)) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
      ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))
    List.length_replicate 0 false
  rw [show (2 * P - 2 * jS : ℕ) = 2 * (P - jS) + 0 from by omega] at h2
  rw [t6T_getD_S, h2, h3]
  rfl

/-- Reading `T3` and beyond. -/
theorem t6T_getD_C (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
        ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))).getD
          c false := by
  rw [t6T, show 2 * B + 2 * P + 4 + c
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + c))) from by omega,
    getD_append_left_length' _ _ (unaryD_length B),
    getD_append_left_length' _ _ (markedD_length jS),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t6T_getD_T3lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < P + 1) :
    (t6T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t6T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_T3FT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ (jT (B + 2) 0 ++ (jT (P + 2) 1 ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t6T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

/-- Reading `T4`'s fill and beyond. -/
theorem t6T_getD_D (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (2 * B + 4 * P + 12 + c) false
      = (List.replicate (2 * B + 4) false ++ (jT (P + 2) 1 ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))).getD
          c false := by
  have hjlen : (jT (P + 2) (P + 1)).length = 2 * P + 6 := by
    rw [jT_length (P + 2) (P + 1) (by omega)]
    omega
  have hj4 : jT (B + 2) 0 = [false, true] ++ List.replicate (2 * B + 4) false := by
    rw [jT, show 2 * (B + 2 - 0) = 2 * B + 4 from by omega]
    rfl
  have h := t6T_getD_C B P jS jW rest (2 * P + 6 + (2 + c)) hjS
  rw [show 2 * B + 2 * P + 4 + (2 * P + 6 + (2 + c)) = 2 * B + 4 * P + 12 + c
      from by omega,
    getD_append_left_length' _ _ hjlen, hj4, List.append_assoc,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t6T_getD_fill4_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < B + 2) :
    (t6T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * i) false = false := by
  rw [t6T_getD_D B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_liveLo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 4 * P + 16) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * B + 4) false)
    (jT (P + 2) 1 ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t6T_getD_D B P jS jW rest (2 * B + 4) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4) = 4 * B + 4 * P + 16 from by omega] at h
  rw [h, h2, jT]
  rfl

/-- Reading `T5`'s fill and beyond. -/
theorem t6T_getD_E (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 4 * P + 20 + c) false
      = (List.replicate (2 * P + 2) false ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))).getD c false := by
  have hj5 : jT (P + 2) 1
      = [true, true, false, true] ++ List.replicate (2 * P + 2) false := by
    rw [jT, show 2 * (P + 2 - 1) = 2 * P + 2 from by omega]
    rfl
  have h := t6T_getD_D B P jS jW rest (2 * B + 4 + (4 + c)) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4 + (4 + c)) = 4 * B + 4 * P + 20 + c
      from by omega,
    getD_append_left_length' _ _ List.length_replicate, hj5, List.append_assoc,
    getD_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl)] at h
  exact h

theorem t6T_getD_fill5_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < P + 1) :
    (t6T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * i) false = false := by
  rw [t6T_getD_E B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_fill5_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < P + 1) :
    (t6T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * i + 1) false = false := by
  have h := t6T_getD_E B P jS jW rest (2 * i + 1) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * i + 1) = 4 * B + 4 * P + 20 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_m6_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 22) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * P + 2) false)
    ([false, true] ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t6T_getD_E B P jS jW rest (2 * P + 2) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * P + 2) = 4 * B + 6 * P + 22 from by omega] at h
  rw [h, h2]
  rfl

theorem t6T_getD_m6_hi (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 22 + 1) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * P + 2) false)
    ([false, true] ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))
    List.length_replicate 1 false
  have h := t6T_getD_E B P jS jW rest (2 * P + 2 + 1) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * P + 2 + 1) = 4 * B + 6 * P + 22 + 1
    from by omega] at h
  rw [h, h2]
  rfl

/-- Reading the `T6` fill zone and beyond. -/
theorem t6T_getD_F (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 24 + c) false
      = (List.replicate (2 * jW) false ++ ([false, true] ++ rest)).getD c false := by
  have h := t6T_getD_E B P jS jW rest (2 * P + 2 + (2 + c)) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * P + 2 + (2 + c)) = 4 * B + 6 * P + 24 + c
      from by omega,
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t6T_getD_fill_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 24 + 2 * i) false = false := by
  rw [t6T_getD_F B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_fill_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 24 + 2 * i + 1) false = false := by
  have h := t6T_getD_F B P jS jW rest (2 * i + 1) hjS
  rw [show 4 * B + 6 * P + 24 + (2 * i + 1) = 4 * B + 6 * P + 24 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6T_getD_frontier_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 24 + 2 * jW) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t6T_getD_F B P jS jW rest _ hjS, h2]
  rfl

theorem t6T_getD_frontier_hi (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t6T B P jS jW rest).getD (4 * B + 6 * P + 24 + 2 * jW + 1) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 1 false
  have h := t6T_getD_F B P jS jW rest (2 * jW + 1) hjS
  rw [show 4 * B + 6 * P + 24 + (2 * jW + 1) = 4 * B + 6 * P + 24 + 2 * jW + 1
    from by omega] at h
  rw [h, h2]
  rfl

/-! ## The write lemmas -/

theorem t6T_markSrc (B P jS jW : ℕ) (rest : List Bool) (hjS : jS < P) :
    writeAt (t6T B P jS jW rest) (2 * B + 2 + 2 * jS + 1) false
      = t6T B P (jS + 1) jW rest := by
  rw [writeAt_of_lt false (by
      simp only [t6T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      omega), t6T,
    show 2 * B + 2 + 2 * jS + 1 = 2 * B + 2 + (2 * jS + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    show List.replicate (2 * (P - jS)) true
      = true :: true :: List.replicate (2 * (P - jS - 1)) true from by
        rw [show 2 * (P - jS) = 2 * (P - jS - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t6T, ← markedD_snoc, show P - (jS + 1) = P - jS - 1 from by omega]
  simp [List.append_assoc]

theorem t6T_adv1 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t6T B P jS jW (r0 :: r1 :: rest)) (4 * B + 6 * P + 24 + 2 * jW + 1) false
      = t6A B P jS jW r0 r1 rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ (r0 :: r1 :: rest)) List.length_replicate 1 false
  rw [writeAt_of_lt false (by
      simp only [t6T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      omega), t6T,
    show 4 * B + 6 * P + 24 + 2 * jW + 1
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * P + 6 + (2 * B + 6
        + (2 * P + 6 + (2 + (2 * jW + 1)))))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (P + 2) 1).length = 2 * P + 6 from by
      rw [jT_length (P + 2) 1 (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    hset]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t6A, show (2 * jW + 2 : ℕ) = 2 * jW + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * jW + 1), List.replicate_succ' (n := 2 * jW)]
  simp

theorem t6A_write (B P jS jW k : ℕ) (w u v : Bool) (rest : List Bool)
    (hjS : jS ≤ P) (hk : k < (u :: v :: rest).length) :
    writeAt (t6A B P jS jW u v rest) (4 * B + 6 * P + 24 + 2 * jW + 2 + k) w
      = unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
        ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
        ++ ([false, true]
        ++ (List.replicate (2 * jW + 2) false ++ ((u :: v :: rest).set k w))))))))) := by
  rw [writeAt_of_lt w (by
      simp only [t6A, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      simp only [List.length_cons] at hk
      omega), t6A,
    show 4 * B + 6 * P + 24 + 2 * jW + 2 + k
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * P + 6 + (2 * B + 6
        + (2 * P + 6 + (2 + (2 * jW + 2 + k)))))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (P + 2) 1).length = 2 * P + 6 from by
      rw [jT_length (P + 2) 1 (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ List.length_replicate]

theorem t6T_adv2 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t6A B P jS jW r0 r1 rest) (4 * B + 6 * P + 24 + 2 * jW + 2) false
      = t6A B P jS jW false r1 rest := by
  have h := t6A_write B P jS jW 0 false r0 r1 rest hjS (by simp)
  rw [show 4 * B + 6 * P + 24 + 2 * jW + 2 + 0 = 4 * B + 6 * P + 24 + 2 * jW + 2
      from by omega,
    show ((r0 :: r1 :: rest).set 0 false : List Bool) = false :: r1 :: rest from rfl]
    at h
  rw [h, t6A]

theorem t6A_writeV (B P jS jW : ℕ) (w u v : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t6A B P jS jW u v rest) (4 * B + 6 * P + 24 + 2 * jW + 3) w
      = t6A B P jS jW u w rest := by
  have h := t6A_write B P jS jW 1 w u v rest hjS (by simp)
  rw [show 4 * B + 6 * P + 24 + 2 * jW + 2 + 1 = 4 * B + 6 * P + 24 + 2 * jW + 3
      from by omega,
    show ((u :: v :: rest).set 1 w : List Bool) = u :: w :: rest from rfl] at h
  rw [h, t6A]

theorem t6A_fold (B P jS jW : ℕ) (rest : List Bool) :
    t6A B P jS jW false true rest = t6T B P jS (jW + 1) rest := by
  rw [t6A, t6T, show (2 * (jW + 1) : ℕ) = 2 * jW + 2 from by omega]
  simp

/-- The MODIFIED endgame advance's fold: three zeros complete the fill. -/
theorem t6A_egFold (B P : ℕ) (rest : List Bool) :
    t6A B P P P false false rest = t6M B P rest := by
  rw [t6A, t6M, Nat.sub_self,
    show (2 * P + 4 : ℕ) = 2 * P + 2 + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * P + 2 + 1), List.replicate_succ' (n := 2 * P + 2)]
  simp

theorem t6H_heal (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    writeAt (t6H B P i rest) (2 * B + 2 + 2 * i + 1) true = t6H B P (i + 1) rest := by
  rw [writeAt_of_lt true (by
      simp only [t6H, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      omega), t6H,
    show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t6H, show P - (i + 1) = P - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ### Heal reads -/

theorem t6H_getD_T1lo (B P i : ℕ) (rest : List Bool) (k : ℕ) (hk : k < B) :
    (t6H B P i rest).getD (2 * k) false = true := by
  rw [t6H, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t6H_getD_T1FT (B P i : ℕ) (rest : List Bool) :
    (t6H B P i rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (List.replicate (2 * i) true ++ (markedD (P - i)
      ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0 ++ (jT (P + 2) 1
      ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest)))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t6H, unaryD_eq, List.append_assoc, h]
  rfl

theorem t6H_getD_lo (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t6H B P i rest).getD (2 * B + 2 + 2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (jT (P + 2) 1
      ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t6H, getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t6H_getD_hi (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t6H B P i rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (jT (P + 2) 1
      ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest)))))))
    List.length_replicate 1 false
  rw [t6H, show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t6H_getD_done (B P : ℕ) (rest : List Bool) :
    (t6H B P P rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    (markedD (P - P) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (jT (P + 2) 1
      ++ ([false, true] ++ (List.replicate (2 * P + 4) false ++ rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t6H, getD_append_left_length' _ _ (unaryD_length B), h, Nat.sub_self]
  rfl

/-! ## Seed reads and writes (on the entry shape) -/

theorem t5Out_t6T (B P : ℕ) (t0 t1 : Bool) (TL : List Bool) :
    writeAt (writeAt (t5Out B P (t0 :: t1 :: TL)) (4 * B + 6 * P + 24) false)
        (4 * B + 6 * P + 25) true
      = t6T B P 0 0 TL := by
  have hlen5 : (jT (P + 2) 1).length = 2 * P + 6 := by
    rw [jT_length (P + 2) 1 (by omega)]
    omega
  rw [writeAt_of_lt false (by
      simp only [t5Out, List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      omega), t5Out,
    show 4 * B + 6 * P + 24
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 * B + 6 + (2 * P + 6 + (2 + 0)))))
      from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    set_append_left_length' _ _ hlen5,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  simp only [List.set_cons_zero]
  rw [writeAt_of_lt true (by
      simp only [List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega),
        jT_length (P + 2) 1 (by omega)]
      omega),
    show 4 * B + 6 * P + 25
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 * B + 6 + (2 * P + 6 + (2 + 1)))))
      from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    set_append_left_length' _ _ hlen5,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  simp only [List.set_cons_succ, List.set_cons_zero]
  rw [t6T, Nat.sub_zero]
  simp [unaryD_eq, markedD]

/-! ### Entry-shape reads -/

theorem t5Out_getD_T1lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B) :
    (t5Out B P TL).getD (2 * i) false = true := by
  rw [t5Out, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_T1FT (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (jT (P + 2) 1 ++ ([false, true] ++ TL))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5Out, unaryD_eq B, List.append_assoc, h]
  rfl

theorem t5Out_getD_A (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t5Out B P TL).getD (2 * B + 2 + c) false
      = (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (jT (P + 2) 1 ++ ([false, true] ++ TL))))).getD c false := by
  rw [t5Out, getD_append_left_length' _ _ (unaryD_length B)]

theorem t5Out_getD_T2lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P) :
    (t5Out B P TL).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t5Out_getD_A, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_T2FT (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (jT (P + 2) 1 ++ ([false, true] ++ TL)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5Out_getD_A, unaryD_eq, List.append_assoc, h]
  rfl

theorem t5Out_getD_C (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t5Out B P TL).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (jT (P + 2) 1 ++ ([false, true] ++ TL)))).getD c false := by
  have h := t5Out_getD_A B P TL (2 * P + 2 + c)
  rw [show 2 * B + 2 + (2 * P + 2 + c) = 2 * B + 2 * P + 4 + c from by omega,
    getD_append_left_length' _ _ (unaryD_length P)] at h
  exact h

theorem t5Out_getD_T3lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P + 1) :
    (t5Out B P TL).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t5Out_getD_C, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_T3FT (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ (jT (B + 2) 0 ++ (jT (P + 2) 1 ++ ([false, true] ++ TL))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5Out_getD_C, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

theorem t5Out_getD_D (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t5Out B P TL).getD (2 * B + 4 * P + 12 + c) false
      = (List.replicate (2 * B + 4) false
        ++ (jT (P + 2) 1 ++ ([false, true] ++ TL))).getD c false := by
  have hjlen : (jT (P + 2) (P + 1)).length = 2 * P + 6 := by
    rw [jT_length (P + 2) (P + 1) (by omega)]
    omega
  have hj4 : jT (B + 2) 0 = [false, true] ++ List.replicate (2 * B + 4) false := by
    rw [jT, show 2 * (B + 2 - 0) = 2 * B + 4 from by omega]
    rfl
  have h := t5Out_getD_C B P TL (2 * P + 6 + (2 + c))
  rw [show 2 * B + 2 * P + 4 + (2 * P + 6 + (2 + c)) = 2 * B + 4 * P + 12 + c
      from by omega,
    getD_append_left_length' _ _ hjlen, hj4, List.append_assoc,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t5Out_getD_fill4_lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B + 2) :
    (t5Out B P TL).getD (2 * B + 4 * P + 12 + 2 * i) false = false := by
  rw [t5Out_getD_D, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_liveLo (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (4 * B + 4 * P + 16) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * B + 4) false)
    (jT (P + 2) 1 ++ ([false, true] ++ TL)) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t5Out_getD_D B P TL (2 * B + 4)
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4) = 4 * B + 4 * P + 16 from by omega] at h
  rw [h, h2, jT]
  rfl

theorem t5Out_getD_E (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t5Out B P TL).getD (4 * B + 4 * P + 20 + c) false
      = (List.replicate (2 * P + 2) false ++ ([false, true] ++ TL)).getD c false := by
  have hj5 : jT (P + 2) 1
      = [true, true, false, true] ++ List.replicate (2 * P + 2) false := by
    rw [jT, show 2 * (P + 2 - 1) = 2 * P + 2 from by omega]
    rfl
  have h := t5Out_getD_D B P TL (2 * B + 4 + (4 + c))
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4 + (4 + c)) = 4 * B + 4 * P + 20 + c
      from by omega,
    getD_append_left_length' _ _ List.length_replicate, hj5, List.append_assoc,
    getD_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl)] at h
  exact h

theorem t5Out_getD_fill5_lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P + 1) :
    (t5Out B P TL).getD (4 * B + 4 * P + 20 + 2 * i) false = false := by
  rw [t5Out_getD_E, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_fill5_hi (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P + 1) :
    (t5Out B P TL).getD (4 * B + 4 * P + 20 + 2 * i + 1) false = false := by
  have h := t5Out_getD_E B P TL (2 * i + 1)
  rw [show 4 * B + 4 * P + 20 + (2 * i + 1) = 4 * B + 4 * P + 20 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5Out_getD_m6_lo (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (4 * B + 6 * P + 22) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * P + 2) false)
    ([false, true] ++ TL) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t5Out_getD_E B P TL (2 * P + 2)
  rw [show 4 * B + 4 * P + 20 + (2 * P + 2) = 4 * B + 6 * P + 22 from by omega] at h
  rw [h, h2]
  rfl

theorem t5Out_getD_m6_hi (B P : ℕ) (TL : List Bool) :
    (t5Out B P TL).getD (4 * B + 6 * P + 22 + 1) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * P + 2) false)
    ([false, true] ++ TL) List.length_replicate 1 false
  have h := t5Out_getD_E B P TL (2 * P + 2 + 1)
  rw [show 4 * B + 4 * P + 20 + (2 * P + 2 + 1) = 4 * B + 6 * P + 22 + 1
    from by omega] at h
  rw [h, h2]
  rfl

/-! ## The `T6` machine

Control: `State = Fin 74 × Bool`.  Seed `0-21`, round `22-47`, endgame `48-66` (the
MODIFIED advance: three zeros, no new frontier), heal `67-71`, done `72`, dead `73`. -/

def t6Machine : Machine where
  State := Fin 74 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 72) || decide (s.1 = 73)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, b), none, 1) else ((2, b), none, 1))
    else if s.1 = 1 then ((0, s.2), none, 1)
    else if s.1 = 2 then ((3, s.2), none, 1)
    else if s.1 = 3 then (if b then ((4, b), none, 1) else ((5, b), none, 1))
    else if s.1 = 4 then ((3, s.2), none, 1)
    else if s.1 = 5 then ((6, s.2), none, 1)
    else if s.1 = 6 then (if b then ((7, b), none, 1) else ((8, b), none, 1))
    else if s.1 = 7 then ((6, s.2), none, 1)
    else if s.1 = 8 then ((9, s.2), none, 1)
    else if s.1 = 9 then ((10, s.2), none, 1)
    else if s.1 = 10 then ((11, s.2), none, 1)
    else if s.1 = 11 then ((12, s.2), none, 1)
    else if s.1 = 12 then ((13, s.2), none, 1)
    else if s.1 = 13 then (if b then ((15, b), none, 1) else ((14, b), none, 1))
    else if s.1 = 14 then ((13, s.2), none, 1)
    else if s.1 = 15 then ((16, s.2), none, 1)
    else if s.1 = 16 then ((17, s.2), none, 1)
    else if s.1 = 17 then ((18, s.2), none, 1)
    else if s.1 = 18 then (if b then ((73, b), none, 2) else ((19, b), none, 1))
    else if s.1 = 19 then (if b then ((20, s.2), none, 1) else ((18, s.2), none, 1))
    else if s.1 = 20 then ((21, s.2), some false, 1)
    else if s.1 = 21 then ((22, s.2), some true, 3)
    else if s.1 = 22 then (if b then ((23, b), none, 1) else ((24, b), none, 1))
    else if s.1 = 23 then ((22, s.2), none, 1)
    else if s.1 = 24 then ((25, s.2), none, 1)
    else if s.1 = 25 then (if b then ((26, b), none, 1) else ((48, b), none, 1))
    else if s.1 = 26 then
      (if b then ((27, s.2), some false, 1) else ((25, s.2), none, 1))
    else if s.1 = 27 then (if b then ((28, b), none, 1) else ((29, b), none, 1))
    else if s.1 = 28 then ((27, s.2), none, 1)
    else if s.1 = 29 then ((30, s.2), none, 1)
    else if s.1 = 30 then (if b then ((31, b), none, 1) else ((32, b), none, 1))
    else if s.1 = 31 then ((30, s.2), none, 1)
    else if s.1 = 32 then ((33, s.2), none, 1)
    else if s.1 = 33 then ((34, s.2), none, 1)
    else if s.1 = 34 then ((35, s.2), none, 1)
    else if s.1 = 35 then ((36, s.2), none, 1)
    else if s.1 = 36 then ((37, s.2), none, 1)
    else if s.1 = 37 then (if b then ((39, b), none, 1) else ((38, b), none, 1))
    else if s.1 = 38 then ((37, s.2), none, 1)
    else if s.1 = 39 then ((40, s.2), none, 1)
    else if s.1 = 40 then ((41, s.2), none, 1)
    else if s.1 = 41 then ((42, s.2), none, 1)
    else if s.1 = 42 then (if b then ((73, b), none, 2) else ((43, b), none, 1))
    else if s.1 = 43 then (if b then ((44, s.2), none, 1) else ((42, s.2), none, 1))
    else if s.1 = 44 then (if b then ((73, b), none, 2) else ((45, b), none, 1))
    else if s.1 = 45 then
      (if b then ((46, s.2), some false, 1) else ((44, s.2), none, 1))
    else if s.1 = 46 then ((47, s.2), some false, 1)
    else if s.1 = 47 then ((22, s.2), some true, 3)
    else if s.1 = 48 then ((49, s.2), none, 1)
    else if s.1 = 49 then (if b then ((50, b), none, 1) else ((51, b), none, 1))
    else if s.1 = 50 then ((49, s.2), none, 1)
    else if s.1 = 51 then ((52, s.2), none, 1)
    else if s.1 = 52 then ((53, s.2), none, 1)
    else if s.1 = 53 then ((54, s.2), none, 1)
    else if s.1 = 54 then ((55, s.2), none, 1)
    else if s.1 = 55 then ((56, s.2), none, 1)
    else if s.1 = 56 then (if b then ((58, b), none, 1) else ((57, b), none, 1))
    else if s.1 = 57 then ((56, s.2), none, 1)
    else if s.1 = 58 then ((59, s.2), none, 1)
    else if s.1 = 59 then ((60, s.2), none, 1)
    else if s.1 = 60 then ((61, s.2), none, 1)
    else if s.1 = 61 then (if b then ((73, b), none, 2) else ((62, b), none, 1))
    else if s.1 = 62 then (if b then ((63, s.2), none, 1) else ((61, s.2), none, 1))
    else if s.1 = 63 then (if b then ((73, b), none, 2) else ((64, b), none, 1))
    else if s.1 = 64 then
      (if b then ((65, s.2), some false, 1) else ((63, s.2), none, 1))
    else if s.1 = 65 then ((66, s.2), some false, 1)
    else if s.1 = 66 then ((67, s.2), some false, 3)
    else if s.1 = 67 then (if b then ((68, b), none, 1) else ((69, b), none, 1))
    else if s.1 = 68 then ((67, s.2), none, 1)
    else if s.1 = 69 then ((70, s.2), none, 1)
    else if s.1 = 70 then (if b then ((71, b), none, 1) else ((72, b), none, 2))
    else if s.1 = 71 then
      (if b then ((73, s.2), none, 2) else ((70, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 72)

theorem init_t6 (x : List Bool) : init t6Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem g6_0T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_0F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_1 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_3T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_3F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_5 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_6T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_6F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(6, s), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_7 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(7, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_8 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_9 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(9, s), p, T⟩ = ⟨(10, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_10 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(10, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_11 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(11, s), p, T⟩ = ⟨(12, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_12 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_13T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(13, s), p, T⟩ = ⟨(15, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_13F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(13, s), p, T⟩ = ⟨(14, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_14 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(14, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_15 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(15, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_16 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(16, s), p, T⟩ = ⟨(17, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_17 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(17, s), p, T⟩ = ⟨(18, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_18F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(18, s), p, T⟩ = ⟨(19, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_19T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(19, s), p, T⟩ = ⟨(20, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_19F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(19, s), p, T⟩ = ⟨(18, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_20 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(20, s), p, T⟩ = ⟨(21, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_21 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(21, s), p, T⟩ = ⟨(22, s), 0, writeAt T p true⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_22T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(22, s), p, T⟩ = ⟨(23, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_22F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(22, s), p, T⟩ = ⟨(24, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_23 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(23, s), p, T⟩ = ⟨(22, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_24 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(24, s), p, T⟩ = ⟨(25, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_25T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(25, s), p, T⟩ = ⟨(26, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_25F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(25, s), p, T⟩ = ⟨(48, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_26T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(26, s), p, T⟩ = ⟨(27, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_26F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(26, s), p, T⟩ = ⟨(25, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_27T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(27, s), p, T⟩ = ⟨(28, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_27F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(27, s), p, T⟩ = ⟨(29, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_28 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(28, s), p, T⟩ = ⟨(27, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_29 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(29, s), p, T⟩ = ⟨(30, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_30T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(30, s), p, T⟩ = ⟨(31, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_30F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(30, s), p, T⟩ = ⟨(32, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_31 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(31, s), p, T⟩ = ⟨(30, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_32 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(32, s), p, T⟩ = ⟨(33, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_33 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(33, s), p, T⟩ = ⟨(34, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_34 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(34, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_35 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(35, s), p, T⟩ = ⟨(36, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_36 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(36, s), p, T⟩ = ⟨(37, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_37T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(37, s), p, T⟩ = ⟨(39, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_37F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(37, s), p, T⟩ = ⟨(38, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_38 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(38, s), p, T⟩ = ⟨(37, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_39 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(39, s), p, T⟩ = ⟨(40, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_40 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(40, s), p, T⟩ = ⟨(41, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_41 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(41, s), p, T⟩ = ⟨(42, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_42F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(42, s), p, T⟩ = ⟨(43, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_43T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(43, s), p, T⟩ = ⟨(44, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_43F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(43, s), p, T⟩ = ⟨(42, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_44F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(44, s), p, T⟩ = ⟨(45, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_45T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(45, s), p, T⟩ = ⟨(46, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_45F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(45, s), p, T⟩ = ⟨(44, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_46 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(46, s), p, T⟩ = ⟨(47, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_47 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(47, s), p, T⟩ = ⟨(22, s), 0, writeAt T p true⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_48 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(48, s), p, T⟩ = ⟨(49, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_49T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(49, s), p, T⟩ = ⟨(50, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_49F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(49, s), p, T⟩ = ⟨(51, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_50 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(50, s), p, T⟩ = ⟨(49, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_51 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(51, s), p, T⟩ = ⟨(52, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_52 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(52, s), p, T⟩ = ⟨(53, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_53 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(53, s), p, T⟩ = ⟨(54, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_54 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(54, s), p, T⟩ = ⟨(55, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_55 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(55, s), p, T⟩ = ⟨(56, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_56T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(56, s), p, T⟩ = ⟨(58, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_56F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(56, s), p, T⟩ = ⟨(57, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_57 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(57, s), p, T⟩ = ⟨(56, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_58 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(58, s), p, T⟩ = ⟨(59, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_59 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(59, s), p, T⟩ = ⟨(60, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_60 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(60, s), p, T⟩ = ⟨(61, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_61F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(61, s), p, T⟩ = ⟨(62, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_62T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(62, s), p, T⟩ = ⟨(63, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_62F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(62, s), p, T⟩ = ⟨(61, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_63F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(63, s), p, T⟩ = ⟨(64, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_64T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(64, s), p, T⟩ = ⟨(65, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_64F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(64, s), p, T⟩ = ⟨(63, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_65 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(65, s), p, T⟩ = ⟨(66, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_66 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(66, s), p, T⟩ = ⟨(67, s), 0, writeAt T p false⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_67T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(67, s), p, T⟩ = ⟨(68, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_67F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(67, s), p, T⟩ = ⟨(69, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_68 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(68, s), p, T⟩ = ⟨(67, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_69 {s : Bool} {p : ℕ} {T : List Bool} :
    step t6Machine ⟨(69, s), p, T⟩ = ⟨(70, s), p + 1, T⟩ := by
  simp only [step, t6Machine, moveHead]; rfl

theorem g6_70T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t6Machine ⟨(70, s), p, T⟩ = ⟨(71, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_70F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(70, s), p, T⟩ = ⟨(72, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

theorem g6_71F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t6Machine ⟨(71, s), p, T⟩ = ⟨(70, s), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t6Machine, moveHead, h]

/-! ### Composites -/

theorem d6_seedT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_0T h1, g6_1]

theorem d6_seedX1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_0F h1, g6_2]

theorem d6_seedT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_3T h1, g6_4]

theorem d6_seedX2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_3F h1, g6_5]

theorem d6_seedT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_6T h1, g6_7]

theorem d6_seedX3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(6, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_6F h1, g6_8]

theorem d6_seedHops {s : Bool} {p : ℕ} {T : List Bool} :
    run t6Machine 4 ⟨(9, s), p, T⟩ = ⟨(13, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_9, g6_10, g6_11, g6_12]

theorem d6_seedFill4 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(13, s), p, T⟩ = ⟨(13, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_13F h1, g6_14]

theorem d6_seedLive {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 4 ⟨(13, s), p, T⟩ = ⟨(18, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_13T h1, g6_15, g6_16, g6_17]

theorem d6_seedFill5 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(18, s), p, T⟩ = ⟨(18, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_18F h1, g6_19F h2]

theorem d6_seedM6 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 2 ⟨(18, s), p, T⟩ = ⟨(20, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_18F h1, g6_19T h2]

theorem d6_seedWrites {s : Bool} {p : ℕ} {T : List Bool} :
    run t6Machine 2 ⟨(20, s), p, T⟩
      = ⟨(22, s), 0, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, g6_20, g6_21]

theorem d6_T1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(22, s), p, T⟩ = ⟨(22, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_22T h1, g6_23]

theorem d6_X1r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(22, s), p, T⟩ = ⟨(25, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_22F h1, g6_24]

theorem d6_skipMk {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(25, s), p, T⟩ = ⟨(25, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_25T h1, g6_26F h2]

theorem d6_mark {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 2 ⟨(25, s), p, T⟩ = ⟨(27, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, g6_25T h1, g6_26T h2]

theorem d6_exhaust {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(25, s), p, T⟩ = ⟨(49, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_25F h1, g6_48]

theorem d6_T2r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(27, s), p, T⟩ = ⟨(27, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_27T h1, g6_28]

theorem d6_X2r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(27, s), p, T⟩ = ⟨(30, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_27F h1, g6_29]

theorem d6_T3r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(30, s), p, T⟩ = ⟨(30, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_30T h1, g6_31]

theorem d6_X3r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(30, s), p, T⟩ = ⟨(33, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_30F h1, g6_32]

theorem d6_hopsR {s : Bool} {p : ℕ} {T : List Bool} :
    run t6Machine 4 ⟨(33, s), p, T⟩ = ⟨(37, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_33, g6_34, g6_35, g6_36]

theorem d6_fill4R {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(37, s), p, T⟩ = ⟨(37, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_37F h1, g6_38]

theorem d6_liveR {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 4 ⟨(37, s), p, T⟩ = ⟨(42, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_37T h1, g6_39, g6_40, g6_41]

theorem d6_fill5R {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(42, s), p, T⟩ = ⟨(42, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_42F h1, g6_43F h2]

theorem d6_m6R {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 2 ⟨(42, s), p, T⟩ = ⟨(44, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_42F h1, g6_43T h2]

theorem d6_skipF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(44, s), p, T⟩ = ⟨(44, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_44F h1, g6_45F h2]

theorem d6_adv {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 4 ⟨(44, s), p, T⟩
      = ⟨(22, false), 0,
          writeAt (writeAt (writeAt T (p + 1) false) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_44F h1, g6_45T h2, g6_46,
    g6_47]

theorem d6_T3e {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(49, s), p, T⟩ = ⟨(49, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_49T h1, g6_50]

theorem d6_X3e {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(49, s), p, T⟩ = ⟨(52, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_49F h1, g6_51]

theorem d6_hopsE {s : Bool} {p : ℕ} {T : List Bool} :
    run t6Machine 4 ⟨(52, s), p, T⟩ = ⟨(56, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_52, g6_53, g6_54, g6_55]

theorem d6_fill4E {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(56, s), p, T⟩ = ⟨(56, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_56F h1, g6_57]

theorem d6_liveE {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 4 ⟨(56, s), p, T⟩ = ⟨(61, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_56T h1, g6_58, g6_59, g6_60]

theorem d6_fill5E {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(61, s), p, T⟩ = ⟨(61, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_61F h1, g6_62F h2]

theorem d6_m6E {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 2 ⟨(61, s), p, T⟩ = ⟨(63, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_61F h1, g6_62T h2]

theorem d6_skipFe {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(63, s), p, T⟩ = ⟨(63, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_63F h1, g6_64F h2]

theorem d6_advE {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t6Machine 4 ⟨(63, s), p, T⟩
      = ⟨(67, false), 0,
          writeAt (writeAt (writeAt T (p + 1) false) (p + 2) false) (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, g6_63F h1, g6_64T h2, g6_65,
    g6_66]

theorem d6_T1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t6Machine 2 ⟨(67, s), p, T⟩ = ⟨(67, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_67T h1, g6_68]

theorem d6_X1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t6Machine 2 ⟨(67, s), p, T⟩ = ⟨(70, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, g6_67F h1, g6_69]

theorem d6_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t6Machine 2 ⟨(70, s), p, T⟩ = ⟨(70, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, g6_70T h1, g6_71F h2]

theorem d6_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    run t6Machine 1 ⟨(70, s), p, T⟩ = ⟨(72, false), p, T⟩ := by
  rw [run_succ, run_zero, g6_70F h]

/-! ### Scan run-invariants -/

theorem v6_seedT1 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_seedT1 (h k (by omega))]
    rfl

theorem v6_seedT2 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_seedT2 (h k (by omega))]
    rfl

theorem v6_seedT3 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_seedT3 (h k (by omega))]
    rfl

theorem v6_seedFill4 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t6Machine (2 * k) ⟨(13, s), q, T⟩
      = ⟨(13, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_seedFill4 (h k (by omega))]
    rfl

theorem v6_seedFill5 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(18, s), q, T⟩
      = ⟨(18, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_seedFill5 hk.1 hk.2]
    rfl

theorem v6_T1r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(22, s), q, T⟩
      = ⟨(22, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_T1 (h k (by omega))]
    rfl

theorem v6_skipMk (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(25, s), q, T⟩
      = ⟨(25, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_skipMk hk.1 hk.2]
    rfl

theorem v6_T2r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(27, s), q, T⟩
      = ⟨(27, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_T2r (h k (by omega))]
    rfl

theorem v6_T3r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(30, s), q, T⟩
      = ⟨(30, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_T3r (h k (by omega))]
    rfl

theorem v6_fill4R (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t6Machine (2 * k) ⟨(37, s), q, T⟩
      = ⟨(37, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_fill4R (h k (by omega))]
    rfl

theorem v6_fill5R (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(42, s), q, T⟩
      = ⟨(42, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_fill5R hk.1 hk.2]
    rfl

theorem v6_skipF (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(44, s), q, T⟩
      = ⟨(44, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_skipF hk.1 hk.2]
    rfl

theorem v6_T3e (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(49, s), q, T⟩
      = ⟨(49, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_T3e (h k (by omega))]
    rfl

theorem v6_fill4E (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t6Machine (2 * k) ⟨(56, s), q, T⟩
      = ⟨(56, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_fill4E (h k (by omega))]
    rfl

theorem v6_fill5E (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(61, s), q, T⟩
      = ⟨(61, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_fill5E hk.1 hk.2]
    rfl

theorem v6_skipFe (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t6Machine (2 * k) ⟨(63, s), q, T⟩
      = ⟨(63, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_skipFe hk.1 hk.2]
    rfl

theorem v6_T1h (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t6Machine (2 * k) ⟨(67, s), q, T⟩
      = ⟨(67, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), d6_T1h (h k (by omega))]
    rfl

/-- Heal the source, tape evolving. -/
theorem v6_heal (B P : ℕ) (rest : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P →
    run t6Machine (2 * k) ⟨(70, s), 2 * B + 2 + 2 * i, t6H B P i rest⟩
      = ⟨(70, if k = 0 then s else true), 2 * B + 2 + 2 * (i + k),
          t6H B P (i + k) rest⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      d6_heal (t6H_getD_lo B P i rest (by omega)) (t6H_getD_hi B P i rest (by omega)),
      t6H_heal B P i rest (by omega),
      show 2 * B + 2 + 2 * i + 2 = 2 * B + 2 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The round invariant -/

theorem t6_round (B P j : ℕ) (r0 r1 : Bool) (rest : List Bool) (s : Bool)
    (hj : j < P) :
    run t6Machine (4 * B + 6 * P + 2 * j + 28)
      ⟨(22, s), 0, t6T B P j j (r0 :: r1 :: rest)⟩
      = ⟨(22, false), 0, t6T B P (j + 1) (j + 1) rest⟩ := by
  have st1 := v6_T1r (t6T B P j j (r0 :: r1 :: rest)) 0 B s (fun i hi => by
    simpa using t6T_getD_T1lo B P j j _ i hi)
  simp only [Nat.zero_add] at st1
  have st2 := d6_X1r (s := if B = 0 then s else true) (p := 2 * B)
    (T := t6T B P j j (r0 :: r1 :: rest)) (t6T_getD_T1FT B P j j _)
  have st3 := v6_skipMk (t6T B P j j (r0 :: r1 :: rest)) (2 * B + 2) j false
    (fun i hi => ⟨t6T_getD_Smark_lo B P j j _ i hi, t6T_getD_Smark_hi B P j j _ i hi⟩)
  have h4b : (t6T B P j j (r0 :: r1 :: rest)).getD (2 * B + 2 + 2 * j + 1) false
      = true := by
    have h := t6T_getD_Sdata B P j j (r0 :: r1 :: rest) (2 * j + 1) (by omega)
      (by omega) (by omega)
    rwa [show 2 * B + 2 + (2 * j + 1) = 2 * B + 2 + 2 * j + 1 from by omega] at h
  have st4 := d6_mark (s := if j = 0 then false else true) (p := 2 * B + 2 + 2 * j)
    (T := t6T B P j j (r0 :: r1 :: rest))
    (t6T_getD_Sdata B P j j _ (2 * j) (by omega) (by omega) (by omega)) h4b
  rw [t6T_markSrc B P j j _ hj] at st4
  have st5 := v6_T2r (t6T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 + 2 * j + 2)
    (P - j - 1) true (fun i hi => by
      have h := t6T_getD_Sdata B P (j + 1) j (r0 :: r1 :: rest) (2 * j + 2 + 2 * i)
        (by omega) (by omega) (by omega)
      rwa [show 2 * B + 2 + (2 * j + 2 + 2 * i) = 2 * B + 2 + 2 * j + 2 + 2 * i
        from by omega] at h)
  rw [show 2 * B + 2 + 2 * j + 2 + 2 * (P - j - 1) = 2 * B + 2 + 2 * P from by omega,
    ite_self] at st5
  have st6 := d6_X2r (s := true) (p := 2 * B + 2 + 2 * P)
    (T := t6T B P (j + 1) j (r0 :: r1 :: rest))
    (t6T_getD_SFT B P (j + 1) j _ (by omega))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at st6
  have st7 := v6_T3r (t6T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 * P + 4)
    (P + 1) false (fun i hi => t6T_getD_T3lo B P (j + 1) j _ i (by omega) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at st7
  have h8 := t6T_getD_T3FT B P (j + 1) j (r0 :: r1 :: rest) (by omega)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h8
  have st8 := d6_X3r (s := true) (p := 2 * B + 4 * P + 6)
    (T := t6T B P (j + 1) j (r0 :: r1 :: rest)) h8
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at st8
  have st9 := d6_hopsR (s := false) (p := 2 * B + 4 * P + 8)
    (T := t6T B P (j + 1) j (r0 :: r1 :: rest))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at st9
  have st10 := v6_fill4R (t6T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 4 * P + 12)
    (B + 2) false (fun i hi => t6T_getD_fill4_lo B P (j + 1) j _ i (by omega) hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at st10
  have st11 := d6_liveR (s := false) (p := 4 * B + 4 * P + 16)
    (T := t6T B P (j + 1) j (r0 :: r1 :: rest))
    (t6T_getD_liveLo B P (j + 1) j _ (by omega))
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at st11
  have st12 := v6_fill5R (t6T B P (j + 1) j (r0 :: r1 :: rest)) (4 * B + 4 * P + 20)
    (P + 1) true (fun i hi => ⟨t6T_getD_fill5_lo B P (j + 1) j _ i (by omega) hi,
      t6T_getD_fill5_hi B P (j + 1) j _ i (by omega) hi⟩)
  rw [show 4 * B + 4 * P + 20 + 2 * (P + 1) = 4 * B + 6 * P + 22 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at st12
  have st13 := d6_m6R (s := false) (p := 4 * B + 6 * P + 22)
    (T := t6T B P (j + 1) j (r0 :: r1 :: rest))
    (t6T_getD_m6_lo B P (j + 1) j _ (by omega))
    (t6T_getD_m6_hi B P (j + 1) j _ (by omega))
  rw [show 4 * B + 6 * P + 22 + 2 = 4 * B + 6 * P + 24 from by omega] at st13
  have st14 := v6_skipF (t6T B P (j + 1) j (r0 :: r1 :: rest)) (4 * B + 6 * P + 24) j
    false (fun i hi => ⟨t6T_getD_fill_lo B P (j + 1) j _ i (by omega) hi,
      t6T_getD_fill_hi B P (j + 1) j _ i (by omega) hi⟩)
  have st15 := d6_adv (s := if j = 0 then false else false)
    (p := 4 * B + 6 * P + 24 + 2 * j) (T := t6T B P (j + 1) j (r0 :: r1 :: rest))
    (t6T_getD_frontier_lo B P (j + 1) j _ (by omega))
    (t6T_getD_frontier_hi B P (j + 1) j _ (by omega))
  rw [t6T_adv1 B P (j + 1) j r0 r1 rest (by omega),
    t6T_adv2 B P (j + 1) j r0 r1 rest (by omega),
    t6A_writeV B P (j + 1) j true false r1 rest (by omega),
    t6A_fold B P (j + 1) j rest] at st15
  rw [ite_self] at st14 st15
  rw [show 4 * B + 6 * P + 2 * j + 28
      = 2 * B + (2 + (2 * j + (2 + (2 * (P - j - 1) + (2 + (2 * (P + 1) + (2 + (4
        + (2 * (B + 2) + (4 + (2 * (P + 1) + (2 + (2 * j + 4))))))))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, run_add, st11, run_add,
    st12, run_add, st13, run_add, st14, st15]

/-! ## The rounds, the endgame, the run -/

def t6Rounds (B P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t6Rounds B P k + (4 * B + 6 * P + 2 * k + 28)

theorem t6_rounds (B P : ℕ) (rest : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ P) (hlen : 2 * k ≤ rest.length) :
    run t6Machine (t6Rounds B P k) ⟨(22, s), 0, t6T B P 0 0 rest⟩
      = ⟨(22, if k = 0 then s else false), 0, t6T B P k k (rest.drop (2 * k))⟩ := by
  induction k with
  | zero => simp [t6Rounds]
  | succ k ih =>
    rw [show t6Rounds B P (k + 1) = t6Rounds B P k + (4 * B + 6 * P + 2 * k + 28)
        from rfl,
      run_add, ih (by omega) (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
      t6_round B P k _ _ _ _ (by omega), if_neg (by omega)]

/-- The pass's exact clock. -/
def t6Clock (B P : ℕ) : ℕ :=
  (4 * B + 6 * P + 26)
    + (t6Rounds B P P + ((4 * B + 8 * P + 28) + (2 * B + 2 * P + 3)))

set_option maxHeartbeats 1600000 in
/-- **THE `T6` FILL RUNS — THE MORPH PREFIX COMPLETES.**  From the five-target front and
ANY dead tail of length at least `2P+4`, the pass halts DONE with the COMPLETE
six-region prefix, flush against the remaining tail. -/
theorem t6Machine_run (B P : ℕ) (TAIL : List Bool) (hlen : 2 * P + 4 ≤ TAIL.length) :
    run t6Machine (t6Clock B P) (init t6Machine (t5Out B P TAIL))
      = ⟨(72, false), 2 * B + 2 + 2 * P, t6Out B P (TAIL.drop (2 * P + 4))⟩ := by
  obtain ⟨t0, TAIL1, rfl⟩ : ∃ a l, TAIL = a :: l := by
    cases TAIL with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨t1, TL2, rfl⟩ : ∃ a l, TAIL1 = a :: l := by
    cases TAIL1 with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  have hlen2 : 2 * P + 2 ≤ TL2.length := by
    simp only [List.length_cons] at hlen
    omega
  rw [init_t6]
  -- Seed.
  have sd1 := v6_seedT1 (t5Out B P (t0 :: t1 :: TL2)) 0 B false (fun i hi => by
    simpa using t5Out_getD_T1lo B P _ i hi)
  simp only [Nat.zero_add] at sd1
  have sd2 := d6_seedX1 (s := if B = 0 then false else true) (p := 2 * B)
    (T := t5Out B P (t0 :: t1 :: TL2)) (t5Out_getD_T1FT B P _)
  have sd3 := v6_seedT2 (t5Out B P (t0 :: t1 :: TL2)) (2 * B + 2) P false
    (fun i hi => t5Out_getD_T2lo B P _ i hi)
  have sd4 := d6_seedX2 (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t5Out B P (t0 :: t1 :: TL2)) (t5Out_getD_T2FT B P _)
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at sd4
  have sd5 := v6_seedT3 (t5Out B P (t0 :: t1 :: TL2)) (2 * B + 2 * P + 4) (P + 1)
    false (fun i hi => t5Out_getD_T3lo B P _ i hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at sd5
  have h6 := t5Out_getD_T3FT B P (t0 :: t1 :: TL2)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h6
  have sd6 := d6_seedX3 (s := true) (p := 2 * B + 4 * P + 6)
    (T := t5Out B P (t0 :: t1 :: TL2)) h6
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at sd6
  have sd7 := d6_seedHops (s := false) (p := 2 * B + 4 * P + 8)
    (T := t5Out B P (t0 :: t1 :: TL2))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at sd7
  have sd8 := v6_seedFill4 (t5Out B P (t0 :: t1 :: TL2)) (2 * B + 4 * P + 12) (B + 2)
    false (fun i hi => t5Out_getD_fill4_lo B P _ i hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at sd8
  have sd9 := d6_seedLive (s := false) (p := 4 * B + 4 * P + 16)
    (T := t5Out B P (t0 :: t1 :: TL2)) (t5Out_getD_liveLo B P _)
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at sd9
  have sd10 := v6_seedFill5 (t5Out B P (t0 :: t1 :: TL2)) (4 * B + 4 * P + 20) (P + 1)
    true (fun i hi => ⟨t5Out_getD_fill5_lo B P _ i hi, t5Out_getD_fill5_hi B P _ i hi⟩)
  rw [show 4 * B + 4 * P + 20 + 2 * (P + 1) = 4 * B + 6 * P + 22 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at sd10
  have sd11 := d6_seedM6 (s := false) (p := 4 * B + 6 * P + 22)
    (T := t5Out B P (t0 :: t1 :: TL2)) (t5Out_getD_m6_lo B P _)
    (t5Out_getD_m6_hi B P _)
  rw [show 4 * B + 6 * P + 22 + 2 = 4 * B + 6 * P + 24 from by omega] at sd11
  have sd12 := d6_seedWrites (s := false) (p := 4 * B + 6 * P + 24)
    (T := t5Out B P (t0 :: t1 :: TL2))
  rw [show 4 * B + 6 * P + 24 + 1 = 4 * B + 6 * P + 25 from by omega,
    t5Out_t6T B P t0 t1 TL2] at sd12
  -- Rounds.
  have rr := t6_rounds B P TL2 P false (le_refl _) (by omega)
  rw [ite_self] at rr
  -- Endgame: expose the two consumed tail cells.
  have hlen3 : 2 ≤ (TL2.drop (2 * P)).length := by rw [List.length_drop]; omega
  obtain ⟨c0, R1, h0⟩ : ∃ a l, TL2.drop (2 * P) = a :: l := by
    cases h : TL2.drop (2 * P) with
    | nil => rw [h] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c1, R2, h1⟩ : ∃ a l, R1 = a :: l := by
    cases h : R1 with
    | nil => rw [h] at h0; rw [h0] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  have hchain : TL2.drop (2 * P) = c0 :: c1 :: R2 := by rw [h0, h1]
  have hR2 : R2 = TL2.drop (2 * P + 2) := by
    have h := congrArg (List.drop 2) hchain
    simp only [List.drop_drop] at h
    simpa using h.symm
  rw [hchain] at rr
  have eg1 := v6_T1r (t6T B P P P (c0 :: c1 :: R2)) 0 B false (fun i hi => by
    simpa using t6T_getD_T1lo B P P P _ i hi)
  simp only [Nat.zero_add] at eg1
  have eg2 := d6_X1r (s := if B = 0 then false else true)
    (p := 2 * B) (T := t6T B P P P (c0 :: c1 :: R2)) (t6T_getD_T1FT B P P P _)
  have eg3 := v6_skipMk (t6T B P P P (c0 :: c1 :: R2)) (2 * B + 2) P false
    (fun i hi => ⟨t6T_getD_Smark_lo B P P P _ i hi, t6T_getD_Smark_hi B P P P _ i hi⟩)
  have eg4 := d6_exhaust (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t6T B P P P (c0 :: c1 :: R2)) (t6T_getD_SFT B P P P _ (le_refl _))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at eg4
  have eg5 := v6_T3e (t6T B P P P (c0 :: c1 :: R2)) (2 * B + 2 * P + 4) (P + 1) false
    (fun i hi => t6T_getD_T3lo B P P P _ i (le_refl _) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at eg5
  have h7 := t6T_getD_T3FT B P P P (c0 :: c1 :: R2) (le_refl _)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h7
  have eg6 := d6_X3e (s := true) (p := 2 * B + 4 * P + 6)
    (T := t6T B P P P (c0 :: c1 :: R2)) h7
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at eg6
  have eg7 := d6_hopsE (s := false) (p := 2 * B + 4 * P + 8)
    (T := t6T B P P P (c0 :: c1 :: R2))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at eg7
  have eg8 := v6_fill4E (t6T B P P P (c0 :: c1 :: R2)) (2 * B + 4 * P + 12) (B + 2)
    false (fun i hi => t6T_getD_fill4_lo B P P P _ i (le_refl _) hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at eg8
  have eg9 := d6_liveE (s := false) (p := 4 * B + 4 * P + 16)
    (T := t6T B P P P (c0 :: c1 :: R2)) (t6T_getD_liveLo B P P P _ (le_refl _))
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at eg9
  have eg10 := v6_fill5E (t6T B P P P (c0 :: c1 :: R2)) (4 * B + 4 * P + 20) (P + 1)
    true (fun i hi => ⟨t6T_getD_fill5_lo B P P P _ i (le_refl _) hi,
      t6T_getD_fill5_hi B P P P _ i (le_refl _) hi⟩)
  rw [show 4 * B + 4 * P + 20 + 2 * (P + 1) = 4 * B + 6 * P + 22 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at eg10
  have eg11 := d6_m6E (s := false) (p := 4 * B + 6 * P + 22)
    (T := t6T B P P P (c0 :: c1 :: R2)) (t6T_getD_m6_lo B P P P _ (le_refl _))
    (t6T_getD_m6_hi B P P P _ (le_refl _))
  rw [show 4 * B + 6 * P + 22 + 2 = 4 * B + 6 * P + 24 from by omega] at eg11
  have eg12 := v6_skipFe (t6T B P P P (c0 :: c1 :: R2)) (4 * B + 6 * P + 24) P false
    (fun i hi => ⟨t6T_getD_fill_lo B P P P _ i (le_refl _) hi,
      t6T_getD_fill_hi B P P P _ i (le_refl _) hi⟩)
  have eg13 := d6_advE (s := if P = 0 then false else false)
    (p := 4 * B + 6 * P + 24 + 2 * P) (T := t6T B P P P (c0 :: c1 :: R2))
    (t6T_getD_frontier_lo B P P P _ (le_refl _))
    (t6T_getD_frontier_hi B P P P _ (le_refl _))
  rw [t6T_adv1 B P P P c0 c1 R2 (le_refl _), t6T_adv2 B P P P c0 c1 R2 (le_refl _),
    t6A_writeV B P P P false false c1 R2 (le_refl _), t6A_egFold B P R2,
    t6M_H B P R2] at eg13
  rw [ite_self] at eg12 eg13
  -- Heal.
  have hl1 := v6_T1h (t6H B P 0 R2) 0 B false (fun i hi => by
    simpa using t6H_getD_T1lo B P 0 R2 i hi)
  simp only [Nat.zero_add] at hl1
  have hl2 := d6_X1h (s := if B = 0 then false else true) (p := 2 * B)
    (T := t6H B P 0 R2) (t6H_getD_T1FT B P 0 R2)
  have hl3 := v6_heal B P R2 P 0 false (by omega)
  rw [show 2 * B + 2 + 2 * 0 = 2 * B + 2 from by omega,
    show (0 + P : ℕ) = P from by omega] at hl3
  have hl4 := d6_done (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t6H B P P R2) (t6H_getD_done B P R2)
  -- Assemble.
  rw [show t6Clock B P
      = 2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4 + (2 * (B + 2) + (4
        + (2 * (P + 1) + (2 + (2
        + (t6Rounds B P P + (2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4
        + (2 * (B + 2) + (4 + (2 * (P + 1) + (2 + (2 * P + (4 + (2 * B + (2
        + (2 * P + 1))))))))))))))))))))))))))))
      from by rw [t6Clock]; omega,
    run_add, sd1, run_add, sd2, run_add, sd3, run_add, sd4, run_add, sd5, run_add, sd6,
    run_add, sd7, run_add, sd8, run_add, sd9, run_add, sd10, run_add, sd11, run_add,
    sd12, run_add, rr, run_add, eg1, run_add, eg2, run_add, eg3, run_add, eg4, run_add,
    eg5, run_add, eg6, run_add, eg7, run_add, eg8, run_add, eg9, run_add, eg10,
    run_add, eg11, run_add, eg12, run_add, eg13, run_add, hl1, run_add, hl2, run_add,
    hl3, hl4,
    t6H_out B P R2, hR2,
    show (t0 :: t1 :: TL2).drop (2 * P + 4) = TL2.drop (2 * P + 2) from by
      rw [show 2 * P + 4 = 2 * P + 2 + 1 + 1 from by omega]
      rfl]

/-- The done state halts. -/
theorem t6Machine_halt72 : t6Machine.halt ((72 : Fin 74), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT6
