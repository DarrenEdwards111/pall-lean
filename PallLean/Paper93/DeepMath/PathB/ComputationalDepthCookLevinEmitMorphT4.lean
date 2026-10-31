import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT3

/-!
# Cook–Levin M2 emitter — arming morph brick M7 part 1: THE `T4` FILL'S TAPE ALGEBRA

`T4`'s capacity span (`B+2` zero-pairs behind its already-placed marker) plus `T5`'s
live-`1` pair and marker, by the front-bank fabric: source `T1` — AT THE ORIGIN, the
simplest source yet — drives a moving `01` frontier through zero-fill (`00` pairs
behind, three writes per advance, the erase at the HIGH cell), and the endgame's
seven-cell finale writes the last fill pair, `T5`'s `11`, and `T5`'s marker in one
sweep.  `T3`'s tail `00` and `T4`'s marker sit at FIXED offsets after `T3`'s marker, so
the crossings hop them with four unconditional moves — no reads.  The dead suffix stays
a generic drop-tail.  Part 1: descriptors, entry/exit identifications, the full
read/write suite.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT3

/-! ## The descriptor family -/

/-- Mid-pass: `jS` source pairs marked, `jW` zero-fill advances done. -/
def t4T (B P jS jW : ℕ) (rest : List Bool) : List Bool :=
  markedD jS ++ (List.replicate (2 * (B - jS)) true ++ ([false, true]
    ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
    ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))

/-- Mid-advance: the erased frontier merged into the fill, two raw cells. -/
def t4A (B P jS jW : ℕ) (u v : Bool) (rest : List Bool) : List Bool :=
  markedD jS ++ (List.replicate (2 * (B - jS)) true ++ ([false, true]
    ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
    ++ (List.replicate (2 * jW + 2) false ++ (u :: v :: rest)))))))

/-- Post-finale, pre-heal: `T4` complete, `T5`'s live pair and marker placed. -/
def t4M (B P : ℕ) (rest : List Bool) : List Bool :=
  markedD B ++ ([false, true]
    ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
    ++ (List.replicate (2 * B + 4) false
    ++ (true :: true :: false :: true :: rest))))))

/-- Mid-heal: `i` source marks healed. -/
def t4H (B P i : ℕ) (rest : List Bool) : List Bool :=
  List.replicate (2 * i) true ++ (markedD (B - i) ++ ([false, true]
    ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
    ++ (List.replicate (2 * B + 4) false
    ++ (true :: true :: false :: true :: rest)))))))

/-- The exit: four targets written, `T5`'s live pair and marker placed. -/
def t4Out (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (true :: true :: false :: true :: rest))))

theorem t4M_H (B P : ℕ) (rest : List Bool) : t4M B P rest = t4H B P 0 rest := rfl

theorem t4H_out (B P : ℕ) (rest : List Bool) : t4H B P B rest = t4Out B P rest := by
  have hj4 : jT (B + 2) 0 = [false, true] ++ List.replicate (2 * B + 4) false := by
    rw [jT, show 2 * (B + 2 - 0) = 2 * B + 4 from by omega]
    rfl
  rw [t4H, t4Out, Nat.sub_self, unaryD_eq B, hj4]
  simp [markedD]

/-! ## The `getD` suite -/

theorem t4T_getD_Smark_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t4T B P jS jW rest).getD (2 * i) false = true := by
  rw [t4T, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jS i h

theorem t4T_getD_Smark_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t4T B P jS jW rest).getD (2 * i + 1) false = false := by
  rw [t4T, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jS i h

theorem t4T_getD_Sdata (B P jS jW : ℕ) (rest : List Bool) (c : ℕ)
    (hjS : jS ≤ B) (h1 : 2 * jS ≤ c) (h2 : c < 2 * B) :
    (t4T B P jS jW rest).getD c false = true := by
  rw [t4T, show c = 2 * jS + (c - 2 * jS) from by omega,
    getD_append_left_length' _ _ (markedD_length jS),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4T_getD_SFT_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B) false = false := by
  have h2 := getD_append_left_length' (markedD jS)
    (List.replicate (2 * (B - jS)) true ++ ([false, true]
      ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))
    (markedD_length jS) (2 * B - 2 * jS) false
  rw [show 2 * jS + (2 * B - 2 * jS) = 2 * B from by omega] at h2
  have h3 := getD_append_left_length' (List.replicate (2 * (B - jS)) true)
    ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  rw [show (2 * B - 2 * jS : ℕ) = 2 * (B - jS) + 0 from by omega] at h2
  rw [t4T, h2, h3]
  rfl

/-- Reading `T2` and beyond. -/
theorem t4T_getD_A (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 2 + c) false
      = (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))).getD c false := by
  rw [t4T, show 2 * B + 2 + c = 2 * jS + (2 * (B - jS) + (2 + c)) from by omega,
    getD_append_left_length' _ _ (markedD_length jS),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t4T_getD_T2lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ B) (hi : i < P) :
    (t4T B P jS jW rest).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t4T_getD_A B P jS jW rest _ hjS, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4T_getD_T2FT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ ([false, true]
      ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4T_getD_A B P jS jW rest _ hjS, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading `T3` and beyond. -/
theorem t4T_getD_C (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ ([false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))).getD c false := by
  have h := t4T_getD_A B P jS jW rest (2 * P + 2 + c) hjS
  rw [show 2 * B + 2 + (2 * P + 2 + c) = 2 * B + 2 * P + 4 + c from by omega,
    getD_append_left_length' _ _ (unaryD_length P)] at h
  exact h

theorem t4T_getD_T3lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ B) (hi : i < P + 1) :
    (t4T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t4T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4T_getD_T3FT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ ([false, true] ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

/-- Reading the fill and beyond. -/
theorem t4T_getD_F (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 4 * P + 12 + c) false
      = (List.replicate (2 * jW) false ++ ([false, true] ++ rest)).getD c false := by
  have hjlen : (jT (P + 2) (P + 1)).length = 2 * P + 6 := by
    rw [jT_length (P + 2) (P + 1) (by omega)]
    omega
  have h := t4T_getD_C B P jS jW rest (2 * P + 6 + (2 + c)) hjS
  rw [show 2 * B + 2 * P + 4 + (2 * P + 6 + (2 + c)) = 2 * B + 4 * P + 12 + c
      from by omega,
    getD_append_left_length' _ _ hjlen,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t4T_getD_fill_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ B) (hi : i < jW) :
    (t4T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * i) false = false := by
  rw [t4T_getD_F B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4T_getD_fill_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ B) (hi : i < jW) :
    (t4T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * i + 1) false = false := by
  have h := t4T_getD_F B P jS jW rest (2 * i + 1) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * i + 1) = 2 * B + 4 * P + 12 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4T_getD_frontier_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * jW) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t4T_getD_F B P jS jW rest _ hjS, h2]
  rfl

theorem t4T_getD_frontier_hi (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ B) :
    (t4T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * jW + 1) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 1 false
  have h := t4T_getD_F B P jS jW rest (2 * jW + 1) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * jW + 1) = 2 * B + 4 * P + 12 + 2 * jW + 1
    from by omega] at h
  rw [h, h2]
  rfl

/-! ## The write lemmas -/

/-- Mark the source's next pair (the source is at the origin). -/
theorem t4T_markSrc (B P jS jW : ℕ) (rest : List Bool) (hjS : jS < B) :
    writeAt (t4T B P jS jW rest) (2 * jS + 1) false = t4T B P (jS + 1) jW rest := by
  rw [writeAt_of_lt false (by
      simp only [t4T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      omega), t4T,
    set_append_left_length' _ _ (markedD_length jS),
    show List.replicate (2 * (B - jS)) true
      = true :: true :: List.replicate (2 * (B - jS - 1)) true from by
        rw [show 2 * (B - jS) = 2 * (B - jS - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t4T, ← markedD_snoc, show B - (jS + 1) = B - jS - 1 from by omega]
  simp [List.append_assoc]

/-- Advance, write 1: erase the frontier at its HIGH cell (`01 ↦ 00`). -/
theorem t4T_adv1 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ B) :
    writeAt (t4T B P jS jW (r0 :: r1 :: rest)) (2 * B + 4 * P + 12 + 2 * jW + 1) false
      = t4A B P jS jW r0 r1 rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ (r0 :: r1 :: rest)) List.length_replicate 1 false
  rw [writeAt_of_lt false (by
      simp only [t4T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      omega), t4T,
    show 2 * B + 4 * P + 12 + 2 * jW + 1
      = 2 * jS + (2 * (B - jS) + (2 + (2 * P + 2 + (2 * P + 6
        + (2 + (2 * jW + 1)))))) from by omega,
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    hset]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t4A, show (2 * jW + 2 : ℕ) = 2 * jW + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * jW + 1), List.replicate_succ' (n := 2 * jW)]
  simp

/-- General write into the raw slot past the fill. -/
theorem t4A_write (B P jS jW k : ℕ) (w u v : Bool) (rest : List Bool)
    (hjS : jS ≤ B) (hk : k < (u :: v :: rest).length) :
    writeAt (t4A B P jS jW u v rest) (2 * B + 4 * P + 12 + 2 * jW + 2 + k) w
      = markedD jS ++ (List.replicate (2 * (B - jS)) true ++ ([false, true]
        ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
        ++ (List.replicate (2 * jW + 2) false
        ++ ((u :: v :: rest).set k w))))))) := by
  rw [writeAt_of_lt w (by
      simp only [t4A, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      simp only [List.length_cons] at hk
      omega), t4A,
    show 2 * B + 4 * P + 12 + 2 * jW + 2 + k
      = 2 * jS + (2 * (B - jS) + (2 + (2 * P + 2 + (2 * P + 6
        + (2 + (2 * jW + 2 + k)))))) from by omega,
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ List.length_replicate]

/-- The finale's slot is the pre-heal descriptor. -/
theorem t4A_egM (B P : ℕ) (rest : List Bool) :
    (markedD B ++ (List.replicate (2 * (B - B)) true ++ ([false, true]
      ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true]
      ++ (List.replicate (2 * B + 2) false
      ++ (false :: false :: true :: true :: false :: true :: rest)))))))
      : List Bool)
      = t4M B P rest := by
  rw [t4M, Nat.sub_self,
    show (2 * B + 4 : ℕ) = 2 * B + 2 + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * B + 2 + 1), List.replicate_succ' (n := 2 * B + 2)]
  simp

/-- Heal one source mark. -/
theorem t4H_heal (B P i : ℕ) (rest : List Bool) (hi : i < B) :
    writeAt (t4H B P i rest) (2 * i + 1) true = t4H B P (i + 1) rest := by
  rw [writeAt_of_lt true (by
      simp only [t4H, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      omega), t4H,
    show 2 * i + 1 = 2 * i + 1 from rfl,
    set_append_left_length' _ _ List.length_replicate,
    show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
      rw [show B - i = B - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t4H, show B - (i + 1) = B - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ### Heal reads -/

theorem t4H_getD_lo (B P i : ℕ) (rest : List Bool) (hi : i < B) :
    (t4H B P i rest).getD (2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (B - i) ++ ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1)
      ++ ([false, true] ++ (List.replicate (2 * B + 4) false
      ++ (true :: true :: false :: true :: rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4H, h, show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
    rw [show B - i = B - i - 1 + 1 from by omega]
    rfl]
  rfl

theorem t4H_getD_hi (B P i : ℕ) (rest : List Bool) (hi : i < B) :
    (t4H B P i rest).getD (2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (B - i) ++ ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1)
      ++ ([false, true] ++ (List.replicate (2 * B + 4) false
      ++ (true :: true :: false :: true :: rest)))))))
    List.length_replicate 1 false
  rw [t4H, h, show markedD (B - i) = true :: false :: markedD (B - i - 1) from by
    rw [show B - i = B - i - 1 + 1 from by omega]
    rfl]
  rfl

theorem t4H_getD_done (B P : ℕ) (rest : List Bool) :
    (t4H B P B rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    (markedD (B - B) ++ ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1)
      ++ ([false, true] ++ (List.replicate (2 * B + 4) false
      ++ (true :: true :: false :: true :: rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4H, h, Nat.sub_self]
  rfl

/-! ## Seed reads and writes (on the entry shape) -/

theorem t3Out_getD_T1lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B) :
    (t3Out B P TL).getD (2 * i) false = true := by
  rw [t3Out, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3Out_getD_T1FT (B P : ℕ) (TL : List Bool) :
    (t3Out B P TL).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true] ++ TL))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3Out, unaryD_eq B, List.append_assoc, h]
  rfl

theorem t3Out_getD_A (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t3Out B P TL).getD (2 * B + 2 + c) false
      = (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true] ++ TL))).getD c false := by
  rw [t3Out, getD_append_left_length' _ _ (unaryD_length B)]

theorem t3Out_getD_T2lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P) :
    (t3Out B P TL).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t3Out_getD_A, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3Out_getD_T2FT (B P : ℕ) (TL : List Bool) :
    (t3Out B P TL).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ ([false, true] ++ TL)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3Out_getD_A, unaryD_eq, List.append_assoc, h]
  rfl

theorem t3Out_getD_C (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t3Out B P TL).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ ([false, true] ++ TL)).getD c false := by
  have h := t3Out_getD_A B P TL (2 * P + 2 + c)
  rw [show 2 * B + 2 + (2 * P + 2 + c) = 2 * B + 2 * P + 4 + c from by omega,
    getD_append_left_length' _ _ (unaryD_length P)] at h
  exact h

theorem t3Out_getD_T3lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P + 1) :
    (t3Out B P TL).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t3Out_getD_C, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3Out_getD_T3FT (B P : ℕ) (TL : List Bool) :
    (t3Out B P TL).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ ([false, true] ++ TL))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3Out_getD_C, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

theorem t3Out_seed1 (B P : ℕ) (t0 t1 : Bool) (TL : List Bool) :
    writeAt (t3Out B P (t0 :: t1 :: TL)) (2 * B + 4 * P + 12) false
      = t3Out B P (false :: t1 :: TL) := by
  rw [writeAt_of_lt false (by
      simp only [t3Out, List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      omega), t3Out,
    show 2 * B + 4 * P + 12
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 + 0))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  rw [t3Out]
  rfl

theorem t3Out_seed2 (B P : ℕ) (t1 : Bool) (TL : List Bool) :
    writeAt (t3Out B P (false :: t1 :: TL)) (2 * B + 4 * P + 13) true
      = t4T B P 0 0 TL := by
  rw [writeAt_of_lt true (by
      simp only [t3Out, List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega)]
      omega), t3Out,
    show 2 * B + 4 * P + 13
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 + 1))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  simp only [List.set_cons_succ, List.set_cons_zero]
  rw [t4T, Nat.sub_zero]
  simp [unaryD_eq, markedD]

/-! ## The `T4` machine

Control: `State = Fin 57 × Bool`.  Seed `0-14` (cross `T1`/`T2`/`T3`, four
unconditional hops over `T3`'s tail and `T4`'s marker, plant the frontier, reset),
round `15-33` (mark source pair `j` at the origin, flow right across the four written
regions and the hops, skip the zero-fill by high-cell check, 3-write advance with the
erase at the HIGH cell, reset), endgame `34-52` (source spent: flow right, seven-cell
finale — last fill pair, `T5`'s `11`, `T5`'s marker — reset), heal `53-54`
(origin-local), done `55`, dead `56`. -/

def t4Machine : Machine where
  State := Fin 57 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 55) || decide (s.1 = 56)
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
    else if s.1 = 13 then ((14, s.2), some false, 1)
    else if s.1 = 14 then ((15, s.2), some true, 3)
    else if s.1 = 15 then (if b then ((16, b), none, 1) else ((34, b), none, 1))
    else if s.1 = 16 then
      (if b then ((17, s.2), some false, 1) else ((15, s.2), none, 1))
    else if s.1 = 17 then (if b then ((18, b), none, 1) else ((19, b), none, 1))
    else if s.1 = 18 then ((17, s.2), none, 1)
    else if s.1 = 19 then ((20, s.2), none, 1)
    else if s.1 = 20 then (if b then ((21, b), none, 1) else ((22, b), none, 1))
    else if s.1 = 21 then ((20, s.2), none, 1)
    else if s.1 = 22 then ((23, s.2), none, 1)
    else if s.1 = 23 then (if b then ((24, b), none, 1) else ((25, b), none, 1))
    else if s.1 = 24 then ((23, s.2), none, 1)
    else if s.1 = 25 then ((26, s.2), none, 1)
    else if s.1 = 26 then ((27, s.2), none, 1)
    else if s.1 = 27 then ((28, s.2), none, 1)
    else if s.1 = 28 then ((29, s.2), none, 1)
    else if s.1 = 29 then ((30, s.2), none, 1)
    else if s.1 = 30 then (if b then ((56, b), none, 2) else ((31, b), none, 1))
    else if s.1 = 31 then
      (if b then ((32, s.2), some false, 1) else ((30, s.2), none, 1))
    else if s.1 = 32 then ((33, s.2), some false, 1)
    else if s.1 = 33 then ((15, s.2), some true, 3)
    else if s.1 = 34 then ((35, s.2), none, 1)
    else if s.1 = 35 then (if b then ((36, b), none, 1) else ((37, b), none, 1))
    else if s.1 = 36 then ((35, s.2), none, 1)
    else if s.1 = 37 then ((38, s.2), none, 1)
    else if s.1 = 38 then (if b then ((39, b), none, 1) else ((40, b), none, 1))
    else if s.1 = 39 then ((38, s.2), none, 1)
    else if s.1 = 40 then ((41, s.2), none, 1)
    else if s.1 = 41 then ((42, s.2), none, 1)
    else if s.1 = 42 then ((43, s.2), none, 1)
    else if s.1 = 43 then ((44, s.2), none, 1)
    else if s.1 = 44 then ((45, s.2), none, 1)
    else if s.1 = 45 then (if b then ((56, b), none, 2) else ((46, b), none, 1))
    else if s.1 = 46 then
      (if b then ((47, s.2), some false, 1) else ((45, s.2), none, 1))
    else if s.1 = 47 then ((48, s.2), some false, 1)
    else if s.1 = 48 then ((49, s.2), some false, 1)
    else if s.1 = 49 then ((50, s.2), some true, 1)
    else if s.1 = 50 then ((51, s.2), some true, 1)
    else if s.1 = 51 then ((52, s.2), some false, 1)
    else if s.1 = 52 then ((53, s.2), some true, 3)
    else if s.1 = 53 then (if b then ((54, b), none, 1) else ((55, b), none, 2))
    else if s.1 = 54 then
      (if b then ((56, s.2), none, 2) else ((53, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 55)

theorem init_t4 (x : List Bool) : init t4Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem q4_0T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_0F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_1 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_3T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_3F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_5 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_6T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_6F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(6, s), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_7 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(7, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_8 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_9 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(9, s), p, T⟩ = ⟨(10, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_10 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(10, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_11 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(11, s), p, T⟩ = ⟨(12, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_12 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_13 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(13, s), p, T⟩ = ⟨(14, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_14 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(14, s), p, T⟩ = ⟨(15, s), 0, writeAt T p true⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_15T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(15, s), p, T⟩ = ⟨(16, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_15F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(15, s), p, T⟩ = ⟨(34, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_16T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(16, s), p, T⟩ = ⟨(17, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_16F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(16, s), p, T⟩ = ⟨(15, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_17T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(17, s), p, T⟩ = ⟨(18, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_17F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(17, s), p, T⟩ = ⟨(19, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_18 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(18, s), p, T⟩ = ⟨(17, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_19 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(19, s), p, T⟩ = ⟨(20, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_20T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(20, s), p, T⟩ = ⟨(21, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_20F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(20, s), p, T⟩ = ⟨(22, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_21 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(21, s), p, T⟩ = ⟨(20, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_22 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(22, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_23T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(23, s), p, T⟩ = ⟨(24, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_23F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(23, s), p, T⟩ = ⟨(25, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_24 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(24, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_25 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(25, s), p, T⟩ = ⟨(26, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_26 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(26, s), p, T⟩ = ⟨(27, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_27 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(27, s), p, T⟩ = ⟨(28, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_28 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(28, s), p, T⟩ = ⟨(29, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_29 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(29, s), p, T⟩ = ⟨(30, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_30F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(30, s), p, T⟩ = ⟨(31, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_31T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(31, s), p, T⟩ = ⟨(32, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_31F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(31, s), p, T⟩ = ⟨(30, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_32 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(32, s), p, T⟩ = ⟨(33, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_33 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(33, s), p, T⟩ = ⟨(15, s), 0, writeAt T p true⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_34 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(34, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_35T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(35, s), p, T⟩ = ⟨(36, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_35F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(35, s), p, T⟩ = ⟨(37, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_36 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(36, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_37 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(37, s), p, T⟩ = ⟨(38, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_38T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(38, s), p, T⟩ = ⟨(39, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_38F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(38, s), p, T⟩ = ⟨(40, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_39 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(39, s), p, T⟩ = ⟨(38, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_40 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(40, s), p, T⟩ = ⟨(41, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_41 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(41, s), p, T⟩ = ⟨(42, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_42 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(42, s), p, T⟩ = ⟨(43, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_43 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(43, s), p, T⟩ = ⟨(44, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_44 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(44, s), p, T⟩ = ⟨(45, s), p + 1, T⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_45F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(45, s), p, T⟩ = ⟨(46, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_46T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(46, s), p, T⟩ = ⟨(47, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_46F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(46, s), p, T⟩ = ⟨(45, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_47 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(47, s), p, T⟩ = ⟨(48, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_48 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(48, s), p, T⟩ = ⟨(49, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_49 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(49, s), p, T⟩ = ⟨(50, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_50 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(50, s), p, T⟩ = ⟨(51, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_51 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(51, s), p, T⟩ = ⟨(52, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_52 {s : Bool} {p : ℕ} {T : List Bool} :
    step t4Machine ⟨(52, s), p, T⟩ = ⟨(53, s), 0, writeAt T p true⟩ := by
  simp only [step, t4Machine, moveHead]; rfl

theorem q4_53T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t4Machine ⟨(53, s), p, T⟩ = ⟨(54, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_53F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(53, s), p, T⟩ = ⟨(55, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

theorem q4_54F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t4Machine ⟨(54, s), p, T⟩ = ⟨(53, s), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t4Machine, moveHead, h]

/-! ### Composites -/

theorem r4_seedT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_0T h1, q4_1]

theorem r4_seedX1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_0F h1, q4_2]

theorem r4_seedT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_3T h1, q4_4]

theorem r4_seedX2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_3F h1, q4_5]

theorem r4_seedT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_6T h1, q4_7]

theorem r4_seedX3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(6, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_6F h1, q4_8]

theorem r4_seedHops {s : Bool} {p : ℕ} {T : List Bool} :
    run t4Machine 4 ⟨(9, s), p, T⟩ = ⟨(13, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, q4_9, q4_10, q4_11, q4_12]

theorem r4_seedWrites {s : Bool} {p : ℕ} {T : List Bool} :
    run t4Machine 2 ⟨(13, s), p, T⟩
      = ⟨(15, s), 0, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, q4_13, q4_14]

theorem r4_skipMark {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t4Machine 2 ⟨(15, s), p, T⟩ = ⟨(15, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_15T h1, q4_16F h2]

theorem r4_mark {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t4Machine 2 ⟨(15, s), p, T⟩ = ⟨(17, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, q4_15T h1, q4_16T h2]

theorem r4_exhaust {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(15, s), p, T⟩ = ⟨(35, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_15F h1, q4_34]

theorem r4_skipT1r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(17, s), p, T⟩ = ⟨(17, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_17T h1, q4_18]

theorem r4_crossT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(17, s), p, T⟩ = ⟨(20, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_17F h1, q4_19]

theorem r4_skipT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(20, s), p, T⟩ = ⟨(20, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_20T h1, q4_21]

theorem r4_crossT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(20, s), p, T⟩ = ⟨(23, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_20F h1, q4_22]

theorem r4_skipT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(23, s), p, T⟩ = ⟨(23, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_23T h1, q4_24]

theorem r4_crossT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(23, s), p, T⟩ = ⟨(26, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_23F h1, q4_25]

theorem r4_hops {s : Bool} {p : ℕ} {T : List Bool} :
    run t4Machine 4 ⟨(26, s), p, T⟩ = ⟨(30, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, q4_26, q4_27, q4_28, q4_29]

theorem r4_skipFill {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t4Machine 2 ⟨(30, s), p, T⟩ = ⟨(30, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_30F h1, q4_31F h2]

theorem r4_advance {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t4Machine 4 ⟨(30, s), p, T⟩
      = ⟨(15, false), 0,
          writeAt (writeAt (writeAt T (p + 1) false) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, q4_30F h1, q4_31T h2, q4_32,
    q4_33]

theorem e4_skipT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(35, s), p, T⟩ = ⟨(35, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_35T h1, q4_36]

theorem e4_crossT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(35, s), p, T⟩ = ⟨(38, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_35F h1, q4_37]

theorem e4_skipT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t4Machine 2 ⟨(38, s), p, T⟩ = ⟨(38, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_38T h1, q4_39]

theorem e4_crossT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t4Machine 2 ⟨(38, s), p, T⟩ = ⟨(41, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_38F h1, q4_40]

theorem e4_hops {s : Bool} {p : ℕ} {T : List Bool} :
    run t4Machine 4 ⟨(41, s), p, T⟩ = ⟨(45, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, q4_41, q4_42, q4_43, q4_44]

theorem e4_skipFill {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t4Machine 2 ⟨(45, s), p, T⟩ = ⟨(45, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, q4_45F h1, q4_46F h2]

theorem e4_finale {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t4Machine 8 ⟨(45, s), p, T⟩
      = ⟨(53, false), 0,
          writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt T
            (p + 1) false) (p + 2) false) (p + 3) false) (p + 4) true) (p + 5) true)
            (p + 6) false) (p + 7) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ,
    run_zero, q4_45F h1, q4_46T h2, q4_47, q4_48, q4_49, q4_50, q4_51, q4_52]

theorem h4_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t4Machine 2 ⟨(53, s), p, T⟩ = ⟨(53, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, q4_53T h1, q4_54F h2]

theorem h4_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    run t4Machine 1 ⟨(53, s), p, T⟩ = ⟨(55, false), p, T⟩ := by
  rw [run_succ, run_zero, q4_53F h]

/-! ### Scan run-invariants -/

theorem w4_seedT1 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_seedT1 (h k (by omega))]
    rfl

theorem w4_seedT2 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_seedT2 (h k (by omega))]
    rfl

theorem w4_seedT3 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_seedT3 (h k (by omega))]
    rfl

theorem w4_skipMarks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t4Machine (2 * k) ⟨(15, s), q, T⟩
      = ⟨(15, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_skipMark hk.1 hk.2]
    rfl

theorem w4_skipT1r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(17, s), q, T⟩
      = ⟨(17, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_skipT1r (h k (by omega))]
    rfl

theorem w4_skipT2 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_skipT2 (h k (by omega))]
    rfl

theorem w4_skipT3 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(23, s), q, T⟩
      = ⟨(23, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_skipT3 (h k (by omega))]
    rfl

theorem w4_skipFill (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t4Machine (2 * k) ⟨(30, s), q, T⟩
      = ⟨(30, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), r4_skipFill hk.1 hk.2]
    rfl

theorem w4_skipT2e (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(35, s), q, T⟩
      = ⟨(35, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), e4_skipT2 (h k (by omega))]
    rfl

theorem w4_skipT3e (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t4Machine (2 * k) ⟨(38, s), q, T⟩
      = ⟨(38, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), e4_skipT3 (h k (by omega))]
    rfl

theorem w4_skipFille (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t4Machine (2 * k) ⟨(45, s), q, T⟩
      = ⟨(45, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), e4_skipFill hk.1 hk.2]
    rfl

/-- Heal the source, tape evolving. -/
theorem w4_heal (B P : ℕ) (rest : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ B →
    run t4Machine (2 * k) ⟨(53, s), 2 * i, t4H B P i rest⟩
      = ⟨(53, if k = 0 then s else true), 2 * (i + k), t4H B P (i + k) rest⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      h4_heal (t4H_getD_lo B P i rest (by omega)) (t4H_getD_hi B P i rest (by omega)),
      t4H_heal B P i rest (by omega),
      show 2 * i + 2 = 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ### Advance corollaries -/

theorem t4T_adv2 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ B) :
    writeAt (t4A B P jS jW r0 r1 rest) (2 * B + 4 * P + 12 + 2 * jW + 2) false
      = t4A B P jS jW false r1 rest := by
  have h := t4A_write B P jS jW 0 false r0 r1 rest hjS (by simp)
  rw [show 2 * B + 4 * P + 12 + 2 * jW + 2 + 0 = 2 * B + 4 * P + 12 + 2 * jW + 2
      from by omega,
    show ((r0 :: r1 :: rest).set 0 false : List Bool) = false :: r1 :: rest from rfl]
    at h
  rw [h, t4A]

theorem t4A_writeV (B P jS jW : ℕ) (w u v : Bool) (rest : List Bool) (hjS : jS ≤ B) :
    writeAt (t4A B P jS jW u v rest) (2 * B + 4 * P + 12 + 2 * jW + 3) w
      = t4A B P jS jW u w rest := by
  have h := t4A_write B P jS jW 1 w u v rest hjS (by simp)
  rw [show 2 * B + 4 * P + 12 + 2 * jW + 2 + 1 = 2 * B + 4 * P + 12 + 2 * jW + 3
      from by omega,
    show ((u :: v :: rest).set 1 w : List Bool) = u :: w :: rest from rfl] at h
  rw [h, t4A]

theorem t4A_writeRest (B P jS jW k : ℕ) (w u v : Bool) (rest : List Bool)
    (hjS : jS ≤ B) (hk : k < rest.length) :
    writeAt (t4A B P jS jW u v rest) (2 * B + 4 * P + 12 + 2 * jW + 4 + k) w
      = t4A B P jS jW u v (rest.set k w) := by
  have h := t4A_write B P jS jW (2 + k) w u v rest hjS (by simp; omega)
  rw [show 2 * B + 4 * P + 12 + 2 * jW + 2 + (2 + k)
      = 2 * B + 4 * P + 12 + 2 * jW + 4 + k from by omega,
    show ((u :: v :: rest).set (2 + k) w : List Bool) = u :: v :: rest.set k w
      from by rw [show (2 + k : ℕ) = k + 1 + 1 from by omega]; rfl] at h
  rw [h, t4A]

/-- The completed advance folds back to the mid-pass descriptor. -/
theorem t4A_fold (B P jS jW : ℕ) (rest : List Bool) :
    t4A B P jS jW false true rest = t4T B P jS (jW + 1) rest := by
  rw [t4A, t4T, show (2 * (jW + 1) : ℕ) = 2 * jW + 2 from by omega]
  simp

/-- The finale's slot folds to the pre-heal descriptor. -/
theorem t4A_egM' (B P : ℕ) (rest : List Bool) :
    t4A B P B B false false (true :: true :: false :: true :: rest)
      = t4M B P rest := by
  rw [t4A, t4M, Nat.sub_self,
    show (2 * B + 4 : ℕ) = 2 * B + 2 + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * B + 2 + 1), List.replicate_succ' (n := 2 * B + 2)]
  simp

/-! ## The round invariant -/

/-- **One fill round**: mark source pair `j` at the origin, advance the zero-fill. -/
theorem t4_round (B P j : ℕ) (r0 r1 : Bool) (rest : List Bool) (s : Bool)
    (hj : j < B) :
    run t4Machine (2 * B + 4 * P + 2 * j + 16)
      ⟨(15, s), 0, t4T B P j j (r0 :: r1 :: rest)⟩
      = ⟨(15, false), 0, t4T B P (j + 1) (j + 1) rest⟩ := by
  have st1 := w4_skipMarks (t4T B P j j (r0 :: r1 :: rest)) 0 j s (fun i hi => by
    constructor
    · simpa using t4T_getD_Smark_lo B P j j _ i hi
    · simpa using t4T_getD_Smark_hi B P j j _ i hi)
  simp only [Nat.zero_add] at st1
  have h2b : (t4T B P j j (r0 :: r1 :: rest)).getD (2 * j + 1) false = true :=
    t4T_getD_Sdata B P j j _ (2 * j + 1) (by omega) (by omega) (by omega)
  have st2 := r4_mark (s := if j = 0 then s else true) (p := 2 * j)
    (T := t4T B P j j (r0 :: r1 :: rest))
    (t4T_getD_Sdata B P j j _ (2 * j) (by omega) (by omega) (by omega)) h2b
  rw [t4T_markSrc B P j j _ hj] at st2
  have st3 := w4_skipT1r (t4T B P (j + 1) j (r0 :: r1 :: rest)) (2 * j + 2)
    (B - j - 1) true (fun i hi => by
      have h := t4T_getD_Sdata B P (j + 1) j (r0 :: r1 :: rest) (2 * j + 2 + 2 * i)
        (by omega) (by omega) (by omega)
      rwa [show (2 * j + 2 + 2 * i : ℕ) = 2 * j + 2 + 2 * i from rfl] at h)
  rw [show 2 * j + 2 + 2 * (B - j - 1) = 2 * B from by omega, ite_self] at st3
  have st4 := r4_crossT1 (s := true) (p := 2 * B)
    (T := t4T B P (j + 1) j (r0 :: r1 :: rest))
    (t4T_getD_SFT_lo B P (j + 1) j _ (by omega))
  have st5 := w4_skipT2 (t4T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2) P false
    (fun i hi => t4T_getD_T2lo B P (j + 1) j _ i (by omega) hi)
  have st6 := r4_crossT2 (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t4T B P (j + 1) j (r0 :: r1 :: rest))
    (t4T_getD_T2FT B P (j + 1) j _ (by omega))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at st6
  have st7 := w4_skipT3 (t4T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 * P + 4)
    (P + 1) false (fun i hi => t4T_getD_T3lo B P (j + 1) j _ i (by omega) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at st7
  have h8 := t4T_getD_T3FT B P (j + 1) j (r0 :: r1 :: rest) (by omega)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h8
  have st8 := r4_crossT3 (s := true) (p := 2 * B + 4 * P + 6)
    (T := t4T B P (j + 1) j (r0 :: r1 :: rest)) h8
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at st8
  have st9 := r4_hops (s := false) (p := 2 * B + 4 * P + 8)
    (T := t4T B P (j + 1) j (r0 :: r1 :: rest))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at st9
  have st10 := w4_skipFill (t4T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 4 * P + 12)
    j false (fun i hi => ⟨t4T_getD_fill_lo B P (j + 1) j _ i (by omega) hi,
      t4T_getD_fill_hi B P (j + 1) j _ i (by omega) hi⟩)
  rw [ite_self] at st10
  have st11 := r4_advance (s := false) (p := 2 * B + 4 * P + 12 + 2 * j)
    (T := t4T B P (j + 1) j (r0 :: r1 :: rest))
    (t4T_getD_frontier_lo B P (j + 1) j _ (by omega))
    (t4T_getD_frontier_hi B P (j + 1) j _ (by omega))
  rw [t4T_adv1 B P (j + 1) j r0 r1 rest (by omega),
    t4T_adv2 B P (j + 1) j r0 r1 rest (by omega),
    t4A_writeV B P (j + 1) j true false r1 rest (by omega),
    t4A_fold B P (j + 1) j rest] at st11
  rw [show 2 * B + 4 * P + 2 * j + 16
      = 2 * j + (2 + (2 * (B - j - 1) + (2 + (2 * P + (2 + (2 * (P + 1)
        + (2 + (4 + (2 * j + 4))))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, st11]

/-! ## The rounds, the endgame, the run -/

/-- The cumulative clock of the first `k` rounds. -/
def t4Rounds (B P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t4Rounds B P k + (2 * B + 4 * P + 2 * k + 16)

theorem t4_rounds (B P : ℕ) (rest : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ B) (hlen : 2 * k ≤ rest.length) :
    run t4Machine (t4Rounds B P k) ⟨(15, s), 0, t4T B P 0 0 rest⟩
      = ⟨(15, if k = 0 then s else false), 0, t4T B P k k (rest.drop (2 * k))⟩ := by
  induction k with
  | zero => simp [t4Rounds]
  | succ k ih =>
    rw [show t4Rounds B P (k + 1) = t4Rounds B P k + (2 * B + 4 * P + 2 * k + 16)
        from rfl,
      run_add, ih (by omega) (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
      t4_round B P k _ _ _ _ (by omega), if_neg (by omega)]

/-- The pass's exact clock. -/
def t4Clock (B P : ℕ) : ℕ :=
  (2 * B + 4 * P + 14)
    + (t4Rounds B P B + ((4 * B + 4 * P + 20) + (2 * B + 1)))

set_option maxHeartbeats 1600000 in
/-- **THE `T4` FILL RUNS**: from the three-target front and ANY dead tail of length at
least `2B+8`, the pass halts DONE with `T4` complete and `T5`'s live pair and marker
placed — consuming exactly `2B+8` tail cells. -/
theorem t4Machine_run (B P : ℕ) (TAIL : List Bool) (hlen : 2 * B + 8 ≤ TAIL.length) :
    run t4Machine (t4Clock B P) (init t4Machine (t3Out B P TAIL))
      = ⟨(55, false), 2 * B, t4Out B P (TAIL.drop (2 * B + 8))⟩ := by
  obtain ⟨t0, TAIL1, rfl⟩ : ∃ a l, TAIL = a :: l := by
    cases TAIL with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨t1, TL2, rfl⟩ : ∃ a l, TAIL1 = a :: l := by
    cases TAIL1 with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  have hlen2 : 2 * B + 6 ≤ TL2.length := by
    simp only [List.length_cons] at hlen
    omega
  rw [init_t4]
  -- Seed.
  have sd1 := w4_seedT1 (t3Out B P (t0 :: t1 :: TL2)) 0 B false (fun i hi => by
    simpa using t3Out_getD_T1lo B P _ i hi)
  simp only [Nat.zero_add] at sd1
  have sd2 := r4_seedX1 (s := if B = 0 then false else true) (p := 2 * B)
    (T := t3Out B P (t0 :: t1 :: TL2)) (t3Out_getD_T1FT B P _)
  have sd3 := w4_seedT2 (t3Out B P (t0 :: t1 :: TL2)) (2 * B + 2) P false
    (fun i hi => t3Out_getD_T2lo B P _ i hi)
  have sd4 := r4_seedX2 (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t3Out B P (t0 :: t1 :: TL2)) (t3Out_getD_T2FT B P _)
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at sd4
  have sd5 := w4_seedT3 (t3Out B P (t0 :: t1 :: TL2)) (2 * B + 2 * P + 4) (P + 1)
    false (fun i hi => t3Out_getD_T3lo B P _ i hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at sd5
  have h6 := t3Out_getD_T3FT B P (t0 :: t1 :: TL2)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h6
  have sd6 := r4_seedX3 (s := true) (p := 2 * B + 4 * P + 6)
    (T := t3Out B P (t0 :: t1 :: TL2)) h6
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at sd6
  have sd7 := r4_seedHops (s := false) (p := 2 * B + 4 * P + 8)
    (T := t3Out B P (t0 :: t1 :: TL2))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at sd7
  have sd8 := r4_seedWrites (s := false) (p := 2 * B + 4 * P + 12)
    (T := t3Out B P (t0 :: t1 :: TL2))
  rw [t3Out_seed1 B P t0 t1 TL2,
    show 2 * B + 4 * P + 12 + 1 = 2 * B + 4 * P + 13 from by omega,
    t3Out_seed2 B P t1 TL2] at sd8
  -- Rounds.
  have rr := t4_rounds B P TL2 B false (le_refl _) (by omega)
  rw [ite_self] at rr
  -- Endgame: expose the six consumed tail cells.
  have hlen3 : 6 ≤ (TL2.drop (2 * B)).length := by rw [List.length_drop]; omega
  obtain ⟨c0, R1, h0⟩ : ∃ a l, TL2.drop (2 * B) = a :: l := by
    cases h : TL2.drop (2 * B) with
    | nil => rw [h] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c1, R2, h1⟩ : ∃ a l, R1 = a :: l := by
    cases h : R1 with
    | nil => rw [h] at h0; rw [h0] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c2, R3, h2⟩ : ∃ a l, R2 = a :: l := by
    cases h : R2 with
    | nil => rw [h] at h1; rw [h1] at h0; rw [h0] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c3, R4, h3⟩ : ∃ a l, R3 = a :: l := by
    cases h : R3 with
    | nil => rw [h] at h2; rw [h2] at h1; rw [h1] at h0; rw [h0] at hlen3
             simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c4, R5, h4⟩ : ∃ a l, R4 = a :: l := by
    cases h : R4 with
    | nil => rw [h] at h3; rw [h3] at h2; rw [h2] at h1; rw [h1] at h0
             rw [h0] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨c5, R6, h5⟩ : ∃ a l, R5 = a :: l := by
    cases h : R5 with
    | nil => rw [h] at h4; rw [h4] at h3; rw [h3] at h2; rw [h2] at h1; rw [h1] at h0
             rw [h0] at hlen3; simp at hlen3
    | cons a l => exact ⟨a, l, rfl⟩
  have hchain : TL2.drop (2 * B) = c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6 := by
    rw [h0, h1, h2, h3, h4, h5]
  have hR6 : R6 = TL2.drop (2 * B + 6) := by
    have h := congrArg (List.drop 6) hchain
    simp only [List.drop_drop] at h
    simpa using h.symm
  rw [hchain] at rr
  have eg1 := w4_skipMarks (t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6)) 0 B
    false (fun i hi => by
      constructor
      · simpa using t4T_getD_Smark_lo B P B B _ i hi
      · simpa using t4T_getD_Smark_hi B P B B _ i hi)
  simp only [Nat.zero_add] at eg1
  have hex := t4T_getD_SFT_lo B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6)
    (le_refl _)
  have eg2 := r4_exhaust (s := if B = 0 then false else true) (p := 2 * B)
    (T := t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6)) hex
  have eg3 := w4_skipT2e (t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (2 * B + 2) P false (fun i hi => t4T_getD_T2lo B P B B _ i (le_refl _) hi)
  have eg4 := e4_crossT2 (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (t4T_getD_T2FT B P B B _ (le_refl _))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at eg4
  have eg5 := w4_skipT3e (t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (2 * B + 2 * P + 4) (P + 1) false
    (fun i hi => t4T_getD_T3lo B P B B _ i (le_refl _) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at eg5
  have h7 := t4T_getD_T3FT B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6) (le_refl _)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h7
  have eg6 := e4_crossT3 (s := true) (p := 2 * B + 4 * P + 6)
    (T := t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6)) h7
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at eg6
  have eg7 := e4_hops (s := false) (p := 2 * B + 4 * P + 8)
    (T := t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at eg7
  have eg8 := w4_skipFille (t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (2 * B + 4 * P + 12) B false
    (fun i hi => ⟨t4T_getD_fill_lo B P B B _ i (le_refl _) hi,
      t4T_getD_fill_hi B P B B _ i (le_refl _) hi⟩)
  rw [ite_self] at eg8
  have eg9 := e4_finale (s := false) (p := 2 * B + 4 * P + 12 + 2 * B)
    (T := t4T B P B B (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (t4T_getD_frontier_lo B P B B _ (le_refl _))
    (t4T_getD_frontier_hi B P B B _ (le_refl _))
  rw [t4T_adv1 B P B B c0 c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    t4T_adv2 B P B B c0 c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    t4A_writeV B P B B false false c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    show 2 * B + 4 * P + 12 + 2 * B + 4 = 2 * B + 4 * P + 12 + 2 * B + 4 + 0
      from by omega,
    t4A_writeRest B P B B 0 true false false (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _)
      (by simp),
    show ((c2 :: c3 :: c4 :: c5 :: R6).set 0 true : List Bool)
      = true :: c3 :: c4 :: c5 :: R6 from rfl,
    show 2 * B + 4 * P + 12 + 2 * B + 5 = 2 * B + 4 * P + 12 + 2 * B + 4 + 1
      from by omega,
    t4A_writeRest B P B B 1 true false false (true :: c3 :: c4 :: c5 :: R6) (le_refl _)
      (by simp),
    show ((true :: c3 :: c4 :: c5 :: R6).set 1 true : List Bool)
      = true :: true :: c4 :: c5 :: R6 from rfl,
    show 2 * B + 4 * P + 12 + 2 * B + 6 = 2 * B + 4 * P + 12 + 2 * B + 4 + 2
      from by omega,
    t4A_writeRest B P B B 2 false false false (true :: true :: c4 :: c5 :: R6)
      (le_refl _) (by simp),
    show ((true :: true :: c4 :: c5 :: R6).set 2 false : List Bool)
      = true :: true :: false :: c5 :: R6 from rfl,
    show 2 * B + 4 * P + 12 + 2 * B + 7 = 2 * B + 4 * P + 12 + 2 * B + 4 + 3
      from by omega,
    t4A_writeRest B P B B 3 true false false (true :: true :: false :: c5 :: R6)
      (le_refl _) (by simp),
    show ((true :: true :: false :: c5 :: R6).set 3 true : List Bool)
      = true :: true :: false :: true :: R6 from rfl,
    t4A_egM' B P R6, t4M_H B P R6] at eg9
  -- Heal.
  have hl1 := w4_heal B P R6 B 0 false (by omega)
  rw [show (2 * 0 : ℕ) = 0 from by omega, show (0 + B : ℕ) = B from by omega] at hl1
  have hl2 := h4_done (s := if B = 0 then false else true) (p := 2 * B)
    (T := t4H B P B R6) (t4H_getD_done B P R6)
  -- Assemble.
  rw [show t4Clock B P
      = 2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4 + (2
        + (t4Rounds B P B + (2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4
        + (2 * B + (8 + (2 * B + 1))))))))))))))))))
      from by rw [t4Clock]; omega,
    run_add, sd1, run_add, sd2, run_add, sd3, run_add, sd4, run_add, sd5, run_add, sd6,
    run_add, sd7, run_add, sd8, run_add, rr, run_add, eg1, run_add, eg2, run_add, eg3,
    run_add, eg4, run_add, eg5, run_add, eg6, run_add, eg7, run_add, eg8, run_add, eg9,
    run_add, hl1, hl2, t4H_out B P R6, hR6,
    show (t0 :: t1 :: TL2).drop (2 * B + 8) = TL2.drop (2 * B + 6) from by
      rw [show 2 * B + 8 = 2 * B + 6 + 1 + 1 from by omega]
      rfl]

/-- The done state halts. -/
theorem t4Machine_halt55 : t4Machine.halt ((55 : Fin 57), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4
