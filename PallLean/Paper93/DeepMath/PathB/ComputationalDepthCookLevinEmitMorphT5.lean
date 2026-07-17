import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT4

/-!
# Cook–Levin M2 emitter — arming morph brick M8: THE `T5` FILL

`T5`'s capacity span (`P+1` zero-pairs behind its placed live pair and marker), by the
front-bank zero-fill fabric: source `T2` drives the moving `01` frontier; `P` rounds
plus one endgame advance fill the span, and the frontier's final resting `01` IS `T6`'s
marker — the endgame writes nothing structural at all, the leanest pass of the arc.
The crossings hop `T3`'s tail and `T4`'s marker unconditionally, skip `T4`'s zero-fill
by content (exit on the first true low — `T5`'s live pair), and hop the live pair and
marker unconditionally.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT5

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4

/-! ## The descriptor family -/

/-- Mid-pass: `jS` source pairs marked, `jW` zero-fill advances done. -/
def t5T (B P jS jW : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (true :: true :: false :: true
    :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))))

/-- Mid-advance. -/
def t5A (B P jS jW : ℕ) (u v : Bool) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (true :: true :: false :: true
    :: (List.replicate (2 * jW + 2) false ++ (u :: v :: rest))))))))

/-- Mid-heal: `i` source marks healed (fill complete, `T6`'s marker resting). -/
def t5H (B P i : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (2 * i) true ++ (markedD (P - i) ++ ([false, true]
    ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (true :: true :: false :: true
    :: (List.replicate (2 * P + 2) false ++ ([false, true] ++ rest))))))))

/-- The exit: five targets written, `T6`'s marker placed. -/
def t5Out (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
    ++ (jT (P + 2) 1 ++ ([false, true] ++ rest)))))

theorem t5T_M (B P : ℕ) (rest : List Bool) :
    t5T B P P (P + 1) rest = t5H B P 0 rest := by
  rw [t5T, t5H, Nat.sub_self, Nat.sub_zero,
    show 2 * (P + 1) = 2 * P + 2 from by omega]
  rfl

theorem t5H_out (B P : ℕ) (rest : List Bool) : t5H B P P rest = t5Out B P rest := by
  have hj5 : jT (P + 2) 1
      = true :: true :: false :: true :: List.replicate (2 * P + 2) false := by
    rw [jT, show 2 * (P + 2 - 1) = 2 * P + 2 from by omega]
    rfl
  rw [t5H, t5Out, Nat.sub_self, unaryD_eq P, hj5]
  simp [markedD]

/-! ## The `getD` suite -/

theorem t5T_getD_T1lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (hi : i < B) :
    (t5T B P jS jW rest).getD (2 * i) false = true := by
  rw [t5T, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_T1FT (B P jS jW : ℕ) (rest : List Bool) :
    (t5T B P jS jW rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true
      ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5T, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading the source and beyond. -/
theorem t5T_getD_S (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) :
    (t5T B P jS jW rest).getD (2 * B + 2 + c) false
      = (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
        ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (true :: true :: false :: true
        :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))).getD c false := by
  rw [t5T, getD_append_left_length' _ _ (unaryD_length B)]

theorem t5T_getD_Smark_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t5T B P jS jW rest).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t5T_getD_S, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jS i h

theorem t5T_getD_Smark_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t5T B P jS jW rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h2 := t5T_getD_S B P jS jW rest (2 * i + 1)
  rw [show 2 * B + 2 + (2 * i + 1) = 2 * B + 2 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jS i h

theorem t5T_getD_Sdata (B P jS jW : ℕ) (rest : List Bool) (c : ℕ)
    (hjS : jS ≤ P) (h1 : 2 * jS ≤ c) (h2 : c < 2 * P) :
    (t5T B P jS jW rest).getD (2 * B + 2 + c) false = true := by
  rw [t5T_getD_S, show c = 2 * jS + (c - 2 * jS) from by omega,
    getD_append_left_length' _ _ (markedD_length jS),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_SFT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h2 := getD_append_left_length' (markedD jS)
    (List.replicate (2 * (P - jS)) true ++ ([false, true]
      ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))))
    (markedD_length jS) (2 * P - 2 * jS) false
  rw [show 2 * jS + (2 * P - 2 * jS) = 2 * P from by omega] at h2
  have h3 := getD_append_left_length' (List.replicate (2 * (P - jS)) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  rw [show (2 * P - 2 * jS : ℕ) = 2 * (P - jS) + 0 from by omega] at h2
  rw [t5T_getD_S, h2, h3]
  rfl

/-- Reading `T3` and beyond. -/
theorem t5T_getD_C (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (true :: true :: false :: true
        :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest))))).getD c false := by
  rw [t5T, show 2 * B + 2 * P + 4 + c
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + c))) from by omega,
    getD_append_left_length' _ _ (unaryD_length B),
    getD_append_left_length' _ _ (markedD_length jS),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t5T_getD_T3lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < P + 1) :
    (t5T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t5T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_T3FT (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ (jT (B + 2) 0 ++ (true :: true :: false :: true
      :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5T_getD_C B P jS jW rest _ hjS, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

/-- Reading `T4`'s fill and beyond. -/
theorem t5T_getD_D (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (2 * B + 4 * P + 12 + c) false
      = (List.replicate (2 * B + 4) false
        ++ (true :: true :: false :: true
        :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))).getD c false := by
  have hjlen : (jT (P + 2) (P + 1)).length = 2 * P + 6 := by
    rw [jT_length (P + 2) (P + 1) (by omega)]
    omega
  have hj4 : jT (B + 2) 0 = [false, true] ++ List.replicate (2 * B + 4) false := by
    rw [jT, show 2 * (B + 2 - 0) = 2 * B + 4 from by omega]
    rfl
  have h := t5T_getD_C B P jS jW rest (2 * P + 6 + (2 + c)) hjS
  rw [show 2 * B + 2 * P + 4 + (2 * P + 6 + (2 + c)) = 2 * B + 4 * P + 12 + c
      from by omega,
    getD_append_left_length' _ _ hjlen, hj4, List.append_assoc,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t5T_getD_fill4_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < B + 2) :
    (t5T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * i) false = false := by
  rw [t5T_getD_D B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_fill4_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < B + 2) :
    (t5T B P jS jW rest).getD (2 * B + 4 * P + 12 + 2 * i + 1) false = false := by
  have h := t5T_getD_D B P jS jW rest (2 * i + 1) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * i + 1) = 2 * B + 4 * P + 12 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_liveLo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 16) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * B + 4) false)
    (true :: true :: false :: true
      :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t5T_getD_D B P jS jW rest (2 * B + 4) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4) = 4 * B + 4 * P + 16 from by omega] at h
  rw [h, h2]
  rfl

/-- Reading the fill zone and beyond. -/
theorem t5T_getD_F (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 20 + c) false
      = (List.replicate (2 * jW) false ++ ([false, true] ++ rest)).getD c false := by
  have h := t5T_getD_D B P jS jW rest (2 * B + 4 + (4 + c)) hjS
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4 + (4 + c)) = 4 * B + 4 * P + 20 + c
      from by omega,
    getD_append_left_length' _ _ List.length_replicate,
    show (true :: true :: false :: true
        :: (List.replicate (2 * jW) false ++ ([false, true] ++ rest)) : List Bool)
      = [true, true, false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ rest)) from rfl,
    getD_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl)] at h
  exact h

theorem t5T_getD_fill_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * i) false = false := by
  rw [t5T_getD_F B P jS jW rest _ hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_fill_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * i + 1) false = false := by
  have h := t5T_getD_F B P jS jW rest (2 * i + 1) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * i + 1) = 4 * B + 4 * P + 20 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5T_getD_frontier_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * jW) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t5T_getD_F B P jS jW rest _ hjS, h2]
  rfl

theorem t5T_getD_frontier_hi (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t5T B P jS jW rest).getD (4 * B + 4 * P + 20 + 2 * jW + 1) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ rest) List.length_replicate 1 false
  have h := t5T_getD_F B P jS jW rest (2 * jW + 1) hjS
  rw [show 4 * B + 4 * P + 20 + (2 * jW + 1) = 4 * B + 4 * P + 20 + 2 * jW + 1
    from by omega] at h
  rw [h, h2]
  rfl

/-! ## The write lemmas -/

theorem t5T_markSrc (B P jS jW : ℕ) (rest : List Bool) (hjS : jS < P) :
    writeAt (t5T B P jS jW rest) (2 * B + 2 + 2 * jS + 1) false
      = t5T B P (jS + 1) jW rest := by
  rw [writeAt_of_lt false (by
      simp only [t5T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      omega), t5T,
    show 2 * B + 2 + 2 * jS + 1 = 2 * B + 2 + (2 * jS + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    show List.replicate (2 * (P - jS)) true
      = true :: true :: List.replicate (2 * (P - jS - 1)) true from by
        rw [show 2 * (P - jS) = 2 * (P - jS - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t5T, ← markedD_snoc, show P - (jS + 1) = P - jS - 1 from by omega]
  simp [List.append_assoc]

theorem t5T_adv1 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t5T B P jS jW (r0 :: r1 :: rest)) (4 * B + 4 * P + 20 + 2 * jW + 1) false
      = t5A B P jS jW r0 r1 rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW) false)
    ([false, true] ++ (r0 :: r1 :: rest)) List.length_replicate 1 false
  rw [writeAt_of_lt false (by
      simp only [t5T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      omega), t5T,
    show 4 * B + 4 * P + 20 + 2 * jW + 1
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * P + 6 + (2 * B + 6
        + (4 + (2 * jW + 1))))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    show (true :: true :: false :: true
        :: (List.replicate (2 * jW) false ++ ([false, true] ++ (r0 :: r1 :: rest)))
        : List Bool)
      = [true, true, false, true]
        ++ (List.replicate (2 * jW) false ++ ([false, true] ++ (r0 :: r1 :: rest)))
      from rfl,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    hset]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t5A, show (2 * jW + 2 : ℕ) = 2 * jW + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * jW + 1), List.replicate_succ' (n := 2 * jW)]
  simp

theorem t5A_write (B P jS jW k : ℕ) (w u v : Bool) (rest : List Bool)
    (hjS : jS ≤ P) (hk : k < (u :: v :: rest).length) :
    writeAt (t5A B P jS jW u v rest) (4 * B + 4 * P + 20 + 2 * jW + 2 + k) w
      = unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
        ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (true :: true :: false :: true
        :: (List.replicate (2 * jW + 2) false ++ ((u :: v :: rest).set k w)))))))) := by
  rw [writeAt_of_lt w (by
      simp only [t5A, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      simp only [List.length_cons] at hk
      omega), t5A,
    show 4 * B + 4 * P + 20 + 2 * jW + 2 + k
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * P + 6 + (2 * B + 6
        + (4 + (2 * jW + 2 + k))))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    show (true :: true :: false :: true
        :: (List.replicate (2 * jW + 2) false ++ (u :: v :: rest)) : List Bool)
      = [true, true, false, true]
        ++ (List.replicate (2 * jW + 2) false ++ (u :: v :: rest)) from rfl,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl),
    set_append_left_length' _ _ List.length_replicate]
  rfl

theorem t5T_adv2 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t5A B P jS jW r0 r1 rest) (4 * B + 4 * P + 20 + 2 * jW + 2) false
      = t5A B P jS jW false r1 rest := by
  have h := t5A_write B P jS jW 0 false r0 r1 rest hjS (by simp)
  rw [show 4 * B + 4 * P + 20 + 2 * jW + 2 + 0 = 4 * B + 4 * P + 20 + 2 * jW + 2
      from by omega,
    show ((r0 :: r1 :: rest).set 0 false : List Bool) = false :: r1 :: rest from rfl]
    at h
  rw [h, t5A]

theorem t5A_writeV (B P jS jW : ℕ) (w u v : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t5A B P jS jW u v rest) (4 * B + 4 * P + 20 + 2 * jW + 3) w
      = t5A B P jS jW u w rest := by
  have h := t5A_write B P jS jW 1 w u v rest hjS (by simp)
  rw [show 4 * B + 4 * P + 20 + 2 * jW + 2 + 1 = 4 * B + 4 * P + 20 + 2 * jW + 3
      from by omega,
    show ((u :: v :: rest).set 1 w : List Bool) = u :: w :: rest from rfl] at h
  rw [h, t5A]

theorem t5A_fold (B P jS jW : ℕ) (rest : List Bool) :
    t5A B P jS jW false true rest = t5T B P jS (jW + 1) rest := by
  rw [t5A, t5T, show (2 * (jW + 1) : ℕ) = 2 * jW + 2 from by omega]
  simp

theorem t5H_heal (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    writeAt (t5H B P i rest) (2 * B + 2 + 2 * i + 1) true = t5H B P (i + 1) rest := by
  rw [writeAt_of_lt true (by
      simp only [t5H, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      omega), t5H,
    show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t5H, show P - (i + 1) = P - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ### Heal reads -/

theorem t5H_getD_T1lo (B P i : ℕ) (rest : List Bool) (k : ℕ) (hk : k < B) :
    (t5H B P i rest).getD (2 * k) false = true := by
  rw [t5H, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t5H_getD_T1FT (B P i : ℕ) (rest : List Bool) :
    (t5H B P i rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (List.replicate (2 * i) true ++ (markedD (P - i)
      ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * P + 2) false ++ ([false, true] ++ rest)))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5H, unaryD_eq, List.append_assoc, h]
  rfl

theorem t5H_getD_lo (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t5H B P i rest).getD (2 * B + 2 + 2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * P + 2) false ++ ([false, true] ++ rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5H, getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t5H_getD_hi (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t5H B P i rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * P + 2) false ++ ([false, true] ++ rest)))))))
    List.length_replicate 1 false
  rw [t5H, show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t5H_getD_done (B P : ℕ) (rest : List Bool) :
    (t5H B P P rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    (markedD (P - P) ++ ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true
      :: (List.replicate (2 * P + 2) false ++ ([false, true] ++ rest)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t5H, getD_append_left_length' _ _ (unaryD_length B), h, Nat.sub_self]
  rfl

/-! ## Seed reads and writes (on the entry shape) -/

theorem t4Out_getD_T1lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B) :
    (t4Out B P TL).getD (2 * i) false = true := by
  rw [t4Out, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4Out_getD_T1FT (B P : ℕ) (TL : List Bool) :
    (t4Out B P TL).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true :: TL)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4Out, unaryD_eq B, List.append_assoc, h]
  rfl

theorem t4Out_getD_A (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t4Out B P TL).getD (2 * B + 2 + c) false
      = (unaryD P ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (true :: true :: false :: true :: TL)))).getD c false := by
  rw [t4Out, getD_append_left_length' _ _ (unaryD_length B)]

theorem t4Out_getD_T2lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P) :
    (t4Out B P TL).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t4Out_getD_A, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4Out_getD_T2FT (B P : ℕ) (TL : List Bool) :
    (t4Out B P TL).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
      ++ (true :: true :: false :: true :: TL))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4Out_getD_A, unaryD_eq, List.append_assoc, h]
  rfl

theorem t4Out_getD_C (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t4Out B P TL).getD (2 * B + 2 * P + 4 + c) false
      = (jT (P + 2) (P + 1) ++ (jT (B + 2) 0
        ++ (true :: true :: false :: true :: TL))).getD c false := by
  have h := t4Out_getD_A B P TL (2 * P + 2 + c)
  rw [show 2 * B + 2 + (2 * P + 2 + c) = 2 * B + 2 * P + 4 + c from by omega,
    getD_append_left_length' _ _ (unaryD_length P)] at h
  exact h

theorem t4Out_getD_T3lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P + 1) :
    (t4Out B P TL).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t4Out_getD_C, jT, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4Out_getD_T3FT (B P : ℕ) (TL : List Bool) :
    (t4Out B P TL).getD (2 * B + 2 * P + 4 + (2 * P + 2)) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (([false, true] ++ List.replicate (2 * (P + 2 - (P + 1))) false)
      ++ (jT (B + 2) 0 ++ (true :: true :: false :: true :: TL)))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t4Out_getD_C, jT, List.append_assoc,
    show (2 * P + 2 : ℕ) = 2 * (P + 1) from by omega, h]
  rfl

theorem t4Out_getD_D (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t4Out B P TL).getD (2 * B + 4 * P + 12 + c) false
      = (List.replicate (2 * B + 4) false
        ++ (true :: true :: false :: true :: TL)).getD c false := by
  have hjlen : (jT (P + 2) (P + 1)).length = 2 * P + 6 := by
    rw [jT_length (P + 2) (P + 1) (by omega)]
    omega
  have hj4 : jT (B + 2) 0 = [false, true] ++ List.replicate (2 * B + 4) false := by
    rw [jT, show 2 * (B + 2 - 0) = 2 * B + 4 from by omega]
    rfl
  have h := t4Out_getD_C B P TL (2 * P + 6 + (2 + c))
  rw [show 2 * B + 2 * P + 4 + (2 * P + 6 + (2 + c)) = 2 * B + 4 * P + 12 + c
      from by omega,
    getD_append_left_length' _ _ hjlen, hj4, List.append_assoc,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
    at h
  exact h

theorem t4Out_getD_fill4_lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B + 2) :
    (t4Out B P TL).getD (2 * B + 4 * P + 12 + 2 * i) false = false := by
  rw [t4Out_getD_D, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4Out_getD_fill4_hi (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B + 2) :
    (t4Out B P TL).getD (2 * B + 4 * P + 12 + 2 * i + 1) false = false := by
  have h := t4Out_getD_D B P TL (2 * i + 1)
  rw [show 2 * B + 4 * P + 12 + (2 * i + 1) = 2 * B + 4 * P + 12 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t4Out_getD_liveLo (B P : ℕ) (TL : List Bool) :
    (t4Out B P TL).getD (4 * B + 4 * P + 16) false = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * B + 4) false)
    (true :: true :: false :: true :: TL) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  have h := t4Out_getD_D B P TL (2 * B + 4)
  rw [show 2 * B + 4 * P + 12 + (2 * B + 4) = 4 * B + 4 * P + 16 from by omega] at h
  rw [h, h2]
  rfl

theorem t4Out_seed1 (B P : ℕ) (t0 t1 : Bool) (TL : List Bool) :
    writeAt (t4Out B P (t0 :: t1 :: TL)) (4 * B + 4 * P + 20) false
      = t4Out B P (false :: t1 :: TL) := by
  rw [writeAt_of_lt false (by
      simp only [t4Out, List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      omega), t4Out,
    show 4 * B + 4 * P + 20
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 * B + 6 + (4 + 0)))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    show (true :: true :: false :: true :: (t0 :: t1 :: TL) : List Bool)
      = [true, true, false, true] ++ (t0 :: t1 :: TL) from rfl,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl)]
  rw [t4Out]
  rfl

theorem t4Out_seed2 (B P : ℕ) (t1 : Bool) (TL : List Bool) :
    writeAt (t4Out B P (false :: t1 :: TL)) (4 * B + 4 * P + 21) true
      = t5T B P 0 0 TL := by
  rw [writeAt_of_lt true (by
      simp only [t4Out, List.length_append, List.length_cons, unaryD_length,
        jT_length (P + 2) (P + 1) (by omega), jT_length (B + 2) 0 (by omega)]
      omega), t4Out,
    show 4 * B + 4 * P + 21
      = 2 * B + 2 + (2 * P + 2 + (2 * P + 6 + (2 * B + 6 + (4 + 1)))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ (show (jT (P + 2) (P + 1)).length = 2 * P + 6 from by
      rw [jT_length (P + 2) (P + 1) (by omega)]; omega),
    set_append_left_length' _ _ (show (jT (B + 2) 0).length = 2 * B + 6 from by
      rw [jT_length (B + 2) 0 (by omega)]; omega),
    show (true :: true :: false :: true :: (false :: t1 :: TL) : List Bool)
      = [true, true, false, true] ++ (false :: t1 :: TL) from rfl,
    set_append_left_length' _ _
      (show ([true, true, false, true] : List Bool).length = 4 from rfl)]
  simp only [List.set_cons_succ, List.set_cons_zero]
  rw [t5T, Nat.sub_zero]
  simp [unaryD_eq, markedD]

/-! ## The `T5` machine

Control: `State = Fin 68 × Bool`.  Seed `0-19` (cross `T1`/`T2`/`T3`, hop `T3`'s tail
and `T4`'s marker, skip `T4`'s zero-fill by content, hop `T5`'s live pair and marker,
plant the frontier, reset), round `20-43` (cross `T1`, mark source pair `j` in `T2`,
flow right, 3-write advance, reset), endgame `44-60` (source spent: flow right, ONE
final advance — the resting `01` IS `T6`'s marker, nothing else written — reset), heal
`61-65`, done `66`, dead `67`. -/

def t5Machine : Machine where
  State := Fin 68 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 66) || decide (s.1 = 67)
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
    else if s.1 = 18 then ((19, s.2), some false, 1)
    else if s.1 = 19 then ((20, s.2), some true, 3)
    else if s.1 = 20 then (if b then ((21, b), none, 1) else ((22, b), none, 1))
    else if s.1 = 21 then ((20, s.2), none, 1)
    else if s.1 = 22 then ((23, s.2), none, 1)
    else if s.1 = 23 then (if b then ((24, b), none, 1) else ((44, b), none, 1))
    else if s.1 = 24 then
      (if b then ((25, s.2), some false, 1) else ((23, s.2), none, 1))
    else if s.1 = 25 then (if b then ((26, b), none, 1) else ((27, b), none, 1))
    else if s.1 = 26 then ((25, s.2), none, 1)
    else if s.1 = 27 then ((28, s.2), none, 1)
    else if s.1 = 28 then (if b then ((29, b), none, 1) else ((30, b), none, 1))
    else if s.1 = 29 then ((28, s.2), none, 1)
    else if s.1 = 30 then ((31, s.2), none, 1)
    else if s.1 = 31 then ((32, s.2), none, 1)
    else if s.1 = 32 then ((33, s.2), none, 1)
    else if s.1 = 33 then ((34, s.2), none, 1)
    else if s.1 = 34 then ((35, s.2), none, 1)
    else if s.1 = 35 then (if b then ((37, b), none, 1) else ((36, b), none, 1))
    else if s.1 = 36 then ((35, s.2), none, 1)
    else if s.1 = 37 then ((38, s.2), none, 1)
    else if s.1 = 38 then ((39, s.2), none, 1)
    else if s.1 = 39 then ((40, s.2), none, 1)
    else if s.1 = 40 then (if b then ((67, b), none, 2) else ((41, b), none, 1))
    else if s.1 = 41 then
      (if b then ((42, s.2), some false, 1) else ((40, s.2), none, 1))
    else if s.1 = 42 then ((43, s.2), some false, 1)
    else if s.1 = 43 then ((20, s.2), some true, 3)
    else if s.1 = 44 then ((45, s.2), none, 1)
    else if s.1 = 45 then (if b then ((46, b), none, 1) else ((47, b), none, 1))
    else if s.1 = 46 then ((45, s.2), none, 1)
    else if s.1 = 47 then ((48, s.2), none, 1)
    else if s.1 = 48 then ((49, s.2), none, 1)
    else if s.1 = 49 then ((50, s.2), none, 1)
    else if s.1 = 50 then ((51, s.2), none, 1)
    else if s.1 = 51 then ((52, s.2), none, 1)
    else if s.1 = 52 then (if b then ((54, b), none, 1) else ((53, b), none, 1))
    else if s.1 = 53 then ((52, s.2), none, 1)
    else if s.1 = 54 then ((55, s.2), none, 1)
    else if s.1 = 55 then ((56, s.2), none, 1)
    else if s.1 = 56 then ((57, s.2), none, 1)
    else if s.1 = 57 then (if b then ((67, b), none, 2) else ((58, b), none, 1))
    else if s.1 = 58 then
      (if b then ((59, s.2), some false, 1) else ((57, s.2), none, 1))
    else if s.1 = 59 then ((60, s.2), some false, 1)
    else if s.1 = 60 then ((61, s.2), some true, 3)
    else if s.1 = 61 then (if b then ((62, b), none, 1) else ((63, b), none, 1))
    else if s.1 = 62 then ((61, s.2), none, 1)
    else if s.1 = 63 then ((64, s.2), none, 1)
    else if s.1 = 64 then (if b then ((65, b), none, 1) else ((66, b), none, 2))
    else if s.1 = 65 then
      (if b then ((67, s.2), none, 2) else ((64, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 66)

theorem init_t5 (x : List Bool) : init t5Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem p5_0T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_0F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_1 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_3T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_3F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_5 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_6T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_6F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(6, s), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_7 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(7, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_8 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_9 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(9, s), p, T⟩ = ⟨(10, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_10 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(10, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_11 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(11, s), p, T⟩ = ⟨(12, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_12 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_13T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(13, s), p, T⟩ = ⟨(15, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_13F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(13, s), p, T⟩ = ⟨(14, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_14 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(14, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_15 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(15, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_16 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(16, s), p, T⟩ = ⟨(17, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_17 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(17, s), p, T⟩ = ⟨(18, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_18 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(18, s), p, T⟩ = ⟨(19, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_19 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(19, s), p, T⟩ = ⟨(20, s), 0, writeAt T p true⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_20T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(20, s), p, T⟩ = ⟨(21, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_20F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(20, s), p, T⟩ = ⟨(22, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_21 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(21, s), p, T⟩ = ⟨(20, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_22 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(22, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_23T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(23, s), p, T⟩ = ⟨(24, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_23F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(23, s), p, T⟩ = ⟨(44, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_24T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(24, s), p, T⟩ = ⟨(25, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_24F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(24, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_25T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(25, s), p, T⟩ = ⟨(26, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_25F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(25, s), p, T⟩ = ⟨(27, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_26 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(26, s), p, T⟩ = ⟨(25, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_27 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(27, s), p, T⟩ = ⟨(28, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_28T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(28, s), p, T⟩ = ⟨(29, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_28F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(28, s), p, T⟩ = ⟨(30, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_29 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(29, s), p, T⟩ = ⟨(28, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_30 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(30, s), p, T⟩ = ⟨(31, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_31 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(31, s), p, T⟩ = ⟨(32, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_32 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(32, s), p, T⟩ = ⟨(33, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_33 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(33, s), p, T⟩ = ⟨(34, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_34 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(34, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_35T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(35, s), p, T⟩ = ⟨(37, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_35F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(35, s), p, T⟩ = ⟨(36, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_36 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(36, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_37 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(37, s), p, T⟩ = ⟨(38, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_38 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(38, s), p, T⟩ = ⟨(39, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_39 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(39, s), p, T⟩ = ⟨(40, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_40F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(40, s), p, T⟩ = ⟨(41, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_41T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(41, s), p, T⟩ = ⟨(42, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_41F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(41, s), p, T⟩ = ⟨(40, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_42 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(42, s), p, T⟩ = ⟨(43, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_43 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(43, s), p, T⟩ = ⟨(20, s), 0, writeAt T p true⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_44 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(44, s), p, T⟩ = ⟨(45, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_45T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(45, s), p, T⟩ = ⟨(46, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_45F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(45, s), p, T⟩ = ⟨(47, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_46 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(46, s), p, T⟩ = ⟨(45, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_47 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(47, s), p, T⟩ = ⟨(48, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_48 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(48, s), p, T⟩ = ⟨(49, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_49 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(49, s), p, T⟩ = ⟨(50, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_50 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(50, s), p, T⟩ = ⟨(51, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_51 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(51, s), p, T⟩ = ⟨(52, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_52T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(52, s), p, T⟩ = ⟨(54, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_52F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(52, s), p, T⟩ = ⟨(53, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_53 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(53, s), p, T⟩ = ⟨(52, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_54 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(54, s), p, T⟩ = ⟨(55, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_55 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(55, s), p, T⟩ = ⟨(56, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_56 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(56, s), p, T⟩ = ⟨(57, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_57F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(57, s), p, T⟩ = ⟨(58, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_58T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(58, s), p, T⟩ = ⟨(59, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_58F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(58, s), p, T⟩ = ⟨(57, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_59 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(59, s), p, T⟩ = ⟨(60, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_60 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(60, s), p, T⟩ = ⟨(61, s), 0, writeAt T p true⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_61T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(61, s), p, T⟩ = ⟨(62, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_61F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(61, s), p, T⟩ = ⟨(63, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_62 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(62, s), p, T⟩ = ⟨(61, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_63 {s : Bool} {p : ℕ} {T : List Bool} :
    step t5Machine ⟨(63, s), p, T⟩ = ⟨(64, s), p + 1, T⟩ := by
  simp only [step, t5Machine, moveHead]; rfl

theorem p5_64T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t5Machine ⟨(64, s), p, T⟩ = ⟨(65, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_64F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(64, s), p, T⟩ = ⟨(66, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

theorem p5_65F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t5Machine ⟨(65, s), p, T⟩ = ⟨(64, s), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t5Machine, moveHead, h]

/-! ### Composites -/

theorem c5_seedT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_0T h1, p5_1]

theorem c5_seedX1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_0F h1, p5_2]

theorem c5_seedT2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_3T h1, p5_4]

theorem c5_seedX2 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_3F h1, p5_5]

theorem c5_seedT3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_6T h1, p5_7]

theorem c5_seedX3 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(6, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_6F h1, p5_8]

theorem c5_seedHops {s : Bool} {p : ℕ} {T : List Bool} :
    run t5Machine 4 ⟨(9, s), p, T⟩ = ⟨(13, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_9, p5_10, p5_11, p5_12]

theorem c5_seedFill {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(13, s), p, T⟩ = ⟨(13, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_13F h1, p5_14]

theorem c5_seedLive {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 4 ⟨(13, s), p, T⟩ = ⟨(18, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_13T h1, p5_15, p5_16, p5_17]

theorem c5_seedWrites {s : Bool} {p : ℕ} {T : List Bool} :
    run t5Machine 2 ⟨(18, s), p, T⟩
      = ⟨(20, s), 0, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, p5_18, p5_19]

theorem c5_T1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(20, s), p, T⟩ = ⟨(20, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_20T h1, p5_21]

theorem c5_X1r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(20, s), p, T⟩ = ⟨(23, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_20F h1, p5_22]

theorem c5_skipMk {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t5Machine 2 ⟨(23, s), p, T⟩ = ⟨(23, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_23T h1, p5_24F h2]

theorem c5_mark {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t5Machine 2 ⟨(23, s), p, T⟩ = ⟨(25, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, p5_23T h1, p5_24T h2]

theorem c5_exhaust {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(23, s), p, T⟩ = ⟨(45, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_23F h1, p5_44]

theorem c5_T2r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(25, s), p, T⟩ = ⟨(25, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_25T h1, p5_26]

theorem c5_X2r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(25, s), p, T⟩ = ⟨(28, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_25F h1, p5_27]

theorem c5_T3r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_28T h1, p5_29]

theorem c5_X3r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(28, s), p, T⟩ = ⟨(31, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_28F h1, p5_30]

theorem c5_hopsR {s : Bool} {p : ℕ} {T : List Bool} :
    run t5Machine 4 ⟨(31, s), p, T⟩ = ⟨(35, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_31, p5_32, p5_33, p5_34]

theorem c5_fillR {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(35, s), p, T⟩ = ⟨(35, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_35F h1, p5_36]

theorem c5_liveR {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 4 ⟨(35, s), p, T⟩ = ⟨(40, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_35T h1, p5_37, p5_38, p5_39]

theorem c5_skipF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t5Machine 2 ⟨(40, s), p, T⟩ = ⟨(40, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_40F h1, p5_41F h2]

theorem c5_adv {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t5Machine 4 ⟨(40, s), p, T⟩
      = ⟨(20, false), 0,
          writeAt (writeAt (writeAt T (p + 1) false) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_40F h1, p5_41T h2, p5_42,
    p5_43]

theorem c5_T3e {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(45, s), p, T⟩ = ⟨(45, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_45T h1, p5_46]

theorem c5_X3e {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(45, s), p, T⟩ = ⟨(48, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_45F h1, p5_47]

theorem c5_hopsE {s : Bool} {p : ℕ} {T : List Bool} :
    run t5Machine 4 ⟨(48, s), p, T⟩ = ⟨(52, s), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_48, p5_49, p5_50, p5_51]

theorem c5_fillE {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(52, s), p, T⟩ = ⟨(52, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_52F h1, p5_53]

theorem c5_liveE {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 4 ⟨(52, s), p, T⟩ = ⟨(57, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_52T h1, p5_54, p5_55, p5_56]

theorem c5_skipFe {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run t5Machine 2 ⟨(57, s), p, T⟩ = ⟨(57, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_57F h1, p5_58F h2]

theorem c5_advE {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t5Machine 4 ⟨(57, s), p, T⟩
      = ⟨(61, false), 0,
          writeAt (writeAt (writeAt T (p + 1) false) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, p5_57F h1, p5_58T h2, p5_59,
    p5_60]

theorem c5_T1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t5Machine 2 ⟨(61, s), p, T⟩ = ⟨(61, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_61T h1, p5_62]

theorem c5_X1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t5Machine 2 ⟨(61, s), p, T⟩ = ⟨(64, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, p5_61F h1, p5_63]

theorem c5_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t5Machine 2 ⟨(64, s), p, T⟩ = ⟨(64, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, p5_64T h1, p5_65F h2]

theorem c5_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    run t5Machine 1 ⟨(64, s), p, T⟩ = ⟨(66, false), p, T⟩ := by
  rw [run_succ, run_zero, p5_64F h]

/-! ### Scan run-invariants -/

theorem w5_seedT1 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_seedT1 (h k (by omega))]
    rfl

theorem w5_seedT2 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_seedT2 (h k (by omega))]
    rfl

theorem w5_seedT3 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_seedT3 (h k (by omega))]
    rfl

theorem w5_seedFill (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t5Machine (2 * k) ⟨(13, s), q, T⟩
      = ⟨(13, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_seedFill (h k (by omega))]
    rfl

theorem w5_T1r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_T1 (h k (by omega))]
    rfl

theorem w5_skipMk (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t5Machine (2 * k) ⟨(23, s), q, T⟩
      = ⟨(23, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_skipMk hk.1 hk.2]
    rfl

theorem w5_T2r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(25, s), q, T⟩
      = ⟨(25, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_T2r (h k (by omega))]
    rfl

theorem w5_T3r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(28, s), q, T⟩
      = ⟨(28, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_T3r (h k (by omega))]
    rfl

theorem w5_fillR (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t5Machine (2 * k) ⟨(35, s), q, T⟩
      = ⟨(35, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_fillR (h k (by omega))]
    rfl

theorem w5_skipF (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t5Machine (2 * k) ⟨(40, s), q, T⟩
      = ⟨(40, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_skipF hk.1 hk.2]
    rfl

theorem w5_T3e (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(45, s), q, T⟩
      = ⟨(45, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_T3e (h k (by omega))]
    rfl

theorem w5_fillE (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false) :
    run t5Machine (2 * k) ⟨(52, s), q, T⟩
      = ⟨(52, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_fillE (h k (by omega))]
    rfl

theorem w5_skipFe (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = false
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t5Machine (2 * k) ⟨(57, s), q, T⟩
      = ⟨(57, if k = 0 then s else false), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_skipFe hk.1 hk.2]
    rfl

theorem w5_T1h (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t5Machine (2 * k) ⟨(61, s), q, T⟩
      = ⟨(61, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), c5_T1h (h k (by omega))]
    rfl

/-- Heal the source, tape evolving. -/
theorem w5_heal (B P : ℕ) (rest : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P →
    run t5Machine (2 * k) ⟨(64, s), 2 * B + 2 + 2 * i, t5H B P i rest⟩
      = ⟨(64, if k = 0 then s else true), 2 * B + 2 + 2 * (i + k),
          t5H B P (i + k) rest⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      c5_heal (t5H_getD_lo B P i rest (by omega)) (t5H_getD_hi B P i rest (by omega)),
      t5H_heal B P i rest (by omega),
      show 2 * B + 2 + 2 * i + 2 = 2 * B + 2 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The round invariant -/

/-- **One fill round**: mark source pair `j` in `T2`, advance the zero-fill. -/
theorem t5_round (B P j : ℕ) (r0 r1 : Bool) (rest : List Bool) (s : Bool)
    (hj : j < P) :
    run t5Machine (4 * B + 4 * P + 2 * j + 24)
      ⟨(20, s), 0, t5T B P j j (r0 :: r1 :: rest)⟩
      = ⟨(20, false), 0, t5T B P (j + 1) (j + 1) rest⟩ := by
  have st1 := w5_T1r (t5T B P j j (r0 :: r1 :: rest)) 0 B s (fun i hi => by
    simpa using t5T_getD_T1lo B P j j _ i hi)
  simp only [Nat.zero_add] at st1
  have st2 := c5_X1r (s := if B = 0 then s else true) (p := 2 * B)
    (T := t5T B P j j (r0 :: r1 :: rest)) (t5T_getD_T1FT B P j j _)
  have st3 := w5_skipMk (t5T B P j j (r0 :: r1 :: rest)) (2 * B + 2) j false
    (fun i hi => ⟨t5T_getD_Smark_lo B P j j _ i hi, t5T_getD_Smark_hi B P j j _ i hi⟩)
  have h4b : (t5T B P j j (r0 :: r1 :: rest)).getD (2 * B + 2 + 2 * j + 1) false
      = true := by
    have h := t5T_getD_Sdata B P j j (r0 :: r1 :: rest) (2 * j + 1) (by omega)
      (by omega) (by omega)
    rwa [show 2 * B + 2 + (2 * j + 1) = 2 * B + 2 + 2 * j + 1 from by omega] at h
  have st4 := c5_mark (s := if j = 0 then false else true) (p := 2 * B + 2 + 2 * j)
    (T := t5T B P j j (r0 :: r1 :: rest))
    (t5T_getD_Sdata B P j j _ (2 * j) (by omega) (by omega) (by omega)) h4b
  rw [t5T_markSrc B P j j _ hj] at st4
  have st5 := w5_T2r (t5T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 + 2 * j + 2)
    (P - j - 1) true (fun i hi => by
      have h := t5T_getD_Sdata B P (j + 1) j (r0 :: r1 :: rest) (2 * j + 2 + 2 * i)
        (by omega) (by omega) (by omega)
      rwa [show 2 * B + 2 + (2 * j + 2 + 2 * i) = 2 * B + 2 + 2 * j + 2 + 2 * i
        from by omega] at h)
  rw [show 2 * B + 2 + 2 * j + 2 + 2 * (P - j - 1) = 2 * B + 2 + 2 * P from by omega,
    ite_self] at st5
  have st6 := c5_X2r (s := true) (p := 2 * B + 2 + 2 * P)
    (T := t5T B P (j + 1) j (r0 :: r1 :: rest))
    (t5T_getD_SFT B P (j + 1) j _ (by omega))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at st6
  have st7 := w5_T3r (t5T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 * P + 4)
    (P + 1) false (fun i hi => t5T_getD_T3lo B P (j + 1) j _ i (by omega) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at st7
  have h8 := t5T_getD_T3FT B P (j + 1) j (r0 :: r1 :: rest) (by omega)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h8
  have st8 := c5_X3r (s := true) (p := 2 * B + 4 * P + 6)
    (T := t5T B P (j + 1) j (r0 :: r1 :: rest)) h8
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at st8
  have st9 := c5_hopsR (s := false) (p := 2 * B + 4 * P + 8)
    (T := t5T B P (j + 1) j (r0 :: r1 :: rest))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at st9
  have st10 := w5_fillR (t5T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 4 * P + 12)
    (B + 2) false (fun i hi => t5T_getD_fill4_lo B P (j + 1) j _ i (by omega) hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at st10
  have st11 := c5_liveR (s := false) (p := 4 * B + 4 * P + 16)
    (T := t5T B P (j + 1) j (r0 :: r1 :: rest))
    (t5T_getD_liveLo B P (j + 1) j _ (by omega))
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at st11
  have st12 := w5_skipF (t5T B P (j + 1) j (r0 :: r1 :: rest)) (4 * B + 4 * P + 20) j
    true (fun i hi => ⟨t5T_getD_fill_lo B P (j + 1) j _ i (by omega) hi,
      t5T_getD_fill_hi B P (j + 1) j _ i (by omega) hi⟩)
  have st13 := c5_adv (s := if j = 0 then true else false)
    (p := 4 * B + 4 * P + 20 + 2 * j) (T := t5T B P (j + 1) j (r0 :: r1 :: rest))
    (t5T_getD_frontier_lo B P (j + 1) j _ (by omega))
    (t5T_getD_frontier_hi B P (j + 1) j _ (by omega))
  rw [t5T_adv1 B P (j + 1) j r0 r1 rest (by omega),
    t5T_adv2 B P (j + 1) j r0 r1 rest (by omega),
    t5A_writeV B P (j + 1) j true false r1 rest (by omega),
    t5A_fold B P (j + 1) j rest] at st13
  rw [show 4 * B + 4 * P + 2 * j + 24
      = 2 * B + (2 + (2 * j + (2 + (2 * (P - j - 1) + (2 + (2 * (P + 1) + (2 + (4
        + (2 * (B + 2) + (4 + (2 * j + 4))))))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, run_add, st11, run_add,
    st12, st13]

/-! ## The rounds, the endgame, the run -/

/-- The cumulative clock of the first `k` rounds. -/
def t5Rounds (B P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t5Rounds B P k + (4 * B + 4 * P + 2 * k + 24)

theorem t5_rounds (B P : ℕ) (rest : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ P) (hlen : 2 * k ≤ rest.length) :
    run t5Machine (t5Rounds B P k) ⟨(20, s), 0, t5T B P 0 0 rest⟩
      = ⟨(20, if k = 0 then s else false), 0, t5T B P k k (rest.drop (2 * k))⟩ := by
  induction k with
  | zero => simp [t5Rounds]
  | succ k ih =>
    rw [show t5Rounds B P (k + 1) = t5Rounds B P k + (4 * B + 4 * P + 2 * k + 24)
        from rfl,
      run_add, ih (by omega) (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
      t5_round B P k _ _ _ _ (by omega), if_neg (by omega)]

/-- The pass's exact clock. -/
def t5Clock (B P : ℕ) : ℕ :=
  (4 * B + 4 * P + 22)
    + (t5Rounds B P P + ((4 * B + 6 * P + 24) + (2 * B + 2 * P + 3)))

set_option maxHeartbeats 1600000 in
/-- **THE `T5` FILL RUNS**: from the four-target front and ANY dead tail of length at
least `2P+4`, the pass halts DONE with `T5` complete and `T6`'s marker placed (the
resting frontier) — consuming exactly `2P+4` tail cells. -/
theorem t5Machine_run (B P : ℕ) (TAIL : List Bool) (hlen : 2 * P + 4 ≤ TAIL.length) :
    run t5Machine (t5Clock B P) (init t5Machine (t4Out B P TAIL))
      = ⟨(66, false), 2 * B + 2 + 2 * P, t5Out B P (TAIL.drop (2 * P + 4))⟩ := by
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
  rw [init_t5]
  -- Seed.
  have sd1 := w5_seedT1 (t4Out B P (t0 :: t1 :: TL2)) 0 B false (fun i hi => by
    simpa using t4Out_getD_T1lo B P _ i hi)
  simp only [Nat.zero_add] at sd1
  have sd2 := c5_seedX1 (s := if B = 0 then false else true) (p := 2 * B)
    (T := t4Out B P (t0 :: t1 :: TL2)) (t4Out_getD_T1FT B P _)
  have sd3 := w5_seedT2 (t4Out B P (t0 :: t1 :: TL2)) (2 * B + 2) P false
    (fun i hi => t4Out_getD_T2lo B P _ i hi)
  have sd4 := c5_seedX2 (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t4Out B P (t0 :: t1 :: TL2)) (t4Out_getD_T2FT B P _)
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at sd4
  have sd5 := w5_seedT3 (t4Out B P (t0 :: t1 :: TL2)) (2 * B + 2 * P + 4) (P + 1)
    false (fun i hi => t4Out_getD_T3lo B P _ i hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at sd5
  have h6 := t4Out_getD_T3FT B P (t0 :: t1 :: TL2)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h6
  have sd6 := c5_seedX3 (s := true) (p := 2 * B + 4 * P + 6)
    (T := t4Out B P (t0 :: t1 :: TL2)) h6
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at sd6
  have sd7 := c5_seedHops (s := false) (p := 2 * B + 4 * P + 8)
    (T := t4Out B P (t0 :: t1 :: TL2))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at sd7
  have sd8 := w5_seedFill (t4Out B P (t0 :: t1 :: TL2)) (2 * B + 4 * P + 12) (B + 2)
    false (fun i hi => t4Out_getD_fill4_lo B P _ i hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at sd8
  have sd9 := c5_seedLive (s := false) (p := 4 * B + 4 * P + 16)
    (T := t4Out B P (t0 :: t1 :: TL2)) (t4Out_getD_liveLo B P _)
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at sd9
  have sd10 := c5_seedWrites (s := true) (p := 4 * B + 4 * P + 20)
    (T := t4Out B P (t0 :: t1 :: TL2))
  rw [t4Out_seed1 B P t0 t1 TL2,
    show 4 * B + 4 * P + 20 + 1 = 4 * B + 4 * P + 21 from by omega,
    t4Out_seed2 B P t1 TL2] at sd10
  -- Rounds.
  have rr := t5_rounds B P TL2 P true (le_refl _) (by omega)
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
  have eg1 := w5_T1r (t5T B P P P (c0 :: c1 :: R2)) 0 B
    (if P = 0 then true else false) (fun i hi => by
    simpa using t5T_getD_T1lo B P P P _ i hi)
  simp only [Nat.zero_add] at eg1
  have eg2 := c5_X1r (s := if B = 0 then (if P = 0 then true else false) else true)
    (p := 2 * B) (T := t5T B P P P (c0 :: c1 :: R2)) (t5T_getD_T1FT B P P P _)
  have eg3 := w5_skipMk (t5T B P P P (c0 :: c1 :: R2)) (2 * B + 2) P false
    (fun i hi => ⟨t5T_getD_Smark_lo B P P P _ i hi, t5T_getD_Smark_hi B P P P _ i hi⟩)
  have eg4 := c5_exhaust (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t5T B P P P (c0 :: c1 :: R2)) (t5T_getD_SFT B P P P _ (le_refl _))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at eg4
  have eg5 := w5_T3e (t5T B P P P (c0 :: c1 :: R2)) (2 * B + 2 * P + 4) (P + 1) false
    (fun i hi => t5T_getD_T3lo B P P P _ i (le_refl _) hi)
  rw [show 2 * B + 2 * P + 4 + 2 * (P + 1) = 2 * B + 4 * P + 6 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at eg5
  have h7 := t5T_getD_T3FT B P P P (c0 :: c1 :: R2) (le_refl _)
  rw [show 2 * B + 2 * P + 4 + (2 * P + 2) = 2 * B + 4 * P + 6 from by omega] at h7
  have eg6 := c5_X3e (s := true) (p := 2 * B + 4 * P + 6)
    (T := t5T B P P P (c0 :: c1 :: R2)) h7
  rw [show 2 * B + 4 * P + 6 + 2 = 2 * B + 4 * P + 8 from by omega] at eg6
  have eg7 := c5_hopsE (s := false) (p := 2 * B + 4 * P + 8)
    (T := t5T B P P P (c0 :: c1 :: R2))
  rw [show 2 * B + 4 * P + 8 + 4 = 2 * B + 4 * P + 12 from by omega] at eg7
  have eg8 := w5_fillE (t5T B P P P (c0 :: c1 :: R2)) (2 * B + 4 * P + 12) (B + 2)
    false (fun i hi => t5T_getD_fill4_lo B P P P _ i (le_refl _) hi)
  rw [show 2 * B + 4 * P + 12 + 2 * (B + 2) = 4 * B + 4 * P + 16 from by omega,
    if_neg (show ¬(B + 2 = 0) from by omega)] at eg8
  have eg9 := c5_liveE (s := false) (p := 4 * B + 4 * P + 16)
    (T := t5T B P P P (c0 :: c1 :: R2)) (t5T_getD_liveLo B P P P _ (le_refl _))
  rw [show 4 * B + 4 * P + 16 + 4 = 4 * B + 4 * P + 20 from by omega] at eg9
  have eg10 := w5_skipFe (t5T B P P P (c0 :: c1 :: R2)) (4 * B + 4 * P + 20) P true
    (fun i hi => ⟨t5T_getD_fill_lo B P P P _ i (le_refl _) hi,
      t5T_getD_fill_hi B P P P _ i (le_refl _) hi⟩)
  have eg11 := c5_advE (s := if P = 0 then true else false)
    (p := 4 * B + 4 * P + 20 + 2 * P) (T := t5T B P P P (c0 :: c1 :: R2))
    (t5T_getD_frontier_lo B P P P _ (le_refl _))
    (t5T_getD_frontier_hi B P P P _ (le_refl _))
  rw [t5T_adv1 B P P P c0 c1 R2 (le_refl _), t5T_adv2 B P P P c0 c1 R2 (le_refl _),
    t5A_writeV B P P P true false c1 R2 (le_refl _), t5A_fold B P P P R2,
    t5T_M B P R2] at eg11
  -- Heal.
  have hl1 := w5_T1h (t5H B P 0 R2) 0 B false (fun i hi => by
    simpa using t5H_getD_T1lo B P 0 R2 i hi)
  simp only [Nat.zero_add] at hl1
  have hl2 := c5_X1h (s := if B = 0 then false else true) (p := 2 * B)
    (T := t5H B P 0 R2) (t5H_getD_T1FT B P 0 R2)
  have hl3 := w5_heal B P R2 P 0 false (by omega)
  rw [show 2 * B + 2 + 2 * 0 = 2 * B + 2 from by omega,
    show (0 + P : ℕ) = P from by omega] at hl3
  have hl4 := c5_done (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t5H B P P R2) (t5H_getD_done B P R2)
  -- Assemble.
  rw [show t5Clock B P
      = 2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4 + (2 * (B + 2) + (4 + (2
        + (t5Rounds B P P + (2 * B + (2 + (2 * P + (2 + (2 * (P + 1) + (2 + (4
        + (2 * (B + 2) + (4 + (2 * P + (4 + (2 * B + (2 + (2 * P
        + 1))))))))))))))))))))))))
      from by rw [t5Clock]; omega,
    run_add, sd1, run_add, sd2, run_add, sd3, run_add, sd4, run_add, sd5, run_add, sd6,
    run_add, sd7, run_add, sd8, run_add, sd9, run_add, sd10, run_add, rr, run_add, eg1,
    run_add, eg2, run_add, eg3, run_add, eg4, run_add, eg5, run_add, eg6, run_add, eg7,
    run_add, eg8, run_add, eg9, run_add, eg10, run_add, eg11, run_add, hl1, run_add,
    hl2, run_add, hl3, hl4, t5H_out B P R2, hR2,
    show (t0 :: t1 :: TL2).drop (2 * P + 4) = TL2.drop (2 * P + 2) from by
      rw [show 2 * P + 4 = 2 * P + 2 + 1 + 1 from by omega]
      rfl]

/-- The done state halts. -/
theorem t5Machine_halt66 : t5Machine.halt ((66 : Fin 68), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT5
