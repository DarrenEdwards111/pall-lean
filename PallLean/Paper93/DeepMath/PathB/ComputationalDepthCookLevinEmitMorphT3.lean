import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT2

/-!
# Cook–Levin M2 emitter — arming morph brick M6: THE `T3` WRITE (front-bank fabric)

The span-overlap resolution, executed.  After M5 the old scaffold (field delimiter,
input region, region 4) is never needed again: `T3`'s span (`P+1` true pairs) is
measured from the FRONT BANK — `T2`'s own extent plus one — and the write advances a
MOVING FRONTIER (`01`) rightward from `T2`'s marker, filling true pairs behind it and
paving the dead suffix with unconditional writes (never reading ahead).  The dead
suffix is a GENERIC TAIL with a length-only hypothesis, consumed two cells per advance
(`List.drop`): no `P`-vs-`B` case splits, and the eventual pass chain telescopes the
drops to exactly where the output region begins.

Round `j`: cross `T1`, mark `T2`'s pair `j`, flow rightward across `T2`'s remainder
and marker, skip the written pairs, and advance the frontier (erase `01 ↦ 11`, write a
fresh `01` two cells on).  Endgame (source spent): ONE more advance — the frontier
STOPS AS `T3`'s marker — then the `00` capacity tail and `T4`'s marker are written in
the same sweep; a final sweep heals `T2`.  Exit: `unaryD B ++ unaryD P ++
jT (P+2) (P+1) ++ 01 ++ (tail.drop (2P+8))` — three targets and `T4`'s marker placed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT3

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2

/-! ## The descriptor family -/

/-- The pass's entry: the two written targets and the dead tail. -/
def t3In (B P : ℕ) (TAIL : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ TAIL)

/-- Brick M5's exit is the entry at the concrete tail. -/
theorem t2Out_t3In (B P : ℕ) (x : List Bool) (E : List Bool) :
    t2Out B P x E
      = t3In B P (List.replicate (6 * B + 16) true ++ ([false, true]
        ++ (xVis x x.length ++ (unaryD (P + 1) ++ E)))) := rfl

/-- Mid-pass: `jS` source pairs marked, `jW` frontier advances done. -/
def t3T (B P jS jW : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (List.replicate (2 * jW) true ++ ([false, true] ++ rest)))))

/-- Post-endgame, pre-heal: `T3` complete, `T4`'s marker placed, source fully marked. -/
def t3M (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD P ++ ([false, true]
    ++ (List.replicate (2 * (P + 1)) true ++ ([false, true]
    ++ ([false, false] ++ ([false, true] ++ rest))))))

/-- Mid-heal: `i` source marks healed. -/
def t3H (B P i : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (2 * i) true ++ (markedD (P - i) ++ ([false, true]
    ++ (List.replicate (2 * (P + 1)) true ++ ([false, true]
    ++ ([false, false] ++ ([false, true] ++ rest)))))))

/-- The exit: `T1`, `T2`, `T3` written, `T4`'s marker placed. -/
def t3Out (B P : ℕ) (rest : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1) ++ ([false, true] ++ rest)))

theorem t3M_H (B P : ℕ) (rest : List Bool) : t3M B P rest = t3H B P 0 rest := rfl

theorem t3H_out (B P : ℕ) (rest : List Bool) : t3H B P P rest = t3Out B P rest := by
  rw [t3H, t3Out, Nat.sub_self, unaryD_eq P, jT,
    show 2 * (P + 2 - (P + 1)) = 2 from by omega]
  simp [markedD, List.append_assoc]

/-! ## The `getD` suite (front zone only — independent of the tail) -/

theorem t3T_getD_T1lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (hi : i < B) :
    (t3T B P jS jW rest).getD (2 * i) false = true := by
  rw [t3T, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3T_getD_T1mark (B P jS jW : ℕ) (rest : List Bool) :
    (t3T B P jS jW rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true
      ++ ([false, true] ++ (List.replicate (2 * jW) true ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3T, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading the source region and beyond. -/
theorem t3T_getD_S (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) :
    (t3T B P jS jW rest).getD (2 * B + 2 + c) false
      = (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
        ++ (List.replicate (2 * jW) true ++ ([false, true] ++ rest))))).getD c false := by
  rw [t3T, getD_append_left_length' _ _ (unaryD_length B)]

theorem t3T_getD_Smark_lo (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t3T B P jS jW rest).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t3T_getD_S, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jS i h

theorem t3T_getD_Smark_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ) (h : i < jS) :
    (t3T B P jS jW rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h2 := t3T_getD_S B P jS jW rest (2 * i + 1)
  rw [show 2 * B + 2 + (2 * i + 1) = 2 * B + 2 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jS i h

theorem t3T_getD_Sdata (B P jS jW : ℕ) (rest : List Bool) (c : ℕ)
    (hjS : jS ≤ P) (h1 : 2 * jS ≤ c) (h2 : c < 2 * P) :
    (t3T B P jS jW rest).getD (2 * B + 2 + c) false = true := by
  rw [t3T_getD_S, show c = 2 * jS + (c - 2 * jS) from by omega,
    getD_append_left_length' _ _ (markedD_length jS),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3T_getD_SFT_lo (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t3T B P jS jW rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h2 := getD_append_left_length' (markedD jS)
    (List.replicate (2 * (P - jS)) true ++ ([false, true]
      ++ (List.replicate (2 * jW) true ++ ([false, true] ++ rest))))
    (markedD_length jS) (2 * P - 2 * jS) false
  rw [show 2 * jS + (2 * P - 2 * jS) = 2 * P from by omega] at h2
  have h3 := getD_append_left_length' (List.replicate (2 * (P - jS)) true)
    ([false, true] ++ (List.replicate (2 * jW) true ++ ([false, true] ++ rest)))
    List.length_replicate 0 false
  rw [show (2 * P - 2 * jS : ℕ) = 2 * (P - jS) + 0 from by omega] at h2
  rw [t3T_getD_S, h2, h3]
  rfl

/-- Reading the written zone and beyond. -/
theorem t3T_getD_W (B P jS jW : ℕ) (rest : List Bool) (c : ℕ) (hjS : jS ≤ P) :
    (t3T B P jS jW rest).getD (2 * B + 2 * P + 4 + c) false
      = (List.replicate (2 * jW) true ++ ([false, true] ++ rest)).getD c false := by
  rw [t3T, show 2 * B + 2 * P + 4 + c
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + c))) from by omega,
    getD_append_left_length' _ _ (unaryD_length B),
    getD_append_left_length' _ _ (markedD_length jS),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t3T_getD_Wdata (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t3T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * i) false = true := by
  rw [t3T_getD_W B P jS jW rest (2 * i) hjS,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3T_getD_Wdata_hi (B P jS jW : ℕ) (rest : List Bool) (i : ℕ)
    (hjS : jS ≤ P) (hi : i < jW) :
    (t3T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * i + 1) false = true := by
  have h := t3T_getD_W B P jS jW rest (2 * i + 1) hjS
  rw [show 2 * B + 2 * P + 4 + (2 * i + 1) = 2 * B + 2 * P + 4 + 2 * i + 1
    from by omega] at h
  rw [h, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3T_getD_frontier (B P jS jW : ℕ) (rest : List Bool) (hjS : jS ≤ P) :
    (t3T B P jS jW rest).getD (2 * B + 2 * P + 4 + 2 * jW) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * jW) true)
    ([false, true] ++ rest) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t3T_getD_W B P jS jW rest (2 * jW) hjS, h2]
  rfl

/-! ## The write lemmas -/

/-- Mark the source's next pair. -/
theorem t3T_markSrc (B P jS jW : ℕ) (rest : List Bool) (hjS : jS < P) :
    writeAt (t3T B P jS jW rest) (2 * B + 2 + 2 * jS + 1) false
      = t3T B P (jS + 1) jW rest := by
  rw [writeAt_of_lt false (by
      simp only [t3T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3T,
    show 2 * B + 2 + 2 * jS + 1 = 2 * B + 2 + (2 * jS + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    show List.replicate (2 * (P - jS)) true
      = true :: true :: List.replicate (2 * (P - jS - 1)) true from by
        rw [show 2 * (P - jS) = 2 * (P - jS - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t3T, ← markedD_snoc, show P - (jS + 1) = P - jS - 1 from by omega]
  simp [List.append_assoc]

/-- Mid-advance: the erased frontier merged into the written zone, two raw cells. -/
def t3A (B P jS jW : ℕ) (u v : Bool) (rest : List Bool) : List Bool :=
  unaryD B ++ (markedD jS ++ (List.replicate (2 * (P - jS)) true ++ ([false, true]
    ++ (List.replicate (2 * jW + 2) true ++ (u :: v :: rest)))))

/-- Advance, write 1: erase the frontier (`01 ↦ 11`). -/
theorem t3T_adv1 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t3T B P jS jW (r0 :: r1 :: rest)) (2 * B + 2 * P + 4 + 2 * jW) true
      = t3A B P jS jW r0 r1 rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW) true)
    ([false, true] ++ (r0 :: r1 :: rest)) List.length_replicate 0 true
  simp only [Nat.add_zero] at hset
  rw [writeAt_of_lt true (by
      simp only [t3T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3T,
    show 2 * B + 2 * P + 4 + 2 * jW
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + 2 * jW))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    hset]
  simp only [List.cons_append, List.set_cons_zero]
  rw [t3A, show (2 * jW + 2 : ℕ) = 2 * jW + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * jW + 1), List.replicate_succ' (n := 2 * jW)]
  simp

/-- Advance, write 2: the fresh marker's `0`. -/
theorem t3T_adv2 (B P jS jW : ℕ) (r0 r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t3A B P jS jW r0 r1 rest) (2 * B + 2 * P + 4 + 2 * jW + 2) false
      = t3A B P jS jW false r1 rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW + 2) true)
    (r0 :: r1 :: rest) List.length_replicate 0 false
  simp only [Nat.add_zero] at hset
  rw [writeAt_of_lt false (by
      simp only [t3A, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3A,
    show 2 * B + 2 * P + 4 + 2 * jW + 2
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * jW + 2)))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    hset]
  rw [t3A]
  rfl

/-- Advance, write 3: the fresh marker's `1`. -/
theorem t3T_adv3 (B P jS jW : ℕ) (r1 : Bool) (rest : List Bool) (hjS : jS ≤ P) :
    writeAt (t3A B P jS jW false r1 rest) (2 * B + 2 * P + 4 + 2 * jW + 3) true
      = t3T B P jS (jW + 1) rest := by
  have hset := set_append_left_length' (List.replicate (2 * jW + 2) true)
    (false :: r1 :: rest) List.length_replicate 1 true
  rw [writeAt_of_lt true (by
      simp only [t3A, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3A,
    show 2 * B + 2 * P + 4 + 2 * jW + 3
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * jW + 2 + 1)))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    hset]
  simp only [List.set_cons_succ, List.set_cons_zero]
  rw [t3T, show (2 * (jW + 1) : ℕ) = 2 * jW + 2 from by omega]
  simp

/-- Heal one source mark. -/
theorem t3H_heal (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    writeAt (t3H B P i rest) (2 * B + 2 + 2 * i + 1) true = t3H B P (i + 1) rest := by
  rw [writeAt_of_lt true (by
      simp only [t3H, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3H,
    show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t3H, show P - (i + 1) = P - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ### Heal reads -/

theorem t3H_getD_T1lo (B P i : ℕ) (rest : List Bool) (k : ℕ) (hk : k < B) :
    (t3H B P i rest).getD (2 * k) false = true := by
  rw [t3H, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3H_getD_T1mark (B P i : ℕ) (rest : List Bool) :
    (t3H B P i rest).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (List.replicate (2 * i) true ++ (markedD (P - i)
      ++ ([false, true] ++ (List.replicate (2 * (P + 1)) true ++ ([false, true]
      ++ ([false, false] ++ ([false, true] ++ rest))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3H, unaryD_eq, List.append_assoc, h]
  rfl

theorem t3H_getD_lo (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t3H B P i rest).getD (2 * B + 2 + 2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (List.replicate (2 * (P + 1)) true
      ++ ([false, true] ++ ([false, false] ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3H, show 2 * B + 2 + 2 * i = 2 * B + 2 + (2 * i) from rfl,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t3H_getD_hi (B P i : ℕ) (rest : List Bool) (hi : i < P) :
    (t3H B P i rest).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ ([false, true] ++ (List.replicate (2 * (P + 1)) true
      ++ ([false, true] ++ ([false, false] ++ ([false, true] ++ rest))))))
    List.length_replicate 1 false
  rw [t3H, show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t3H_getD_done (B P : ℕ) (rest : List Bool) :
    (t3H B P P rest).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    (markedD (P - P) ++ ([false, true] ++ (List.replicate (2 * (P + 1)) true
      ++ ([false, true] ++ ([false, false] ++ ([false, true] ++ rest))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3H, show 2 * B + 2 + 2 * P = 2 * B + 2 + (2 * P) from rfl,
    getD_append_left_length' _ _ (unaryD_length B), h, Nat.sub_self]
  rfl

/-- Write into the raw tail at offset `k` past the frontier. -/
theorem t3T_writeRest (B P jS jW k : ℕ) (w : Bool) (rest : List Bool)
    (hjS : jS ≤ P) (hk : k < rest.length) :
    writeAt (t3T B P jS jW rest) (2 * B + 2 * P + 4 + 2 * jW + 2 + k) w
      = t3T B P jS jW (rest.set k w) := by
  rw [writeAt_of_lt w (by
      simp only [t3T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, unaryD_length]
      omega), t3T,
    show 2 * B + 2 * P + 4 + 2 * jW + 2 + k
      = 2 * B + 2 + (2 * jS + (2 * (P - jS) + (2 + (2 * jW + (2 + k)))))
      from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jS),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  rw [t3T]

/-- The endgame's written tail is the pre-heal descriptor. -/
theorem t3T_egM (B P : ℕ) (rest : List Bool) :
    t3T B P P (P + 1) (false :: false :: false :: true :: rest) = t3M B P rest := by
  rw [t3T, t3M, Nat.sub_self]
  simp

/-! ## Seed reads and writes -/

theorem t3In_getD_T1lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < B) :
    (t3In B P TL).getD (2 * i) false = true := by
  rw [t3In, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3In_getD_T1mark (B P : ℕ) (TL : List Bool) :
    (t3In B P TL).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (unaryD P ++ TL)) List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3In, unaryD_eq B, List.append_assoc, h]
  rfl

theorem t3In_getD_T2 (B P : ℕ) (TL : List Bool) (c : ℕ) :
    (t3In B P TL).getD (2 * B + 2 + c) false = (unaryD P ++ TL).getD c false := by
  rw [t3In, getD_append_left_length' _ _ (unaryD_length B)]

theorem t3In_getD_T2lo (B P : ℕ) (TL : List Bool) (i : ℕ) (hi : i < P) :
    (t3In B P TL).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t3In_getD_T2, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t3In_getD_T2mark (B P : ℕ) (TL : List Bool) :
    (t3In B P TL).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ TL) List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t3In_getD_T2, unaryD_eq, List.append_assoc, h]
  rfl

theorem t3In_seed1 (B P : ℕ) (t0 t1 : Bool) (TL : List Bool) :
    writeAt (t3In B P (t0 :: t1 :: TL)) (2 * B + 2 * P + 4) false
      = t3In B P (false :: t1 :: TL) := by
  rw [writeAt_of_lt false (by
      simp only [t3In, List.length_append, List.length_cons, unaryD_length]
      omega), t3In,
    show 2 * B + 2 * P + 4 = 2 * B + 2 + (2 * P + 2 + 0) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P)]
  rw [t3In]
  rfl

theorem t3In_seed2 (B P : ℕ) (t1 : Bool) (TL : List Bool) :
    writeAt (t3In B P (false :: t1 :: TL)) (2 * B + 2 * P + 5) true
      = t3T B P 0 0 TL := by
  rw [writeAt_of_lt true (by
      simp only [t3In, List.length_append, List.length_cons, unaryD_length]
      omega), t3In,
    show 2 * B + 2 * P + 5 = 2 * B + 2 + (2 * P + 2 + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P)]
  simp only [List.set_cons_succ, List.set_cons_zero]
  rw [t3T, Nat.sub_zero]
  simp [unaryD_eq, markedD]

/-! ## The `T3` machine

Control: `State = Fin 43 × Bool`.  Seed `0-7` (cross `T1`, cross `T2`, plant the
frontier, reset), round `8-22` (cross `T1`, mark source pair `j`, flow across the
source remainder and its marker, skip the written pairs, 3-write advance, reset),
endgame `23-34` (source spent: final advance — the frontier stops as `T3`'s marker —
then `00` and `T4`'s marker, reset), heal `35-39`, done `41`, dead `42`. -/

def t3Machine : Machine where
  State := Fin 43 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 41) || decide (s.1 = 42)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, b), none, 1) else ((2, b), none, 1))
    else if s.1 = 1 then ((0, s.2), none, 1)
    else if s.1 = 2 then ((3, s.2), none, 1)
    else if s.1 = 3 then (if b then ((4, b), none, 1) else ((5, b), none, 1))
    else if s.1 = 4 then ((3, s.2), none, 1)
    else if s.1 = 5 then ((6, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some false, 1)
    else if s.1 = 7 then ((8, s.2), some true, 3)
    else if s.1 = 8 then (if b then ((9, b), none, 1) else ((10, b), none, 1))
    else if s.1 = 9 then ((8, s.2), none, 1)
    else if s.1 = 10 then ((11, s.2), none, 1)
    else if s.1 = 11 then (if b then ((12, b), none, 1) else ((23, b), none, 1))
    else if s.1 = 12 then
      (if b then ((13, s.2), some false, 1) else ((11, s.2), none, 1))
    else if s.1 = 13 then (if b then ((14, b), none, 1) else ((15, b), none, 1))
    else if s.1 = 14 then ((13, s.2), none, 1)
    else if s.1 = 15 then ((16, s.2), none, 1)
    else if s.1 = 16 then (if b then ((17, b), none, 1) else ((18, b), none, 1))
    else if s.1 = 17 then ((16, s.2), none, 1)
    else if s.1 = 18 then ((19, s.2), none, 0)
    else if s.1 = 19 then ((20, s.2), some true, 1)
    else if s.1 = 20 then ((21, s.2), none, 1)
    else if s.1 = 21 then ((22, s.2), some false, 1)
    else if s.1 = 22 then ((8, s.2), some true, 3)
    else if s.1 = 23 then ((24, s.2), none, 1)
    else if s.1 = 24 then (if b then ((25, b), none, 1) else ((26, b), none, 1))
    else if s.1 = 25 then ((24, s.2), none, 1)
    else if s.1 = 26 then ((27, s.2), none, 0)
    else if s.1 = 27 then ((28, s.2), some true, 1)
    else if s.1 = 28 then ((29, s.2), none, 1)
    else if s.1 = 29 then ((30, s.2), some false, 1)
    else if s.1 = 30 then ((31, s.2), some true, 1)
    else if s.1 = 31 then ((32, s.2), some false, 1)
    else if s.1 = 32 then ((33, s.2), some false, 1)
    else if s.1 = 33 then ((34, s.2), some false, 1)
    else if s.1 = 34 then ((35, s.2), some true, 3)
    else if s.1 = 35 then (if b then ((36, b), none, 1) else ((37, b), none, 1))
    else if s.1 = 36 then ((35, s.2), none, 1)
    else if s.1 = 37 then ((38, s.2), none, 1)
    else if s.1 = 38 then (if b then ((39, b), none, 1) else ((41, b), none, 2))
    else if s.1 = 39 then
      (if b then ((42, s.2), none, 2) else ((38, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 41)

theorem init_t3 (x : List Bool) : init t3Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem s3_0T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_0F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_1 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_3T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_3F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_5 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_6 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(6, s), p, T⟩ = ⟨(7, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_7 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(7, s), p, T⟩ = ⟨(8, s), 0, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_8T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(8, s), p, T⟩ = ⟨(9, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_8F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(8, s), p, T⟩ = ⟨(10, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_9 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(9, s), p, T⟩ = ⟨(8, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_10 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(10, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_11T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(11, s), p, T⟩ = ⟨(12, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_11F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(11, s), p, T⟩ = ⟨(23, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_12T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_12F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(12, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_13T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(13, s), p, T⟩ = ⟨(14, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_13F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(13, s), p, T⟩ = ⟨(15, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_14 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(14, s), p, T⟩ = ⟨(13, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_15 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(15, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_16T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(16, s), p, T⟩ = ⟨(17, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_16F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(16, s), p, T⟩ = ⟨(18, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_17 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(17, s), p, T⟩ = ⟨(16, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_18 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(18, s), p, T⟩ = ⟨(19, s), p - 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_19 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(19, s), p, T⟩ = ⟨(20, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_20 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(20, s), p, T⟩ = ⟨(21, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_21 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(21, s), p, T⟩ = ⟨(22, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_22 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(22, s), p, T⟩ = ⟨(8, s), 0, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_23 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(23, s), p, T⟩ = ⟨(24, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_24T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(24, s), p, T⟩ = ⟨(25, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_24F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(24, s), p, T⟩ = ⟨(26, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_25 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(25, s), p, T⟩ = ⟨(24, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_26 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(26, s), p, T⟩ = ⟨(27, s), p - 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_27 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(27, s), p, T⟩ = ⟨(28, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_28 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(28, s), p, T⟩ = ⟨(29, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_29 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(29, s), p, T⟩ = ⟨(30, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_30 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(30, s), p, T⟩ = ⟨(31, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_31 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(31, s), p, T⟩ = ⟨(32, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_32 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(32, s), p, T⟩ = ⟨(33, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_33 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(33, s), p, T⟩ = ⟨(34, s), p + 1, writeAt T p false⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_34 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(34, s), p, T⟩ = ⟨(35, s), 0, writeAt T p true⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_35T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(35, s), p, T⟩ = ⟨(36, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_35F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(35, s), p, T⟩ = ⟨(37, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_36 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(36, s), p, T⟩ = ⟨(35, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_37 {s : Bool} {p : ℕ} {T : List Bool} :
    step t3Machine ⟨(37, s), p, T⟩ = ⟨(38, s), p + 1, T⟩ := by
  simp only [step, t3Machine, moveHead]; rfl

theorem s3_38T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t3Machine ⟨(38, s), p, T⟩ = ⟨(39, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_38F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(38, s), p, T⟩ = ⟨(41, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

theorem s3_39F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t3Machine ⟨(39, s), p, T⟩ = ⟨(38, s), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t3Machine, moveHead, h]

/-! ### Composites -/

theorem y3_skipT1s {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_0T h1, s3_1]

theorem y3_crossT1s {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_0F h1, s3_2]

theorem y3_skipT2s {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_3T h1, s3_4]

theorem y3_crossT2s {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_3F h1, s3_5]

theorem y3_seed {s : Bool} {p : ℕ} {T : List Bool} :
    run t3Machine 2 ⟨(6, s), p, T⟩
      = ⟨(8, s), 0, writeAt (writeAt T p false) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, s3_6, s3_7]

theorem y3_skipT1r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(8, s), p, T⟩ = ⟨(8, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_8T h1, s3_9]

theorem y3_crossT1r {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(8, s), p, T⟩ = ⟨(11, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_8F h1, s3_10]

theorem y3_skipSrc {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t3Machine 2 ⟨(11, s), p, T⟩ = ⟨(11, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_11T h1, s3_12F h2]

theorem y3_markSrc {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t3Machine 2 ⟨(11, s), p, T⟩
      = ⟨(13, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, s3_11T h1, s3_12T h2]

theorem y3_skipRest {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(13, s), p, T⟩ = ⟨(13, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_13T h1, s3_14]

theorem y3_crossSFT {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(13, s), p, T⟩ = ⟨(16, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_13F h1, s3_15]

theorem y3_skipWr {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(16, s), p, T⟩ = ⟨(16, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_16T h1, s3_17]

theorem y3_advance {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 6 ⟨(16, s), p, T⟩
      = ⟨(8, false), 0,
          writeAt (writeAt (writeAt T p true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_zero,
    s3_16F h1, s3_18, show p + 1 - 1 = p from by omega, s3_19, s3_20, s3_21, s3_22]

theorem y3_bound {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(11, s), p, T⟩ = ⟨(24, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_11F h1, s3_23]

theorem y3_skipWrE {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(24, s), p, T⟩ = ⟨(24, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_24T h1, s3_25]

theorem y3_finale {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 10 ⟨(24, s), p, T⟩
      = ⟨(35, false), 0,
          writeAt (writeAt (writeAt (writeAt (writeAt (writeAt (writeAt T
            p true) (p + 2) false) (p + 3) true) (p + 4) false) (p + 5) false)
            (p + 6) false) (p + 7) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ, run_succ,
    run_succ, run_succ, run_zero,
    s3_24F h1, s3_26, show p + 1 - 1 = p from by omega, s3_27, s3_28, s3_29, s3_30,
    s3_31, s3_32, s3_33, s3_34]

theorem y3_skipT1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t3Machine 2 ⟨(35, s), p, T⟩ = ⟨(35, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_35T h1, s3_36]

theorem y3_crossT1h {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t3Machine 2 ⟨(35, s), p, T⟩ = ⟨(38, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, s3_35F h1, s3_37]

theorem y3_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t3Machine 2 ⟨(38, s), p, T⟩ = ⟨(38, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, s3_38T h1, s3_39F h2]

theorem y3_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    run t3Machine 1 ⟨(38, s), p, T⟩ = ⟨(41, false), p, T⟩ := by
  rw [run_succ, run_zero, s3_38F h]

/-! ### Scan run-invariants -/

theorem z3_skipT1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipT1s (h k (by omega))]
    rfl

theorem z3_skipT2s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipT2s (h k (by omega))]
    rfl

theorem z3_skipT1r (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(8, s), q, T⟩
      = ⟨(8, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipT1r (h k (by omega))]
    rfl

theorem z3_skipSrc (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t3Machine (2 * k) ⟨(11, s), q, T⟩
      = ⟨(11, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipSrc hk.1 hk.2]
    rfl

theorem z3_skipRest (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(13, s), q, T⟩
      = ⟨(13, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipRest (h k (by omega))]
    rfl

theorem z3_skipWr (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(16, s), q, T⟩
      = ⟨(16, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipWr (h k (by omega))]
    rfl

theorem z3_skipWrE (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(24, s), q, T⟩
      = ⟨(24, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipWrE (h k (by omega))]
    rfl

theorem z3_skipT1h (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t3Machine (2 * k) ⟨(35, s), q, T⟩
      = ⟨(35, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), y3_skipT1h (h k (by omega))]
    rfl

/-- Heal the source, tape evolving. -/
theorem z3_heal (B P : ℕ) (rest : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P →
    run t3Machine (2 * k) ⟨(38, s), 2 * B + 2 + 2 * i, t3H B P i rest⟩
      = ⟨(38, if k = 0 then s else true), 2 * B + 2 + 2 * (i + k),
          t3H B P (i + k) rest⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      y3_heal (t3H_getD_lo B P i rest (by omega)) (t3H_getD_hi B P i rest (by omega)),
      t3H_heal B P i rest (by omega),
      show 2 * B + 2 + 2 * i + 2 = 2 * B + 2 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The round invariant -/

/-- **One transcription round**: mark source pair `j`, advance the frontier. -/
theorem t3_round (B P j : ℕ) (r0 r1 : Bool) (rest : List Bool) (s : Bool)
    (hj : j < P) :
    run t3Machine (2 * B + 2 * P + 2 * j + 10)
      ⟨(8, s), 0, t3T B P j j (r0 :: r1 :: rest)⟩
      = ⟨(8, false), 0, t3T B P (j + 1) (j + 1) rest⟩ := by
  have st1 := z3_skipT1r (t3T B P j j (r0 :: r1 :: rest)) 0 B s (fun i hi => by
    simpa using t3T_getD_T1lo B P j j (r0 :: r1 :: rest) i hi)
  simp only [Nat.zero_add] at st1
  have st2 := y3_crossT1r (s := if B = 0 then s else true) (p := 2 * B)
    (T := t3T B P j j (r0 :: r1 :: rest)) (t3T_getD_T1mark B P j j _)
  have st3 := z3_skipSrc (t3T B P j j (r0 :: r1 :: rest)) (2 * B + 2) j false
    (fun i hi => ⟨t3T_getD_Smark_lo B P j j _ i hi, t3T_getD_Smark_hi B P j j _ i hi⟩)
  have h4b : (t3T B P j j (r0 :: r1 :: rest)).getD (2 * B + 2 + 2 * j + 1) false
      = true := by
    have h := t3T_getD_Sdata B P j j (r0 :: r1 :: rest) (2 * j + 1) (by omega)
      (by omega) (by omega)
    rwa [show 2 * B + 2 + (2 * j + 1) = 2 * B + 2 + 2 * j + 1 from by omega] at h
  have st4 := y3_markSrc (s := if j = 0 then false else true) (p := 2 * B + 2 + 2 * j)
    (T := t3T B P j j (r0 :: r1 :: rest))
    (t3T_getD_Sdata B P j j _ (2 * j) (by omega) (by omega) (by omega)) h4b
  rw [t3T_markSrc B P j j _ hj] at st4
  have st5 := z3_skipRest (t3T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 + 2 * j + 2)
    (P - j - 1) true (fun i hi => by
      have h := t3T_getD_Sdata B P (j + 1) j (r0 :: r1 :: rest) (2 * j + 2 + 2 * i)
        (by omega) (by omega) (by omega)
      rwa [show 2 * B + 2 + (2 * j + 2 + 2 * i) = 2 * B + 2 + 2 * j + 2 + 2 * i
        from by omega] at h)
  rw [show 2 * B + 2 + 2 * j + 2 + 2 * (P - j - 1) = 2 * B + 2 + 2 * P from by omega,
    ite_self] at st5
  have st6 := y3_crossSFT (s := true) (p := 2 * B + 2 + 2 * P)
    (T := t3T B P (j + 1) j (r0 :: r1 :: rest))
    (t3T_getD_SFT_lo B P (j + 1) j _ (by omega))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at st6
  have st7 := z3_skipWr (t3T B P (j + 1) j (r0 :: r1 :: rest)) (2 * B + 2 * P + 4) j
    false (fun i hi => t3T_getD_Wdata B P (j + 1) j _ i (by omega) hi)
  have st8 := y3_advance (s := if j = 0 then false else true)
    (p := 2 * B + 2 * P + 4 + 2 * j) (T := t3T B P (j + 1) j (r0 :: r1 :: rest))
    (t3T_getD_frontier B P (j + 1) j _ (by omega))
  rw [t3T_adv1 B P (j + 1) j r0 r1 rest (by omega),
    t3T_adv2 B P (j + 1) j r0 r1 rest (by omega),
    t3T_adv3 B P (j + 1) j r1 rest (by omega)] at st8
  rw [show 2 * B + 2 * P + 2 * j + 10
      = 2 * B + (2 + (2 * j + (2 + (2 * (P - j - 1) + (2 + (2 * j + 6))))))
      from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, st8]

/-! ## The rounds, the endgame, the run -/

/-- The cumulative clock of the first `k` rounds. -/
def t3Rounds (B P : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t3Rounds B P k + (2 * B + 2 * P + 2 * k + 10)

theorem t3_rounds (B P : ℕ) (rest : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ P) (hlen : 2 * k ≤ rest.length) :
    run t3Machine (t3Rounds B P k) ⟨(8, s), 0, t3T B P 0 0 rest⟩
      = ⟨(8, if k = 0 then s else false), 0, t3T B P k k (rest.drop (2 * k))⟩ := by
  induction k with
  | zero => simp [t3Rounds]
  | succ k ih =>
    rw [show t3Rounds B P (k + 1) = t3Rounds B P k + (2 * B + 2 * P + 2 * k + 10)
        from rfl,
      run_add, ih (by omega) (by omega),
      List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega),
      show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
      t3_round B P k _ _ _ _ (by omega), if_neg (by omega)]

/-- The pass's exact clock. -/
def t3Clock (B P : ℕ) : ℕ :=
  (2 * B + 2 * P + 6) + (t3Rounds B P P + ((2 * B + 4 * P + 14) + (2 * B + 2 * P + 3)))

set_option maxHeartbeats 1600000 in
/-- **THE `T3` WRITE RUNS**: from the two-target front and ANY dead tail of length at
least `2P+8`, the pass halts DONE with `T3` written, `T4`'s marker placed, and the
source healed — consuming exactly `2P+8` tail cells. -/
theorem t3Machine_run (B P : ℕ) (TAIL : List Bool) (hlen : 2 * P + 8 ≤ TAIL.length) :
    run t3Machine (t3Clock B P) (init t3Machine (t3In B P TAIL))
      = ⟨(41, false), 2 * B + 2 + 2 * P, t3Out B P (TAIL.drop (2 * P + 8))⟩ := by
  obtain ⟨t0, TAIL1, rfl⟩ : ∃ a l, TAIL = a :: l := by
    cases TAIL with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  obtain ⟨t1, TL2, rfl⟩ : ∃ a l, TAIL1 = a :: l := by
    cases TAIL1 with
    | nil => simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  have hlen2 : 2 * P + 6 ≤ TL2.length := by
    simp only [List.length_cons] at hlen
    omega
  rw [init_t3]
  -- Seed.
  have sd1 := z3_skipT1s (t3In B P (t0 :: t1 :: TL2)) 0 B false (fun i hi => by
    simpa using t3In_getD_T1lo B P _ i hi)
  simp only [Nat.zero_add] at sd1
  have sd2 := y3_crossT1s (s := if B = 0 then false else true) (p := 2 * B)
    (T := t3In B P (t0 :: t1 :: TL2)) (t3In_getD_T1mark B P _)
  have sd3 := z3_skipT2s (t3In B P (t0 :: t1 :: TL2)) (2 * B + 2) P false
    (fun i hi => t3In_getD_T2lo B P _ i hi)
  have sd4 := y3_crossT2s (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t3In B P (t0 :: t1 :: TL2)) (t3In_getD_T2mark B P _)
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at sd4
  have sd5 := y3_seed (s := false) (p := 2 * B + 2 * P + 4)
    (T := t3In B P (t0 :: t1 :: TL2))
  rw [t3In_seed1 B P t0 t1 TL2,
    show 2 * B + 2 * P + 4 + 1 = 2 * B + 2 * P + 5 from by omega,
    t3In_seed2 B P t1 TL2] at sd5
  -- Rounds.
  have rr := t3_rounds B P TL2 P false (le_refl _) (by omega)
  rw [ite_self] at rr
  -- Endgame: expose the six consumed tail cells as variables.
  have hlen3 : 6 ≤ (TL2.drop (2 * P)).length := by rw [List.length_drop]; omega
  obtain ⟨c0, R1, h0⟩ : ∃ a l, TL2.drop (2 * P) = a :: l := by
    cases h : TL2.drop (2 * P) with
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
  have hchain : TL2.drop (2 * P) = c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6 := by
    rw [h0, h1, h2, h3, h4, h5]
  have hR6 : R6 = TL2.drop (2 * P + 6) := by
    have h := congrArg (List.drop 6) hchain
    simp only [List.drop_drop] at h
    simpa using h.symm
  rw [hchain] at rr
  have eg1 := z3_skipT1r (t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6)) 0 B
    false (fun i hi => by simpa using t3T_getD_T1lo B P P P _ i hi)
  simp only [Nat.zero_add] at eg1
  have eg2 := y3_crossT1r (s := if B = 0 then false else true) (p := 2 * B)
    (T := t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (t3T_getD_T1mark B P P P _)
  have eg3 := z3_skipSrc (t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (2 * B + 2) P false
    (fun i hi => ⟨t3T_getD_Smark_lo B P P P _ i hi, t3T_getD_Smark_hi B P P P _ i hi⟩)
  have eg4 := y3_bound (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (t3T_getD_SFT_lo B P P P _ (le_refl _))
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at eg4
  have eg5 := z3_skipWrE (t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (2 * B + 2 * P + 4) P false
    (fun i hi => t3T_getD_Wdata B P P P _ i (le_refl _) hi)
  have eg6 := y3_finale (s := if P = 0 then false else true)
    (p := 2 * B + 2 * P + 4 + 2 * P)
    (T := t3T B P P P (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: R6))
    (t3T_getD_frontier B P P P _ (le_refl _))
  rw [t3T_adv1 B P P P c0 c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    t3T_adv2 B P P P c0 c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    t3T_adv3 B P P P c1 (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _),
    show 2 * B + 2 * P + 4 + 2 * P + 4 = 2 * B + 2 * P + 4 + 2 * (P + 1) + 2 + 0
      from by omega,
    t3T_writeRest B P P (P + 1) 0 false (c2 :: c3 :: c4 :: c5 :: R6) (le_refl _)
      (by simp),
    show ((c2 :: c3 :: c4 :: c5 :: R6).set 0 false : List Bool)
      = false :: c3 :: c4 :: c5 :: R6 from rfl,
    show 2 * B + 2 * P + 4 + 2 * P + 5 = 2 * B + 2 * P + 4 + 2 * (P + 1) + 2 + 1
      from by omega,
    t3T_writeRest B P P (P + 1) 1 false (false :: c3 :: c4 :: c5 :: R6) (le_refl _)
      (by simp),
    show ((false :: c3 :: c4 :: c5 :: R6).set 1 false : List Bool)
      = false :: false :: c4 :: c5 :: R6 from rfl,
    show 2 * B + 2 * P + 4 + 2 * P + 6 = 2 * B + 2 * P + 4 + 2 * (P + 1) + 2 + 2
      from by omega,
    t3T_writeRest B P P (P + 1) 2 false (false :: false :: c4 :: c5 :: R6) (le_refl _)
      (by simp),
    show ((false :: false :: c4 :: c5 :: R6).set 2 false : List Bool)
      = false :: false :: false :: c5 :: R6 from rfl,
    show 2 * B + 2 * P + 4 + 2 * P + 7 = 2 * B + 2 * P + 4 + 2 * (P + 1) + 2 + 3
      from by omega,
    t3T_writeRest B P P (P + 1) 3 true (false :: false :: false :: c5 :: R6)
      (le_refl _) (by simp),
    show ((false :: false :: false :: c5 :: R6).set 3 true : List Bool)
      = false :: false :: false :: true :: R6 from rfl,
    t3T_egM B P R6, t3M_H B P R6] at eg6
  -- Heal.
  have hl1 := z3_skipT1h (t3H B P 0 R6) 0 B
    false (fun i hi => by simpa using t3H_getD_T1lo B P 0 _ i hi)
  simp only [Nat.zero_add] at hl1
  have hl2 := y3_crossT1h (s := if B = 0 then false else true) (p := 2 * B)
    (T := t3H B P 0 R6)
    (t3H_getD_T1mark B P 0 _)
  have hl3 := z3_heal B P R6 P 0 false
    (by omega)
  rw [show 2 * B + 2 + 2 * 0 = 2 * B + 2 from by omega,
    show (0 + P : ℕ) = P from by omega] at hl3
  have hl4 := y3_done (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t3H B P P R6)
    (t3H_getD_done B P _)
  -- Assemble.
  rw [show t3Clock B P
      = 2 * B + (2 + (2 * P + (2 + (2 + (t3Rounds B P P + (2 * B + (2 + (2 * P + (2
        + (2 * P + (10 + (2 * B + (2 + (2 * P + 1))))))))))))))
      from by rw [t3Clock]; omega,
    run_add, sd1, run_add, sd2, run_add, sd3, run_add, sd4, run_add, sd5, run_add, rr,
    run_add, eg1, run_add, eg2, run_add, eg3, run_add, eg4, run_add, eg5, run_add, eg6,
    run_add, hl1, run_add, hl2, run_add, hl3]
  rw [show (if P = 0 then false else true) = (if P = 0 then false else true) from rfl]
    at hl4
  rw [hl4, t3H_out B P R6, hR6,
    show (t0 :: t1 :: TL2).drop (2 * P + 8) = TL2.drop (2 * P + 6) from by
      rw [show 2 * P + 8 = 2 * P + 6 + 1 + 1 from by omega]
      rfl]

/-- The done state halts. -/
theorem t3Machine_halt41 : t3Machine.halt ((41 : Fin 43), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT3
