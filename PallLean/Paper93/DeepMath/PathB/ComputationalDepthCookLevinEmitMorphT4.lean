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

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4
