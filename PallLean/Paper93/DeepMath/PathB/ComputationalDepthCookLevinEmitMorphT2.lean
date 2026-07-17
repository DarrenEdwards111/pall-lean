import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphFill

/-!
# Cook–Levin M2 emitter — arming morph brick M5 part 1: THE `T2` WRITE'S TAPE ALGEBRA

`T2 = unaryD P`'s marker goes at position `2B+2P+2`, over brick M4's uniform true-field.
Source: region 4 (`unaryD (P+1)`), the FIRST source beyond the input region — the
crossing walks are M2's 4-cell unit walk (`xVis` value pairs can be `00`, so `0`-low
event counting cannot cross it; the unit walk's terminal detect can).  Discipline:
`P+1` rounds transcribe region 4's pairs into frontier marks (pairs `0..P` of the
field), the LAST mark is then fixed into the marker (`10 ↦ 01`, two writes — the
uniform field makes first-unmarked detection unambiguous, no pre-consume phase), and
one rightward mega-heal restores both mark regions (`10 ↦ 11`), leaving region 4
fresh for `T3`.

This part: the descriptor family (`t2T` mid-round, `t2M` post-fix, `t2H1`/`t2H2`
mid-heal, `t2Out` exit), entry/exit identifications, and the full `getD`/write suite.
Part 2 builds the machine over it.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill

/-! ## The descriptor family -/

/-- Mid-round: `jF` frontier marks in the field, `jR` region-4 pairs consumed. -/
def t2T (B P jF jR : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (markedD jF ++ (List.replicate (6 * B + 2 * P + 18 - 2 * jF) true
    ++ ([false, true] ++ (xVis x x.length
    ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
    ++ ([false, true] ++ E)))))))

/-- The unprocessed tape is brick M4's exit (region 4 exposed). -/
theorem t2T_zero (B P : ℕ) (x : List Bool) (E : List Bool) :
    t2T B P 0 0 x E = fillOut B P x (unaryD (P + 1) ++ E) := by
  rw [t2T, fillOut, unaryD_eq (P + 1)]
  simp [markedD, List.append_assoc]

/-- Post-fix: the marker `01` at field pair `P`, frontier marks `0..P-1` unhealed. -/
def t2M (B P : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (markedD P ++ (false :: true :: (List.replicate (6 * B + 16) true
    ++ ([false, true] ++ (xVis x x.length
    ++ (markedD (P + 1) ++ ([false, true] ++ E)))))))

/-- Mid-fix: the last mark's high cell already healed (`10 ↦ 11`). -/
def t2M' (B P : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (markedD P ++ (true :: true :: (List.replicate (6 * B + 16) true
    ++ ([false, true] ++ (xVis x x.length
    ++ (markedD (P + 1) ++ ([false, true] ++ E)))))))

/-- Mid-heal, phase 1: `i` frontier marks healed. -/
def t2H1 (B P i : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (List.replicate (2 * i) true ++ (markedD (P - i)
    ++ (false :: true :: (List.replicate (6 * B + 16) true
    ++ ([false, true] ++ (xVis x x.length
    ++ (markedD (P + 1) ++ ([false, true] ++ E))))))))

/-- Mid-heal, phase 2: frontier healed, `i` region-4 marks healed. -/
def t2H2 (B P i : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (List.replicate (6 * B + 16) true
    ++ ([false, true] ++ (xVis x x.length
    ++ (List.replicate (2 * i) true ++ (markedD (P + 1 - i)
    ++ ([false, true] ++ E)))))))

/-- The pass's exit: `T1` and `T2` done, region 4 fresh again. -/
def t2Out (B P : ℕ) (x : List Bool) (E : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (List.replicate (6 * B + 16) true
    ++ ([false, true] ++ (xVis x x.length ++ (unaryD (P + 1) ++ E)))))

theorem t2M_H1 (B P : ℕ) (x : List Bool) (E : List Bool) :
    t2M B P x E = t2H1 B P 0 x E := by
  rw [t2M, t2H1, Nat.sub_zero]
  rfl

theorem t2H1_H2 (B P : ℕ) (x : List Bool) (E : List Bool) :
    t2H1 B P P x E = t2H2 B P 0 x E := by
  rw [t2H1, t2H2, Nat.sub_self, unaryD_eq P]
  simp [markedD, List.append_assoc]

theorem t2H2_out (B P : ℕ) (x : List Bool) (E : List Bool) :
    t2H2 B P (P + 1) x E = t2Out B P x E := by
  rw [t2H2, t2Out, Nat.sub_self, unaryD_eq (P + 1)]
  simp [markedD, List.append_assoc]

theorem t2T_length (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) (hjR : jR ≤ P + 1) :
    (t2T B P jF jR x E).length
      = 8 * B + 4 * P + 4 * x.length + 28 + E.length := by
  simp only [t2T, List.length_append, List.length_replicate, markedD_length,
    List.length_cons, List.length_nil, xVis_length, unaryD_length]
  omega

/-! ## The `getD` suite -/

theorem t2T_getD_T1lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hi : i < B) :
    (t2T B P jF jR x E).getD (2 * i) false = true := by
  rw [t2T, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t2T_getD_T1mark (B P jF jR : ℕ) (x : List Bool) (E : List Bool) :
    (t2T B P jF jR x E).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (markedD jF ++ (List.replicate (6 * B + 2 * P + 18 - 2 * jF) true
      ++ ([false, true] ++ (xVis x x.length
      ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
      ++ ([false, true] ++ E))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t2T, unaryD_eq, List.append_assoc, h]
  rfl

/-- Reading the field and beyond: peel `T1`. -/
theorem t2T_getD_F (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ) :
    (t2T B P jF jR x E).getD (2 * B + 2 + c) false
      = (markedD jF ++ (List.replicate (6 * B + 2 * P + 18 - 2 * jF) true
        ++ ([false, true] ++ (xVis x x.length
        ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
        ++ ([false, true] ++ E))))))).getD c false := by
  rw [t2T, getD_append_left_length' _ _ (unaryD_length B)]

theorem t2T_getD_Fmark_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (h : i < jF) :
    (t2T B P jF jR x E).getD (2 * B + 2 + 2 * i) false = true := by
  rw [t2T_getD_F, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jF i h

theorem t2T_getD_Fmark_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (h : i < jF) :
    (t2T B P jF jR x E).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h2 := t2T_getD_F B P jF jR x E (2 * i + 1)
  rw [show 2 * B + 2 + (2 * i + 1) = 2 * B + 2 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jF i h

theorem t2T_getD_Fdata (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (h1 : 2 * jF ≤ c) (h2 : c < 6 * B + 2 * P + 18) :
    (t2T B P jF jR x E).getD (2 * B + 2 + c) false = true := by
  rw [t2T_getD_F, show c = 2 * jF + (c - 2 * jF) from by omega,
    getD_append_left_length' _ _ (markedD_length jF),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t2T_getD_Fend_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) :
    (t2T B P jF jR x E).getD (2 * B + 2 + (6 * B + 2 * P + 18)) false = false := by
  have h2 := getD_append_left_length' (markedD jF)
    (List.replicate (6 * B + 2 * P + 18 - 2 * jF) true ++ ([false, true]
      ++ (xVis x x.length ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
      ++ ([false, true] ++ E))))))
    (markedD_length jF) (6 * B + 2 * P + 18 - 2 * jF) false
  rw [show 2 * jF + (6 * B + 2 * P + 18 - 2 * jF) = 6 * B + 2 * P + 18 from by omega]
    at h2
  have h3 := getD_append_left_length'
    (List.replicate (6 * B + 2 * P + 18 - 2 * jF) true)
    ([false, true] ++ (xVis x x.length ++ (markedD jR
      ++ (List.replicate (2 * (P + 1 - jR)) true ++ ([false, true] ++ E)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h3
  rw [t2T_getD_F, h2, h3]
  rfl

/-- Reading the input region and beyond: peel through the field. -/
theorem t2T_getD_X (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + c) false
      = (xVis x x.length
        ++ (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
        ++ ([false, true] ++ E)))).getD c false := by
  rw [t2T, show 8 * B + 2 * P + 22 + c
      = 2 * B + 2 + (2 * jF + ((6 * B + 2 * P + 18 - 2 * jF) + (2 + c))) from by omega,
    getD_append_left_length' _ _ (unaryD_length B),
    getD_append_left_length' _ _ (markedD_length jF),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

/-- Reading region 4 and beyond: peel through the input. -/
theorem t2T_getD_R4 (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + c) false
      = (markedD jR ++ (List.replicate (2 * (P + 1 - jR)) true
        ++ ([false, true] ++ E))).getD c false := by
  have h := t2T_getD_X B P jF jR x E (4 * x.length + 2 + c) hjF
  rw [show 8 * B + 2 * P + 22 + (4 * x.length + 2 + c)
      = 8 * B + 2 * P + 4 * x.length + 24 + c from by omega,
    getD_append_left_length' _ _ (xVis_length x x.length)] at h
  exact h

theorem t2T_getD_R4mark_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (h : i < jR) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + 2 * i) false
      = true := by
  rw [t2T_getD_R4 B P jF jR x E _ hjF,
    List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jR i h

theorem t2T_getD_R4mark_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (h : i < jR) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1) false
      = false := by
  have h2 := t2T_getD_R4 B P jF jR x E (2 * i + 1) hjF
  rw [show 8 * B + 2 * P + 4 * x.length + 24 + (2 * i + 1)
      = 8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1 from by omega] at h2
  rw [h2, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jR i h

theorem t2T_getD_R4data (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (hjR : jR ≤ P + 1) (h1 : 2 * jR ≤ c)
    (h2 : c < 2 * P + 2) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + c) false = true := by
  rw [t2T_getD_R4 B P jF jR x E _ hjF, show c = 2 * jR + (c - 2 * jR) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t2T_getD_R4end_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) (hjR : jR ≤ P + 1) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + (2 * P + 2)) false
      = false := by
  rw [t2T_getD_R4 B P jF jR x E _ hjF,
    show 2 * P + 2 = 2 * jR + (2 * (P + 1 - jR) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem t2T_getD_R4end_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) (hjR : jR ≤ P + 1) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 4 * x.length + 24 + (2 * P + 3)) false
      = true := by
  rw [t2T_getD_R4 B P jF jR x E _ hjF,
    show 2 * P + 3 = 2 * jR + (2 * (P + 1 - jR) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jR),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ## The write lemmas -/

/-- Mark the next frontier pair. -/
theorem t2T_markF (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF < 3 * B + P + 9) :
    writeAt (t2T B P jF jR x E) (2 * B + 2 + (2 * jF + 1)) false
      = t2T B P (jF + 1) jR x E := by
  rw [writeAt_of_lt false (by
      simp only [t2T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2T,
    show 2 * B + 2 + (2 * jF + 1) = 2 * B + 2 + (2 * jF + 1) from rfl,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jF),
    show List.replicate (6 * B + 2 * P + 18 - 2 * jF) true
      = true :: true :: List.replicate (6 * B + 2 * P + 18 - 2 * jF - 2) true from by
        rw [show 6 * B + 2 * P + 18 - 2 * jF
          = 6 * B + 2 * P + 18 - 2 * jF - 2 + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t2T, ← markedD_snoc,
    show 6 * B + 2 * P + 18 - 2 * (jF + 1) = 6 * B + 2 * P + 18 - 2 * jF - 2
      from by omega]
  simp [List.append_assoc]

/-- Consume region 4's next pair. -/
theorem t2T_markR4 (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) (hjR : jR < P + 1) :
    writeAt (t2T B P jF jR x E)
        (8 * B + 2 * P + 4 * x.length + 24 + (2 * jR + 1)) false
      = t2T B P jF (jR + 1) x E := by
  rw [writeAt_of_lt false (by
      simp only [t2T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2T,
    show 8 * B + 2 * P + 4 * x.length + 24 + (2 * jR + 1)
      = 2 * B + 2 + (2 * jF + ((6 * B + 2 * P + 18 - 2 * jF)
        + (2 + (4 * x.length + 2 + (2 * jR + 1))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length jF),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (xVis_length x x.length),
    set_append_left_length' _ _ (markedD_length jR),
    show List.replicate (2 * (P + 1 - jR)) true
      = true :: true :: List.replicate (2 * (P + 1 - jR - 1)) true from by
        rw [show 2 * (P + 1 - jR) = 2 * (P + 1 - jR - 1) + 1 + 1 from by omega]
        simp [List.replicate_succ]]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t2T, ← markedD_snoc, show P + 1 - (jR + 1) = P + 1 - jR - 1 from by omega]
  simp [List.append_assoc]

/-- Fix, write 1: heal the last frontier mark's high cell. -/
theorem t2T_fix1 (B P : ℕ) (x : List Bool) (E : List Bool) :
    writeAt (t2T B P (P + 1) (P + 1) x E) (2 * B + 2 + 2 * P + 1) true
      = t2M' B P x E := by
  rw [writeAt_of_lt true (by
      simp only [t2T, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2T,
    show 2 * B + 2 + 2 * P + 1 = 2 * B + 2 + (2 * P + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    show markedD (P + 1) = markedD P ++ [true, false] from (markedD_snoc P).symm,
    List.append_assoc,
    set_append_left_length' _ _ (markedD_length P)]
  rw [t2M',
    show 6 * B + 2 * P + 18 - 2 * (P + 1) = 6 * B + 16 from by omega,
    show 2 * (P + 1 - (P + 1)) = 0 from by omega, List.replicate_zero,
    show markedD (P + 1) = markedD P ++ [true, false] from (markedD_snoc P).symm]
  simp [List.append_assoc]

/-- Fix, write 2: the marker's `0`. -/
theorem t2T_fix2 (B P : ℕ) (x : List Bool) (E : List Bool) :
    writeAt (t2M' B P x E) (2 * B + 2 + 2 * P) false = t2M B P x E := by
  rw [writeAt_of_lt false (by
      simp only [t2M', List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2M',
    show 2 * B + 2 + 2 * P = 2 * B + 2 + (2 * P + 0) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (markedD_length P)]
  rw [t2M]
  rfl

/-- Heal one frontier mark. -/
theorem t2H1_heal (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P) :
    writeAt (t2H1 B P i x E) (2 * B + 2 + 2 * i + 1) true = t2H1 B P (i + 1) x E := by
  rw [writeAt_of_lt true (by
      simp only [t2H1, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2H1,
    show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t2H1, show P - (i + 1) = P - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-- Heal one region-4 mark. -/
theorem t2H2_heal (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P + 1) :
    writeAt (t2H2 B P i x E)
        (8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1) true
      = t2H2 B P (i + 1) x E := by
  rw [writeAt_of_lt true (by
      simp only [t2H2, List.length_append, List.length_replicate, markedD_length,
        List.length_cons, List.length_nil, xVis_length, unaryD_length]
      omega), t2H2,
    show 8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1
      = 2 * B + 2 + (2 * P + 2 + ((6 * B + 16)
        + (2 + (4 * x.length + 2 + (2 * i + 1))))) from by omega,
    set_append_left_length' _ _ (unaryD_length B),
    set_append_left_length' _ _ (unaryD_length P),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (xVis_length x x.length),
    set_append_left_length' _ _ List.length_replicate,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [t2H2, show P + 1 - (i + 1) = P + 1 - i - 1 from by omega,
    show (2 * (i + 1) : ℕ) = 2 * i + 1 + 1 from by omega,
    List.replicate_succ' (n := 2 * i + 1), List.replicate_succ' (n := 2 * i)]
  simp

/-! ## Input-region reads at walk positions -/

theorem t2T_getD_unit_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (hi : i < x.length) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * i) false = x.getD i false :=
  (t2T_getD_X B P jF jR x E (4 * i) hjF).trans (xVisE_val_lo x x.length i _ hi)

theorem t2T_getD_unit_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (hi : i < x.length) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * i + 1) false
      = x.getD i false := by
  have h := (t2T_getD_X B P jF jR x E (4 * i + 1) hjF).trans
    (xVisE_val_hi x x.length i _ hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 1) = 8 * B + 2 * P + 22 + 4 * i + 1
    from by omega] at h

theorem t2T_getD_unit_cur (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (hi : i < x.length) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * i + 2) false = true := by
  have h := (t2T_getD_X B P jF jR x E (4 * i + 2) hjF).trans
    (xVisE_cur_lo x x.length i _ hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 2) = 8 * B + 2 * P + 22 + 4 * i + 2
    from by omega] at h

theorem t2T_getD_unit_vis (B P jF jR : ℕ) (x : List Bool) (E : List Bool) (i : ℕ)
    (hjF : jF ≤ 3 * B + P + 9) (hi : i < x.length) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * i + 3) false = false := by
  have h := (t2T_getD_X B P jF jR x E (4 * i + 3) hjF).trans
    (xVisE_cur_hi_vis x x.length i _ hi hi)
  rwa [show 8 * B + 2 * P + 22 + (4 * i + 3) = 8 * B + 2 * P + 22 + 4 * i + 3
    from by omega] at h

theorem t2T_getD_term_lo (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * x.length) false = false :=
  (t2T_getD_X B P jF jR x E (4 * x.length) hjF).trans (xVisE_term_lo x x.length _)

theorem t2T_getD_term_hi (B P jF jR : ℕ) (x : List Bool) (E : List Bool)
    (hjF : jF ≤ 3 * B + P + 9) :
    (t2T B P jF jR x E).getD (8 * B + 2 * P + 22 + 4 * x.length + 1) false = true := by
  have h := (t2T_getD_X B P jF jR x E (4 * x.length + 1) hjF).trans
    (xVisE_term_hi x x.length _)
  rwa [show 8 * B + 2 * P + 22 + (4 * x.length + 1)
    = 8 * B + 2 * P + 22 + 4 * x.length + 1 from by omega] at h

/-! ## Heal-phase reads -/

theorem t2H1_getD_lo (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P) :
    (t2H1 B P i x E).getD (2 * B + 2 + 2 * i) false = true := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ (false :: true :: (List.replicate (6 * B + 16) true
      ++ ([false, true] ++ (xVis x x.length
      ++ (markedD (P + 1) ++ ([false, true] ++ E)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t2H1, show 2 * B + 2 + 2 * i = 2 * B + 2 + (2 * i) from rfl,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t2H1_getD_hi (B P i : ℕ) (x : List Bool) (E : List Bool) (hi : i < P) :
    (t2H1 B P i x E).getD (2 * B + 2 + 2 * i + 1) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P - i) ++ (false :: true :: (List.replicate (6 * B + 16) true
      ++ ([false, true] ++ (xVis x x.length
      ++ (markedD (P + 1) ++ ([false, true] ++ E)))))))
    List.length_replicate 1 false
  rw [t2H1, show 2 * B + 2 + 2 * i + 1 = 2 * B + 2 + (2 * i + 1) from by omega,
    getD_append_left_length' _ _ (unaryD_length B), h,
    show markedD (P - i) = true :: false :: markedD (P - i - 1) from by
      rw [show P - i = P - i - 1 + 1 from by omega]
      rfl]
  rfl

/-- Reading `t2H2` past `T1 ++ T2`. -/
theorem t2H2_getD_F (B P i : ℕ) (x : List Bool) (E : List Bool) (c : ℕ) :
    (t2H2 B P i x E).getD (2 * B + 2 + (2 * P + 2 + c)) false
      = (List.replicate (6 * B + 16) true ++ ([false, true] ++ (xVis x x.length
        ++ (List.replicate (2 * i) true ++ (markedD (P + 1 - i)
        ++ ([false, true] ++ E)))))).getD c false := by
  rw [t2H2, getD_append_left_length' _ _ (unaryD_length B),
    getD_append_left_length' _ _ (unaryD_length P)]

theorem t2H2_getD_mark_lo (B P i : ℕ) (x : List Bool) (E : List Bool) :
    (t2H2 B P i x E).getD (2 * B + 2 + 2 * P) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * P) true)
    ([false, true] ++ (List.replicate (6 * B + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (List.replicate (2 * i) true ++ (markedD (P + 1 - i)
      ++ ([false, true] ++ E)))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t2H2, unaryD_eq P, List.append_assoc,
    show 2 * B + 2 + 2 * P = 2 * B + 2 + (2 * P) from rfl,
    getD_append_left_length' _ _ (unaryD_length B), h]
  rfl

theorem t2H2_getD_Fdata (B P i : ℕ) (x : List Bool) (E : List Bool) (c : ℕ)
    (hc : c < 6 * B + 16) :
    (t2H2 B P i x E).getD (2 * B + 2 + (2 * P + 2 + c)) false = true := by
  rw [t2H2_getD_F, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t2H2_getD_Fend_lo (B P i : ℕ) (x : List Bool) (E : List Bool) :
    (t2H2 B P i x E).getD (2 * B + 2 + (2 * P + 2 + (6 * B + 16))) false = false := by
  have h3 := getD_append_left_length' (List.replicate (6 * B + 16) true)
    ([false, true] ++ (xVis x x.length ++ (List.replicate (2 * i) true
      ++ (markedD (P + 1 - i) ++ ([false, true] ++ E)))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h3
  rw [t2H2_getD_F, h3]
  rfl

/-- Reading `t2H2`'s input region. -/
theorem t2H2_getD_X (B P i : ℕ) (x : List Bool) (E : List Bool) (c : ℕ) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + c) false
      = (xVis x x.length ++ (List.replicate (2 * i) true ++ (markedD (P + 1 - i)
        ++ ([false, true] ++ E)))).getD c false := by
  have h := t2H2_getD_F B P i x E (6 * B + 16 + (2 + c))
  rw [show 2 * B + 2 + (2 * P + 2 + (6 * B + 16 + (2 + c)))
      = 8 * B + 2 * P + 22 + c from by omega] at h
  rw [h, getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]

theorem t2H2_getD_unit_lo (B P i : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k < x.length) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * k) false = x.getD k false :=
  (t2H2_getD_X B P i x E (4 * k)).trans (xVisE_val_lo x x.length k _ hk)

theorem t2H2_getD_unit_hi (B P i : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k < x.length) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * k + 1) false = x.getD k false := by
  have h := (t2H2_getD_X B P i x E (4 * k + 1)).trans (xVisE_val_hi x x.length k _ hk)
  rwa [show 8 * B + 2 * P + 22 + (4 * k + 1) = 8 * B + 2 * P + 22 + 4 * k + 1
    from by omega] at h

theorem t2H2_getD_unit_cur (B P i : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k < x.length) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * k + 2) false = true := by
  have h := (t2H2_getD_X B P i x E (4 * k + 2)).trans (xVisE_cur_lo x x.length k _ hk)
  rwa [show 8 * B + 2 * P + 22 + (4 * k + 2) = 8 * B + 2 * P + 22 + 4 * k + 2
    from by omega] at h

theorem t2H2_getD_unit_vis (B P i : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k < x.length) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * k + 3) false = false := by
  have h := (t2H2_getD_X B P i x E (4 * k + 3)).trans
    (xVisE_cur_hi_vis x x.length k _ hk hk)
  rwa [show 8 * B + 2 * P + 22 + (4 * k + 3) = 8 * B + 2 * P + 22 + 4 * k + 3
    from by omega] at h

theorem t2H2_getD_term_lo (B P i : ℕ) (x : List Bool) (E : List Bool) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * x.length) false = false :=
  (t2H2_getD_X B P i x E (4 * x.length)).trans (xVisE_term_lo x x.length _)

theorem t2H2_getD_term_hi (B P i : ℕ) (x : List Bool) (E : List Bool) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 22 + 4 * x.length + 1) false = true := by
  have h := (t2H2_getD_X B P i x E (4 * x.length + 1)).trans
    (xVisE_term_hi x x.length _)
  rwa [show 8 * B + 2 * P + 22 + (4 * x.length + 1)
    = 8 * B + 2 * P + 22 + 4 * x.length + 1 from by omega] at h

/-- Reading `t2H2`'s region 4. -/
theorem t2H2_getD_R4 (B P i : ℕ) (x : List Bool) (E : List Bool) (c : ℕ) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 4 * x.length + 24 + c) false
      = (List.replicate (2 * i) true ++ (markedD (P + 1 - i)
        ++ ([false, true] ++ E))).getD c false := by
  have h := t2H2_getD_X B P i x E (4 * x.length + 2 + c)
  rw [show 8 * B + 2 * P + 22 + (4 * x.length + 2 + c)
      = 8 * B + 2 * P + 4 * x.length + 24 + c from by omega,
    getD_append_left_length' _ _ (xVis_length x x.length)] at h
  exact h

theorem t2H2_getD_heal_lo (B P i : ℕ) (x : List Bool) (E : List Bool)
    (hi : i < P + 1) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 4 * x.length + 24 + 2 * i) false
      = true := by
  have h2 := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P + 1 - i) ++ ([false, true] ++ E)) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t2H2_getD_R4, h2,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t2H2_getD_heal_hi (B P i : ℕ) (x : List Bool) (E : List Bool)
    (hi : i < P + 1) :
    (t2H2 B P i x E).getD (8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1) false
      = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * i) true)
    (markedD (P + 1 - i) ++ ([false, true] ++ E)) List.length_replicate 1 false
  have h := t2H2_getD_R4 B P i x E (2 * i + 1)
  rw [show 8 * B + 2 * P + 4 * x.length + 24 + (2 * i + 1)
      = 8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 1 from by omega] at h
  rw [h, h2,
    show markedD (P + 1 - i) = true :: false :: markedD (P + 1 - i - 1) from by
      rw [show P + 1 - i = P + 1 - i - 1 + 1 from by omega]
      rfl]
  rfl

theorem t2H2_getD_done (B P : ℕ) (x : List Bool) (E : List Bool) :
    (t2H2 B P (P + 1) x E).getD
      (8 * B + 2 * P + 4 * x.length + 24 + 2 * (P + 1)) false = false := by
  have h2 := getD_append_left_length' (List.replicate (2 * (P + 1)) true)
    (markedD (P + 1 - (P + 1)) ++ ([false, true] ++ E)) List.length_replicate 0 false
  simp only [Nat.add_zero] at h2
  rw [t2H2_getD_R4, h2, Nat.sub_self]
  rfl

/-! ## The `T2` machine

Control: `State = Fin 46 × Bool`.  Phase A (source-find, `0-14`): cross `T1`
(`0/1/2`), cross the field content-blind (`3/4/5`), walk the input's units (`6-10`;
value pair with terminal detect, visited cursor), find in region 4 (`11/12`: skip `10`,
mark `11` ⇒ reset to B, boundary ⇒ `14` reset to C).  Phase B (frontier-find,
`15-19`): cross `T1`, skip `10`, mark `11` ⇒ reset to A.  Phase C (marker fix,
`20-27`): cross `T1`, skip `10`, at the first `11` step LEFT twice, write `1` (heal the
last mark's high), LEFT, write `0` (the marker), reset to D.  Phase D (mega-heal,
`28-43`): cross `T1`, heal the frontier (`31/32`), cross the marker (`31/33`), cross
the field (`34/35/36`), walk the units (`37-41`), heal region 4 (`42/43`), boundary ⇒
DONE.  `44` done, `45` dead. -/

def t2Machine : Machine where
  State := Fin 46 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 44) || decide (s.1 = 45)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, b), none, 1) else ((2, b), none, 1))
    else if s.1 = 1 then ((0, s.2), none, 1)
    else if s.1 = 2 then ((3, s.2), none, 1)
    else if s.1 = 3 then (if b then ((4, b), none, 1) else ((5, b), none, 1))
    else if s.1 = 4 then ((3, s.2), none, 1)
    else if s.1 = 5 then ((6, s.2), none, 1)
    else if s.1 = 6 then (if b then ((7, b), none, 1) else ((8, b), none, 1))
    else if s.1 = 7 then ((9, s.2), none, 1)
    else if s.1 = 8 then
      (if b then ((11, s.2), none, 1) else ((9, s.2), none, 1))
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if b then ((45, s.2), none, 2) else ((6, s.2), none, 1))
    else if s.1 = 11 then (if b then ((12, b), none, 1) else ((14, b), none, 1))
    else if s.1 = 12 then
      (if b then ((15, s.2), some false, 3) else ((11, s.2), none, 1))
    else if s.1 = 14 then ((20, s.2), none, 3)
    else if s.1 = 15 then (if b then ((16, b), none, 1) else ((17, b), none, 1))
    else if s.1 = 16 then ((15, s.2), none, 1)
    else if s.1 = 17 then ((18, s.2), none, 1)
    else if s.1 = 18 then ((19, b), none, 1)
    else if s.1 = 19 then
      (if b then ((0, s.2), some false, 3) else ((18, s.2), none, 1))
    else if s.1 = 20 then (if b then ((21, b), none, 1) else ((22, b), none, 1))
    else if s.1 = 21 then ((20, s.2), none, 1)
    else if s.1 = 22 then ((23, s.2), none, 1)
    else if s.1 = 23 then ((24, b), none, 1)
    else if s.1 = 24 then
      (if b then ((25, s.2), none, 0) else ((23, s.2), none, 1))
    else if s.1 = 25 then ((26, s.2), none, 0)
    else if s.1 = 26 then ((27, s.2), some true, 0)
    else if s.1 = 27 then ((28, s.2), some false, 3)
    else if s.1 = 28 then (if b then ((29, b), none, 1) else ((30, b), none, 1))
    else if s.1 = 29 then ((28, s.2), none, 1)
    else if s.1 = 30 then ((31, s.2), none, 1)
    else if s.1 = 31 then (if b then ((32, b), none, 1) else ((33, b), none, 1))
    else if s.1 = 32 then ((31, s.2), some true, 1)
    else if s.1 = 33 then ((34, s.2), none, 1)
    else if s.1 = 34 then (if b then ((35, b), none, 1) else ((36, b), none, 1))
    else if s.1 = 35 then ((34, s.2), none, 1)
    else if s.1 = 36 then ((37, s.2), none, 1)
    else if s.1 = 37 then (if b then ((38, b), none, 1) else ((39, b), none, 1))
    else if s.1 = 38 then ((40, s.2), none, 1)
    else if s.1 = 39 then
      (if b then ((42, s.2), none, 1) else ((40, s.2), none, 1))
    else if s.1 = 40 then ((41, b), none, 1)
    else if s.1 = 41 then
      (if b then ((45, s.2), none, 2) else ((37, s.2), none, 1))
    else if s.1 = 42 then (if b then ((43, b), none, 1) else ((44, b), none, 2))
    else if s.1 = 43 then ((42, s.2), some true, 1)
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 44)

theorem init_t2 (x : List Bool) : init t2Machine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem u0T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(0, s), p, T⟩ = ⟨(1, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u0F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(0, s), p, T⟩ = ⟨(2, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u1 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(1, s), p, T⟩ = ⟨(0, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u2 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(2, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u3T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(3, s), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u3F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(3, s), p, T⟩ = ⟨(5, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u4 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(4, s), p, T⟩ = ⟨(3, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u5 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(5, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u6T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(6, s), p, T⟩ = ⟨(7, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u6F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(6, s), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u7 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(7, s), p, T⟩ = ⟨(9, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u8T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(8, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u8F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u9 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u10F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(10, s), p, T⟩ = ⟨(6, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u11T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(11, s), p, T⟩ = ⟨(12, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u11F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(11, s), p, T⟩ = ⟨(14, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u12T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(12, s), p, T⟩ = ⟨(15, s), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u12F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(12, s), p, T⟩ = ⟨(11, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u14 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(14, s), p, T⟩ = ⟨(20, s), 0, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u15T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(15, s), p, T⟩ = ⟨(16, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u15F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(15, s), p, T⟩ = ⟨(17, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u16 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(16, s), p, T⟩ = ⟨(15, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u17 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(17, s), p, T⟩ = ⟨(18, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u18 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u19T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(19, s), p, T⟩ = ⟨(0, s), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u19F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(19, s), p, T⟩ = ⟨(18, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u20T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(20, s), p, T⟩ = ⟨(21, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u20F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(20, s), p, T⟩ = ⟨(22, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u21 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(21, s), p, T⟩ = ⟨(20, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u22 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(22, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u23 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(23, s), p, T⟩ = ⟨(24, T.getD p false), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u24T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(24, s), p, T⟩ = ⟨(25, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u24F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(24, s), p, T⟩ = ⟨(23, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u25 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(25, s), p, T⟩ = ⟨(26, s), p - 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u26 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(26, s), p, T⟩ = ⟨(27, s), p - 1, writeAt T p true⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u27 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(27, s), p, T⟩ = ⟨(28, s), 0, writeAt T p false⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u28T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(28, s), p, T⟩ = ⟨(29, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u28F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(28, s), p, T⟩ = ⟨(30, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u29 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(29, s), p, T⟩ = ⟨(28, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u30 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(30, s), p, T⟩ = ⟨(31, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u31T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(31, s), p, T⟩ = ⟨(32, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u31F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(31, s), p, T⟩ = ⟨(33, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u32 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(32, s), p, T⟩ = ⟨(31, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u33 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(33, s), p, T⟩ = ⟨(34, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u34T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(34, s), p, T⟩ = ⟨(35, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u34F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(34, s), p, T⟩ = ⟨(36, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u35 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(35, s), p, T⟩ = ⟨(34, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u36 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(36, s), p, T⟩ = ⟨(37, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u37T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(37, s), p, T⟩ = ⟨(38, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u37F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(37, s), p, T⟩ = ⟨(39, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u38 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(38, s), p, T⟩ = ⟨(40, s), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u39T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(39, s), p, T⟩ = ⟨(42, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u39F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(39, s), p, T⟩ = ⟨(40, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u40 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(40, s), p, T⟩ = ⟨(41, T.getD p false), p + 1, T⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

theorem u41F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(41, s), p, T⟩ = ⟨(37, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u42T {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step t2Machine ⟨(42, s), p, T⟩ = ⟨(43, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u42F {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step t2Machine ⟨(42, s), p, T⟩ = ⟨(44, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, t2Machine, moveHead, h]

theorem u43 {s : Bool} {p : ℕ} {T : List Bool} :
    step t2Machine ⟨(43, s), p, T⟩ = ⟨(42, s), p + 1, writeAt T p true⟩ := by
  simp only [step, t2Machine, moveHead]; rfl

/-! ### Two late reads -/

theorem t2H1_getD_T1lo (B P i : ℕ) (x : List Bool) (E : List Bool) (k : ℕ)
    (hk : k < B) :
    (t2H1 B P i x E).getD (2 * k) false = true := by
  rw [t2H1, unaryD_eq, List.append_assoc,
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem t2H1_getD_T1mark (B P i : ℕ) (x : List Bool) (E : List Bool) :
    (t2H1 B P i x E).getD (2 * B) false = false := by
  have h := getD_append_left_length' (List.replicate (2 * B) true)
    ([false, true] ++ (List.replicate (2 * i) true ++ (markedD (P - i)
      ++ (false :: true :: (List.replicate (6 * B + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (markedD (P + 1) ++ ([false, true] ++ E)))))))))
    List.length_replicate 0 false
  simp only [Nat.add_zero] at h
  rw [t2H1, unaryD_eq, List.append_assoc, h]
  rfl

/-! ### Pair- and unit-step composites -/

theorem v_skipT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u0T h1, u1]

theorem v_crossT1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(0, s), p, T⟩ = ⟨(3, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u0F h1, u2]

theorem v_skipField {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(3, s), p, T⟩ = ⟨(3, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u3T h1, u4]

theorem v_crossDelim {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(3, s), p, T⟩ = ⟨(6, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u3F h1, u5]

theorem v_skipUnit {s : Bool} {p : ℕ} {T : List Bool}
    (hv : T.getD (p + 1) false = T.getD p false)
    (hc : T.getD (p + 2) false = true) (hch : T.getD (p + 3) false = false) :
    run t2Machine 4 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  cases hb : T.getD p false with
  | true =>
    rw [hb] at hv
    rw [u6T hb, u7, u9, hc, u10F hch]
  | false =>
    rw [hb] at hv
    rw [u6F hb, u8F hv, u9, hc, u10F hch]

theorem v_term {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t2Machine 2 ⟨(6, s), p, T⟩ = ⟨(11, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u6F h1, u8T h2]

theorem v_skipR4 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t2Machine 2 ⟨(11, s), p, T⟩ = ⟨(11, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u11T h1, u12F h2]

theorem v_markR4 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t2Machine 2 ⟨(11, s), p, T⟩ = ⟨(15, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, u11T h1, u12T h2]

theorem v_bound {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(11, s), p, T⟩ = ⟨(20, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, u11F h1, u14]

theorem v_skipT1B {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(15, s), p, T⟩ = ⟨(15, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u15T h1, u16]

theorem v_crossT1B {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(15, s), p, T⟩ = ⟨(18, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u15F h1, u17]

theorem v_skipFB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t2Machine 2 ⟨(18, s), p, T⟩ = ⟨(18, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u18, h1, u19F h2]

theorem v_markFB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run t2Machine 2 ⟨(18, s), p, T⟩ = ⟨(0, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, u18, h1, u19T h2]

theorem v_skipT1C {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(20, s), p, T⟩ = ⟨(20, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u20T h1, u21]

theorem v_crossT1C {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(20, s), p, T⟩ = ⟨(23, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u20F h1, u22]

theorem v_skipFC {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run t2Machine 2 ⟨(23, s), p, T⟩ = ⟨(23, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u23, h1, u24F h2]

theorem v_fix {s : Bool} {q : ℕ} {T : List Bool}
    (h1 : T.getD (q + 2) false = true) (h2 : T.getD (q + 3) false = true) :
    run t2Machine 5 ⟨(23, s), q + 2, T⟩
      = ⟨(28, true), 0, writeAt (writeAt T (q + 1) true) q false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_succ, run_zero, u23, h1, u24T h2,
    show q + 2 + 1 - 1 = q + 2 from by omega, u25,
    show q + 2 - 1 = q + 1 from by omega, u26,
    show q + 1 - 1 = q from by omega, u27]

theorem v_skipT1D {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u28T h1, u29]

theorem v_crossT1D {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(28, s), p, T⟩ = ⟨(31, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u28F h1, u30]

theorem v_heal1 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(31, s), p, T⟩ = ⟨(31, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, u31T h1, u32]

theorem v_marker {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(31, s), p, T⟩ = ⟨(34, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u31F h1, u33]

theorem v_skipFD {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(34, s), p, T⟩ = ⟨(34, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u34T h1, u35]

theorem v_crossDelimD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) :
    run t2Machine 2 ⟨(34, s), p, T⟩ = ⟨(37, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u34F h1, u36]

theorem v_skipUnitD {s : Bool} {p : ℕ} {T : List Bool}
    (hv : T.getD (p + 1) false = T.getD p false)
    (hc : T.getD (p + 2) false = true) (hch : T.getD (p + 3) false = false) :
    run t2Machine 4 ⟨(37, s), p, T⟩ = ⟨(37, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  cases hb : T.getD p false with
  | true =>
    rw [hb] at hv
    rw [u37T hb, u38, u40, hc, u41F hch]
  | false =>
    rw [hb] at hv
    rw [u37F hb, u39F hv, u40, hc, u41F hch]

theorem v_termD {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run t2Machine 2 ⟨(37, s), p, T⟩ = ⟨(42, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, u37F h1, u39T h2]

theorem v_healR4 {s : Bool} {p : ℕ} {T : List Bool} (h1 : T.getD p false = true) :
    run t2Machine 2 ⟨(42, s), p, T⟩ = ⟨(42, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, u42T h1, u43]

theorem v_done {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    run t2Machine 1 ⟨(42, s), p, T⟩ = ⟨(44, false), p, T⟩ := by
  rw [run_succ, run_zero, u42F h]

/-! ### Scan run-invariants -/

theorem w_skipT1 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipT1 (h k (by omega))]
    rfl

theorem w_skipField (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(3, s), q, T⟩
      = ⟨(3, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipField (h k (by omega))]
    rfl

theorem w_units (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 4 * i + 1) false = T.getD (q + 4 * i) false
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = false) :
    run t2Machine (4 * k) ⟨(6, s), q, T⟩
      = ⟨(6, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipUnit hk.1 hk.2.1 hk.2.2]
    rfl

theorem w_skipR4 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t2Machine (2 * k) ⟨(11, s), q, T⟩
      = ⟨(11, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipR4 hk.1 hk.2]
    rfl

theorem w_skipT1B (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(15, s), q, T⟩
      = ⟨(15, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipT1B (h k (by omega))]
    rfl

theorem w_skipFB (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t2Machine (2 * k) ⟨(18, s), q, T⟩
      = ⟨(18, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipFB hk.1 hk.2]
    rfl

theorem w_skipT1C (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipT1C (h k (by omega))]
    rfl

theorem w_skipFC (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run t2Machine (2 * k) ⟨(23, s), q, T⟩
      = ⟨(23, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipFC hk.1 hk.2]
    rfl

theorem w_skipT1D (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(28, s), q, T⟩
      = ⟨(28, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipT1D (h k (by omega))]
    rfl

theorem w_skipFieldD (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run t2Machine (2 * k) ⟨(34, s), q, T⟩
      = ⟨(34, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipFD (h k (by omega))]
    rfl

theorem w_unitsD (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 4 * i + 1) false = T.getD (q + 4 * i) false
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = false) :
    run t2Machine (4 * k) ⟨(37, s), q, T⟩
      = ⟨(37, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), v_skipUnitD hk.1 hk.2.1 hk.2.2]
    rfl

/-- Heal the frontier marks, tape evolving. -/
theorem w_heal1 (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P →
    run t2Machine (2 * k) ⟨(31, s), 2 * B + 2 + 2 * i, t2H1 B P i x E⟩
      = ⟨(31, if k = 0 then s else true), 2 * B + 2 + 2 * (i + k),
          t2H1 B P (i + k) x E⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      v_heal1 (t2H1_getD_lo B P i x E (by omega)),
      t2H1_heal B P i x E (by omega),
      show 2 * B + 2 + 2 * i + 2 = 2 * B + 2 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-- Heal region 4, tape evolving. -/
theorem w_healR4 (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) :
    ∀ (i : ℕ) (s : Bool), i + k ≤ P + 1 →
    run t2Machine (2 * k)
      ⟨(42, s), 8 * B + 2 * P + 4 * x.length + 24 + 2 * i, t2H2 B P i x E⟩
      = ⟨(42, if k = 0 then s else true),
          8 * B + 2 * P + 4 * x.length + 24 + 2 * (i + k), t2H2 B P (i + k) x E⟩ := by
  induction k with
  | zero => intro i s _; simp
  | succ k ih =>
    intro i s hik
    rw [show 2 * (k + 1) = 2 + 2 * k from by ring, run_add,
      v_healR4 (t2H2_getD_heal_lo B P i x E (by omega)),
      t2H2_heal B P i x E (by omega),
      show 8 * B + 2 * P + 4 * x.length + 24 + 2 * i + 2
        = 8 * B + 2 * P + 4 * x.length + 24 + 2 * (i + 1) from by omega,
      ih (i + 1) true (by omega),
      show i + 1 + k = i + (k + 1) from by ring, ite_self,
      if_neg (show ¬(k + 1 = 0) from by omega)]

/-! ## The round invariant -/

/-- **One transcription round**: consume region 4's pair `j`, mark frontier pair `j`. -/
theorem t2_round (B P : ℕ) (x : List Bool) (E : List Bool) (j : ℕ) (s : Bool)
    (hj : j ≤ P) :
    run t2Machine (10 * B + 2 * P + 4 * x.length + 4 * j + 30)
      ⟨(0, s), 0, t2T B P j j x E⟩
      = ⟨(0, true), 0, t2T B P (j + 1) (j + 1) x E⟩ := by
  have st1 := w_skipT1 (t2T B P j j x E) 0 B s (fun i hi => by
    simpa using t2T_getD_T1lo B P j j x E i hi)
  simp only [Nat.zero_add] at st1
  have st2 := v_crossT1 (s := if B = 0 then s else true) (p := 2 * B)
    (T := t2T B P j j x E) (t2T_getD_T1mark B P j j x E)
  have st3 := w_skipField (t2T B P j j x E) (2 * B + 2) (3 * B + P + 9) false
    (fun i hi => by
      rcases lt_or_ge i j with h | h
      · exact t2T_getD_Fmark_lo B P j j x E i h
      · exact t2T_getD_Fdata B P j j x E (2 * i) (by omega) (by omega) (by omega))
  rw [show 2 * B + 2 + 2 * (3 * B + P + 9) = 8 * B + 2 * P + 20 from by omega,
    if_neg (show ¬(3 * B + P + 9 = 0) from by omega)] at st3
  have h4 := t2T_getD_Fend_lo B P j j x E (by omega)
  rw [show 2 * B + 2 + (6 * B + 2 * P + 18) = 8 * B + 2 * P + 20 from by omega] at h4
  have st4 := v_crossDelim (s := true) (p := 8 * B + 2 * P + 20)
    (T := t2T B P j j x E) h4
  rw [show 8 * B + 2 * P + 20 + 2 = 8 * B + 2 * P + 22 from by omega] at st4
  have st5 := w_units (t2T B P j j x E) (8 * B + 2 * P + 22) x.length false
    (fun i hi => ⟨
      (t2T_getD_unit_hi B P j j x E i (by omega) hi).trans
        (t2T_getD_unit_lo B P j j x E i (by omega) hi).symm,
      t2T_getD_unit_cur B P j j x E i (by omega) hi,
      t2T_getD_unit_vis B P j j x E i (by omega) hi⟩)
  have st6 := v_term (s := if x.length = 0 then false else true)
    (p := 8 * B + 2 * P + 22 + 4 * x.length) (T := t2T B P j j x E)
    (t2T_getD_term_lo B P j j x E (by omega))
    (t2T_getD_term_hi B P j j x E (by omega))
  rw [show 8 * B + 2 * P + 22 + 4 * x.length + 2
      = 8 * B + 2 * P + 4 * x.length + 24 from by omega] at st6
  have st7 := w_skipR4 (t2T B P j j x E) (8 * B + 2 * P + 4 * x.length + 24) j false
    (fun i hi => ⟨t2T_getD_R4mark_lo B P j j x E i (by omega) hi,
      t2T_getD_R4mark_hi B P j j x E i (by omega) hi⟩)
  have h8b : (t2T B P j j x E).getD
      (8 * B + 2 * P + 4 * x.length + 24 + 2 * j + 1) false = true := by
    have h := t2T_getD_R4data B P j j x E (2 * j + 1) (by omega) (by omega) (by omega)
      (by omega)
    rwa [show 8 * B + 2 * P + 4 * x.length + 24 + (2 * j + 1)
      = 8 * B + 2 * P + 4 * x.length + 24 + 2 * j + 1 from by omega] at h
  have st8 := v_markR4 (s := if j = 0 then false else true)
    (p := 8 * B + 2 * P + 4 * x.length + 24 + 2 * j) (T := t2T B P j j x E)
    (t2T_getD_R4data B P j j x E (2 * j) (by omega) (by omega) (by omega) (by omega))
    h8b
  rw [show 8 * B + 2 * P + 4 * x.length + 24 + 2 * j + 1
      = 8 * B + 2 * P + 4 * x.length + 24 + (2 * j + 1) from by omega,
    t2T_markR4 B P j j x E (by omega) (by omega)] at st8
  have st9 := w_skipT1B (t2T B P j (j + 1) x E) 0 B true (fun i hi => by
    simpa using t2T_getD_T1lo B P j (j + 1) x E i hi)
  simp only [Nat.zero_add, ite_self] at st9
  have st10 := v_crossT1B (s := true) (p := 2 * B) (T := t2T B P j (j + 1) x E)
    (t2T_getD_T1mark B P j (j + 1) x E)
  have st11 := w_skipFB (t2T B P j (j + 1) x E) (2 * B + 2) j false
    (fun i hi => ⟨t2T_getD_Fmark_lo B P j (j + 1) x E i hi,
      t2T_getD_Fmark_hi B P j (j + 1) x E i hi⟩)
  have h12b : (t2T B P j (j + 1) x E).getD (2 * B + 2 + 2 * j + 1) false = true := by
    have h := t2T_getD_Fdata B P j (j + 1) x E (2 * j + 1) (by omega) (by omega)
      (by omega)
    rwa [show 2 * B + 2 + (2 * j + 1) = 2 * B + 2 + 2 * j + 1 from by omega] at h
  have st12 := v_markFB (s := if j = 0 then false else true) (p := 2 * B + 2 + 2 * j)
    (T := t2T B P j (j + 1) x E)
    (t2T_getD_Fdata B P j (j + 1) x E (2 * j) (by omega) (by omega) (by omega)) h12b
  rw [show 2 * B + 2 + 2 * j + 1 = 2 * B + 2 + (2 * j + 1) from by omega,
    t2T_markF B P j (j + 1) x E (by omega)] at st12
  rw [show 10 * B + 2 * P + 4 * x.length + 4 * j + 30
      = 2 * B + (2 + (2 * (3 * B + P + 9) + (2 + (4 * x.length + (2 + (2 * j
        + (2 + (2 * B + (2 + (2 * j + 2)))))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, run_add, st9, run_add, st10, run_add, st11, st12]

/-! ## The rounds and the endgame -/

/-- The cumulative clock of the first `k` rounds. -/
def t2Rounds (B P n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t2Rounds B P n k + (10 * B + 2 * P + 4 * n + 4 * k + 30)

theorem t2_rounds (B P : ℕ) (x : List Bool) (E : List Bool) (k : ℕ) (s : Bool)
    (hk : k ≤ P + 1) :
    run t2Machine (t2Rounds B P x.length k) ⟨(0, s), 0, t2T B P 0 0 x E⟩
      = ⟨(0, if k = 0 then s else true), 0, t2T B P k k x E⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show t2Rounds B P x.length (k + 1)
        = t2Rounds B P x.length k + (10 * B + 2 * P + 4 * x.length + 4 * k + 30)
        from rfl,
      run_add, ih (by omega), t2_round B P x E k _ (by omega), if_neg (by omega)]

/-- The pass's exact clock. -/
def t2Clock (B P n : ℕ) : ℕ :=
  t2Rounds B P n (P + 1)
    + ((8 * B + 4 * P + 4 * n + 28) + ((2 * B + 2 * P + 9)
      + (8 * B + 4 * P + 4 * n + 27)))

set_option maxHeartbeats 1600000 in
/-- **THE `T2` WRITE RUNS**: from brick M4's exit, the pass halts DONE with
`unaryD B ++ unaryD P` at the front and region 4 healed back to fresh. -/
theorem t2Machine_run (B P : ℕ) (x : List Bool) (E : List Bool) :
    run t2Machine (t2Clock B P x.length)
      (init t2Machine (fillOut B P x (unaryD (P + 1) ++ E)))
      = ⟨(44, false), 8 * B + 2 * P + 4 * x.length + 24 + 2 * (P + 1),
          t2Out B P x E⟩ := by
  rw [init_t2, ← t2T_zero, t2Clock, run_add,
    t2_rounds B P x E (P + 1) false (le_refl _), if_neg (show ¬(P + 1 = 0) from by omega)]
  -- Endgame block 1: the failed source-find (boundary discovery).
  have e1 := w_skipT1 (t2T B P (P + 1) (P + 1) x E) 0 B true (fun i hi => by
    simpa using t2T_getD_T1lo B P (P + 1) (P + 1) x E i hi)
  simp only [Nat.zero_add, ite_self] at e1
  have e2 := v_crossT1 (s := true) (p := 2 * B) (T := t2T B P (P + 1) (P + 1) x E)
    (t2T_getD_T1mark B P (P + 1) (P + 1) x E)
  have e3 := w_skipField (t2T B P (P + 1) (P + 1) x E) (2 * B + 2) (3 * B + P + 9)
    false (fun i hi => by
      rcases lt_or_ge i (P + 1) with h | h
      · exact t2T_getD_Fmark_lo B P (P + 1) (P + 1) x E i h
      · exact t2T_getD_Fdata B P (P + 1) (P + 1) x E (2 * i) (by omega) (by omega)
          (by omega))
  rw [show 2 * B + 2 + 2 * (3 * B + P + 9) = 8 * B + 2 * P + 20 from by omega,
    if_neg (show ¬(3 * B + P + 9 = 0) from by omega)] at e3
  have h4 := t2T_getD_Fend_lo B P (P + 1) (P + 1) x E (by omega)
  rw [show 2 * B + 2 + (6 * B + 2 * P + 18) = 8 * B + 2 * P + 20 from by omega] at h4
  have e4 := v_crossDelim (s := true) (p := 8 * B + 2 * P + 20)
    (T := t2T B P (P + 1) (P + 1) x E) h4
  rw [show 8 * B + 2 * P + 20 + 2 = 8 * B + 2 * P + 22 from by omega] at e4
  have e5 := w_units (t2T B P (P + 1) (P + 1) x E) (8 * B + 2 * P + 22) x.length false
    (fun i hi => ⟨
      (t2T_getD_unit_hi B P (P + 1) (P + 1) x E i (by omega) hi).trans
        (t2T_getD_unit_lo B P (P + 1) (P + 1) x E i (by omega) hi).symm,
      t2T_getD_unit_cur B P (P + 1) (P + 1) x E i (by omega) hi,
      t2T_getD_unit_vis B P (P + 1) (P + 1) x E i (by omega) hi⟩)
  have e6 := v_term (s := if x.length = 0 then false else true)
    (p := 8 * B + 2 * P + 22 + 4 * x.length) (T := t2T B P (P + 1) (P + 1) x E)
    (t2T_getD_term_lo B P (P + 1) (P + 1) x E (by omega))
    (t2T_getD_term_hi B P (P + 1) (P + 1) x E (by omega))
  rw [show 8 * B + 2 * P + 22 + 4 * x.length + 2
      = 8 * B + 2 * P + 4 * x.length + 24 from by omega] at e6
  have e7 := w_skipR4 (t2T B P (P + 1) (P + 1) x E)
    (8 * B + 2 * P + 4 * x.length + 24) (P + 1) false
    (fun i hi => ⟨t2T_getD_R4mark_lo B P (P + 1) (P + 1) x E i (by omega) hi,
      t2T_getD_R4mark_hi B P (P + 1) (P + 1) x E i (by omega) hi⟩)
  rw [show 8 * B + 2 * P + 4 * x.length + 24 + 2 * (P + 1)
      = 8 * B + 2 * P + 4 * x.length + 24 + (2 * P + 2) from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at e7
  have e8 := v_bound (s := true)
    (p := 8 * B + 2 * P + 4 * x.length + 24 + (2 * P + 2))
    (T := t2T B P (P + 1) (P + 1) x E)
    (t2T_getD_R4end_lo B P (P + 1) (P + 1) x E (by omega) (le_refl _))
  -- Endgame block 2: the marker fix.
  have e9 := w_skipT1C (t2T B P (P + 1) (P + 1) x E) 0 B false (fun i hi => by
    simpa using t2T_getD_T1lo B P (P + 1) (P + 1) x E i hi)
  simp only [Nat.zero_add] at e9
  have e10 := v_crossT1C (s := if B = 0 then false else true) (p := 2 * B)
    (T := t2T B P (P + 1) (P + 1) x E) (t2T_getD_T1mark B P (P + 1) (P + 1) x E)
  have e11 := w_skipFC (t2T B P (P + 1) (P + 1) x E) (2 * B + 2) (P + 1) false
    (fun i hi => ⟨t2T_getD_Fmark_lo B P (P + 1) (P + 1) x E i hi,
      t2T_getD_Fmark_hi B P (P + 1) (P + 1) x E i hi⟩)
  rw [show 2 * B + 2 + 2 * (P + 1) = 2 * B + 2 + 2 * P + 2 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at e11
  have h12a : (t2T B P (P + 1) (P + 1) x E).getD (2 * B + 2 + 2 * P + 2) false
      = true := by
    have h := t2T_getD_Fdata B P (P + 1) (P + 1) x E (2 * P + 2) (by omega) (by omega)
      (by omega)
    rwa [show 2 * B + 2 + (2 * P + 2) = 2 * B + 2 + 2 * P + 2 from by omega] at h
  have h12b : (t2T B P (P + 1) (P + 1) x E).getD (2 * B + 2 + 2 * P + 3) false
      = true := by
    have h := t2T_getD_Fdata B P (P + 1) (P + 1) x E (2 * P + 3) (by omega) (by omega)
      (by omega)
    rwa [show 2 * B + 2 + (2 * P + 3) = 2 * B + 2 + 2 * P + 3 from by omega] at h
  have e12 := v_fix (s := true) (q := 2 * B + 2 + 2 * P)
    (T := t2T B P (P + 1) (P + 1) x E) h12a h12b
  rw [t2T_fix1 B P x E, t2T_fix2 B P x E, t2M_H1 B P x E] at e12
  -- Endgame block 3: the mega-heal.
  have e13 := w_skipT1D (t2H1 B P 0 x E) 0 B true (fun i hi => by
    simpa using t2H1_getD_T1lo B P 0 x E i hi)
  simp only [Nat.zero_add, ite_self] at e13
  have e14 := v_crossT1D (s := true) (p := 2 * B) (T := t2H1 B P 0 x E)
    (t2H1_getD_T1mark B P 0 x E)
  have e15 := w_heal1 B P x E P 0 false (by omega)
  rw [show 2 * B + 2 + 2 * 0 = 2 * B + 2 from by omega,
    show (0 + P : ℕ) = P from by omega, t2H1_H2 B P x E] at e15
  have e16 := v_marker (s := if P = 0 then false else true) (p := 2 * B + 2 + 2 * P)
    (T := t2H2 B P 0 x E) (t2H2_getD_mark_lo B P 0 x E)
  rw [show 2 * B + 2 + 2 * P + 2 = 2 * B + 2 * P + 4 from by omega] at e16
  have e17 := w_skipFieldD (t2H2 B P 0 x E) (2 * B + 2 * P + 4) (3 * B + 8) false
    (fun i hi => by
      have h := t2H2_getD_Fdata B P 0 x E (2 * i) (by omega)
      rwa [show 2 * B + 2 + (2 * P + 2 + 2 * i) = 2 * B + 2 * P + 4 + 2 * i
        from by omega] at h)
  rw [show 2 * B + 2 * P + 4 + 2 * (3 * B + 8) = 8 * B + 2 * P + 20 from by omega,
    if_neg (show ¬(3 * B + 8 = 0) from by omega)] at e17
  have h18 := t2H2_getD_Fend_lo B P 0 x E
  rw [show 2 * B + 2 + (2 * P + 2 + (6 * B + 16)) = 8 * B + 2 * P + 20
    from by omega] at h18
  have e18 := v_crossDelimD (s := true) (p := 8 * B + 2 * P + 20)
    (T := t2H2 B P 0 x E) h18
  rw [show 8 * B + 2 * P + 20 + 2 = 8 * B + 2 * P + 22 from by omega] at e18
  have e19 := w_unitsD (t2H2 B P 0 x E) (8 * B + 2 * P + 22) x.length false
    (fun i hi => ⟨
      (t2H2_getD_unit_hi B P 0 x E i hi).trans
        (t2H2_getD_unit_lo B P 0 x E i hi).symm,
      t2H2_getD_unit_cur B P 0 x E i hi,
      t2H2_getD_unit_vis B P 0 x E i hi⟩)
  have e20 := v_termD (s := if x.length = 0 then false else true)
    (p := 8 * B + 2 * P + 22 + 4 * x.length) (T := t2H2 B P 0 x E)
    (t2H2_getD_term_lo B P 0 x E) (t2H2_getD_term_hi B P 0 x E)
  rw [show 8 * B + 2 * P + 22 + 4 * x.length + 2
      = 8 * B + 2 * P + 4 * x.length + 24 from by omega] at e20
  have e21 := w_healR4 B P x E (P + 1) 0 false (by omega)
  rw [show 8 * B + 2 * P + 4 * x.length + 24 + 2 * 0
      = 8 * B + 2 * P + 4 * x.length + 24 from by omega,
    show (0 + (P + 1) : ℕ) = P + 1 from by omega,
    if_neg (show ¬(P + 1 = 0) from by omega)] at e21
  have e22 := v_done (s := true)
    (p := 8 * B + 2 * P + 4 * x.length + 24 + 2 * (P + 1))
    (T := t2H2 B P (P + 1) x E) (t2H2_getD_done B P x E)
  -- Assemble.
  rw [show (8 * B + 4 * P + 4 * x.length + 28) + ((2 * B + 2 * P + 9)
        + (8 * B + 4 * P + 4 * x.length + 27))
      = 2 * B + (2 + (2 * (3 * B + P + 9) + (2 + (4 * x.length + (2 + (2 * (P + 1)
        + (2 + (2 * B + (2 + (2 * (P + 1) + (5 + (2 * B + (2 + (2 * P + (2
        + (2 * (3 * B + 8) + (2 + (4 * x.length + (2 + (2 * (P + 1)
        + 1)))))))))))))))))))) from by omega,
    run_add, e1, run_add, e2, run_add, e3, run_add, e4, run_add, e5, run_add, e6,
    run_add, e7, run_add, e8, run_add, e9, run_add, e10, run_add, e11, run_add, e12,
    run_add, e13, run_add, e14, run_add, e15, run_add, e16, run_add, e17, run_add,
    e18, run_add, e19, run_add, e20, run_add, e21, e22, t2H2_out B P x E]

/-- The done state halts. -/
theorem t2Machine_halt44 : t2Machine.halt ((44 : Fin 46), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2
