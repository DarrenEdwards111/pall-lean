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

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2
