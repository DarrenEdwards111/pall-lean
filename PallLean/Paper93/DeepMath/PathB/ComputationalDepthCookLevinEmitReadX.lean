import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitNestVar

/-!
# Cook–Levin M2 emitter, E5 — the x-splicer (the cursored input region)

E5 of `SCOPE_EMITTER.md`: reading the input's bits into the emission.  The init family emits, for
`p = 0, 1, …, P`, the unit clause fixing `cell[0][p] = x.getD p false` — its block stream ends in the
**input bit itself**.  Two observations make this buildable without M1's unfinished two-pointer weld:

* the init family's reads are **sequential** (`x[0], x[1], …` in loop order), so no addressed read is
  needed — only a cursor that advances one position per round; and
* a cursor must be **value-preserving** (the loop heals its tracks), which the doubled input encoding
  cannot host (marking a `00`/`11` data pair destroys its value).  So the emitter's input region carries
  the **cursored encoding** `xVis`: each input bit `b` is the 4-cell unit `b b 1 c` — a value pair (never
  written) and a cursor pair (`11` unvisited, `10` visited) — closed by the `01` terminator.  This is a
  faithful, poly-size re-encoding of `x` (an E6 pre-pass concern, same promise family as the doubled
  input).

**This file is E5 (i): the region's complete tape algebra** — the `xVis` descriptor with its full `getD`
suite (value cells independent of the cursor state, cursor classification per visit status, the
terminator), the saturation law (visits cap at `|x|`), the structural cursor-mark write, and the healing
descriptor `xHl` (healed-prefix/visited-total) with its equations (`xHl_zero`/`xHl_sat`), walk facts, and
the structural heal write.  All sorry-free.

E5 (ii) — `readXMachine`, next — runs `for k in range N: read the next input bit and splice it (doubled)
into the output`: find/mark the bound's pair `k`; walk the visited units to the first unvisited cursor;
mark it and **carry the unit's value in the finite control** (the phase encodes it) on the seek to the
output terminator; splice the doubled bit; reset.  When the walk meets the input terminator instead (a
read past `|x|`), the carried value is `false` — exactly `getD`'s default, so the emitted stream is
uniformly `x.getD k false` (`bitsUpTo`).  The finale heals the bound and the cursors.  Both the found and
past-the-end rounds cost the **same** clock (`4·|x| + 2` walk steps either way), so the clock recursion is
uniform.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNest
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar

/-! ## The emitted bit stream -/

/-- The first `k` input bits, with `getD`'s `false` default past the end. -/
def bitsUpTo (x : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => bitsUpTo x k ++ [x.getD k false]

theorem bitsUpTo_length (x : List Bool) (k : ℕ) : (bitsUpTo x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bitsUpTo, List.length_append, ih, List.length_cons, List.length_nil]

/-! ## The cursored input region

Each input bit `b` is the unit `b b 1 c` (value pair, cursor pair); `c = true` unvisited, `c = false`
visited.  `xVis x m` has the first `m` units visited. -/

def xVis : List Bool → ℕ → List Bool
  | [], _ => [false, true]
  | b :: bs, 0 => b :: b :: true :: true :: xVis bs 0
  | b :: bs, m + 1 => b :: b :: true :: false :: xVis bs m

theorem xVis_length (x : List Bool) (m : ℕ) : (xVis x m).length = 4 * x.length + 2 := by
  induction x generalizing m with
  | nil => cases m <;> rfl
  | cons b bs ih =>
    cases m with
    | zero =>
      show (b :: b :: true :: true :: xVis bs 0).length = 4 * (bs.length + 1) + 2
      simp only [List.length_cons, ih]
      omega
    | succ m =>
      show (b :: b :: true :: false :: xVis bs m).length = 4 * (bs.length + 1) + 2
      simp only [List.length_cons, ih]
      omega

/-- Visited saturates at the unit count. -/
theorem xVis_saturate (x : List Bool) (m : ℕ) (h : x.length ≤ m) : xVis x m = xVis x x.length := by
  induction x generalizing m with
  | nil => cases m <;> rfl
  | cons b bs ih =>
    cases m with
    | zero => simp at h
    | succ m =>
      show b :: b :: true :: false :: xVis bs m = b :: b :: true :: false :: xVis bs bs.length
      rw [ih m (by simpa using h)]

/-! ### The `getD` suite (suffix-generic) -/

theorem xVisE_val_lo (x : List Bool) (m i : ℕ) (E : List Bool) (h : i < x.length) :
    (xVis x m ++ E).getD (4 * i) false = x.getD i false := by
  induction x generalizing m i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => cases m <;> rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      cases m with
      | zero =>
        show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (i + 1)) false = _
        rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih 0 i h'
      | succ m =>
        show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (i + 1)) false = _
        rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih m i h'

theorem xVisE_val_hi (x : List Bool) (m i : ℕ) (E : List Bool) (h : i < x.length) :
    (xVis x m ++ E).getD (4 * i + 1) false = x.getD i false := by
  induction x generalizing m i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => cases m <;> rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      cases m with
      | zero =>
        show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (i + 1) + 1) false = _
        rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih 0 i h'
      | succ m =>
        show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (i + 1) + 1) false = _
        rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih m i h'

theorem xVisE_cur_lo (x : List Bool) (m i : ℕ) (E : List Bool) (h : i < x.length) :
    (xVis x m ++ E).getD (4 * i + 2) false = true := by
  induction x generalizing m i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => cases m <;> rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      cases m with
      | zero =>
        show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (i + 1) + 2) false = _
        rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih 0 i h'
      | succ m =>
        show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (i + 1) + 2) false = _
        rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih m i h'

theorem xVisE_cur_hi_vis (x : List Bool) (m i : ℕ) (E : List Bool) (h : i < m)
    (hx : i < x.length) :
    (xVis x m ++ E).getD (4 * i + 3) false = false := by
  induction x generalizing m i with
  | nil => simp at hx
  | cons b bs ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases i with
      | zero => rfl
      | succ i =>
        have h' : i < m := by omega
        have hx' : i < bs.length := by simpa using hx
        show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (i + 1) + 3) false = _
        rw [show 4 * (i + 1) + 3 = 4 * i + 3 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih m i h' hx'

theorem xVisE_cur_hi_unvis (x : List Bool) (m i : ℕ) (E : List Bool) (h : m ≤ i)
    (hx : i < x.length) :
    (xVis x m ++ E).getD (4 * i + 3) false = true := by
  induction x generalizing m i with
  | nil => simp at hx
  | cons b bs ih =>
    cases m with
    | zero =>
      cases i with
      | zero => rfl
      | succ i =>
        have hx' : i < bs.length := by simpa using hx
        show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (i + 1) + 3) false = _
        rw [show 4 * (i + 1) + 3 = 4 * i + 3 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih 0 i (by omega) hx'
    | succ m =>
      cases i with
      | zero => omega
      | succ i =>
        have hx' : i < bs.length := by simpa using hx
        show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (i + 1) + 3) false = _
        rw [show 4 * (i + 1) + 3 = 4 * i + 3 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih m i (by omega) hx'

theorem xVisE_term_lo (x : List Bool) (m : ℕ) (E : List Bool) :
    (xVis x m ++ E).getD (4 * x.length) false = false := by
  induction x generalizing m with
  | nil => cases m <;> rfl
  | cons b bs ih =>
    cases m with
    | zero =>
      show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (bs.length + 1)) false = _
      rw [show 4 * (bs.length + 1) = 4 * bs.length + 1 + 1 + 1 + 1 from by ring]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih 0
    | succ m =>
      show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (bs.length + 1)) false = _
      rw [show 4 * (bs.length + 1) = 4 * bs.length + 1 + 1 + 1 + 1 from by ring]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih m

theorem xVisE_term_hi (x : List Bool) (m : ℕ) (E : List Bool) :
    (xVis x m ++ E).getD (4 * x.length + 1) false = true := by
  induction x generalizing m with
  | nil => cases m <;> rfl
  | cons b bs ih =>
    cases m with
    | zero =>
      show ((b :: b :: true :: true :: xVis bs 0) ++ E).getD (4 * (bs.length + 1) + 1) false = _
      rw [show 4 * (bs.length + 1) + 1 = 4 * bs.length + 1 + 1 + 1 + 1 + 1 from by ring]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih 0
    | succ m =>
      show ((b :: b :: true :: false :: xVis bs m) ++ E).getD (4 * (bs.length + 1) + 1) false
          = _
      rw [show 4 * (bs.length + 1) + 1 = 4 * bs.length + 1 + 1 + 1 + 1 + 1 from by ring]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih m

/-! ### The structural cursor writes -/

/-- Marking the first unvisited cursor. -/
theorem xVis_mark (x : List Bool) (m : ℕ) (E : List Bool) (h : m < x.length) :
    writeAt (xVis x m ++ E) (4 * m + 3) false = xVis x (m + 1) ++ E := by
  induction x generalizing m with
  | nil => simp at h
  | cons b bs ih =>
    cases m with
    | zero =>
      show writeAt ((b :: b :: true :: true :: xVis bs 0) ++ E) 3 false = _
      rw [writeAt_of_lt false (by
          simp only [List.cons_append, List.length_cons]
          omega)]
      simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
      rfl
    | succ m =>
      have h' : m < bs.length := by simpa using h
      show writeAt ((b :: b :: true :: false :: xVis bs m) ++ E) (4 * (m + 1) + 3) false = _
      have hlen : 4 * (m + 1) + 3 < ((b :: b :: true :: false :: xVis bs m) ++ E).length := by
        simp only [List.cons_append, List.length_cons, List.length_append, xVis_length]
        omega
      rw [writeAt_of_lt false hlen,
        show 4 * (m + 1) + 3 = 4 * m + 3 + 1 + 1 + 1 + 1 from by ring]
      simp only [List.cons_append, List.set_cons_succ]
      have := ih m h'
      rw [writeAt_of_lt false (by
          simp only [List.length_append, xVis_length]
          omega)] at this
      rw [this]
      rfl

/-! ### The healing descriptor

The finale's restore walk needs a two-index form: units `< h` already healed (unvisited again), units
`h ≤ · < M` still visited, units `≥ M` never visited. -/

def xHl : List Bool → ℕ → ℕ → List Bool
  | [], _, _ => [false, true]
  | b :: bs, 0, 0 => b :: b :: true :: true :: xHl bs 0 0
  | b :: bs, 0, M + 1 => b :: b :: true :: false :: xHl bs 0 M
  | b :: bs, h + 1, 0 => b :: b :: true :: true :: xHl bs h 0
  | b :: bs, h + 1, M + 1 => b :: b :: true :: true :: xHl bs h M

/-- Nothing healed yet: the visited form. -/
theorem xHl_zero (x : List Bool) (M : ℕ) : xHl x 0 M = xVis x M := by
  induction x generalizing M with
  | nil => cases M <;> rfl
  | cons b bs ih =>
    cases M with
    | zero =>
      show b :: b :: true :: true :: xHl bs 0 0 = b :: b :: true :: true :: xVis bs 0
      rw [ih 0]
    | succ M =>
      show b :: b :: true :: false :: xHl bs 0 M = b :: b :: true :: false :: xVis bs M
      rw [ih M]

/-- Everything healed: the pristine form. -/
theorem xHl_sat (x : List Bool) (h M : ℕ) (hM : M ≤ h) : xHl x h M = xVis x 0 := by
  induction x generalizing h M with
  | nil => cases h <;> cases M <;> rfl
  | cons b bs ih =>
    cases h with
    | zero =>
      cases M with
      | zero =>
        show b :: b :: true :: true :: xHl bs 0 0 = b :: b :: true :: true :: xVis bs 0
        rw [ih 0 0 (le_refl 0)]
      | succ M => omega
    | succ h =>
      cases M with
      | zero =>
        show b :: b :: true :: true :: xHl bs h 0 = b :: b :: true :: true :: xVis bs 0
        rw [ih h 0 (by omega)]
      | succ M =>
        show b :: b :: true :: true :: xHl bs h M = b :: b :: true :: true :: xVis bs 0
        rw [ih h M (by omega)]

theorem xHl_length (x : List Bool) (h M : ℕ) : (xHl x h M).length = 4 * x.length + 2 := by
  induction x generalizing h M with
  | nil => cases h <;> cases M <;> rfl
  | cons b bs ih =>
    cases h with
    | zero =>
      cases M with
      | zero =>
        show (b :: b :: true :: true :: xHl bs 0 0).length = 4 * (bs.length + 1) + 2
        simp only [List.length_cons, ih]; omega
      | succ M =>
        show (b :: b :: true :: false :: xHl bs 0 M).length = 4 * (bs.length + 1) + 2
        simp only [List.length_cons, ih]; omega
    | succ h =>
      cases M with
      | zero =>
        show (b :: b :: true :: true :: xHl bs h 0).length = 4 * (bs.length + 1) + 2
        simp only [List.length_cons, ih]; omega
      | succ M =>
        show (b :: b :: true :: true :: xHl bs h M).length = 4 * (bs.length + 1) + 2
        simp only [List.length_cons, ih]; omega

/-! ### The healing walk's `getD` facts (only the current unit is queried while `h < M`;
past `M` the tape is already `xVis x 0` by `xHl_sat`, so the `xVis` suite serves) -/

theorem xHlE_val_lo (x : List Bool) (h M : ℕ) (E : List Bool) (i : ℕ) (hi : i < x.length) :
    (xHl x h M ++ E).getD (4 * i) false = x.getD i false := by
  induction x generalizing h M i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => cases h <;> cases M <;> rfl
    | succ i =>
      have hi' : i < bs.length := by simpa using hi
      cases h with
      | zero =>
        cases M with
        | zero =>
          show ((b :: b :: true :: true :: xHl bs 0 0) ++ E).getD (4 * (i + 1)) false = _
          rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 0 i hi'
        | succ M =>
          show ((b :: b :: true :: false :: xHl bs 0 M) ++ E).getD (4 * (i + 1)) false = _
          rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 M i hi'
      | succ h =>
        cases M with
        | zero =>
          show ((b :: b :: true :: true :: xHl bs h 0) ++ E).getD (4 * (i + 1)) false = _
          rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih h 0 i hi'
        | succ M =>
          show ((b :: b :: true :: true :: xHl bs h M) ++ E).getD (4 * (i + 1)) false = _
          rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih h M i hi'

theorem xHlE_cur_hi_at (x : List Bool) (h M : ℕ) (E : List Bool) (hh : h < M)
    (hx : h < x.length) :
    (xHl x h M ++ E).getD (4 * h + 3) false = false := by
  induction x generalizing h M with
  | nil => simp at hx
  | cons b bs ih =>
    cases h with
    | zero =>
      cases M with
      | zero => omega
      | succ M => rfl
    | succ h =>
      cases M with
      | zero => omega
      | succ M =>
        have hx' : h < bs.length := by simpa using hx
        show ((b :: b :: true :: true :: xHl bs h M) ++ E).getD (4 * (h + 1) + 3) false = _
        rw [show 4 * (h + 1) + 3 = 4 * h + 3 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.getD_cons_succ]
        exact ih h M (by omega) hx'

/-- The heal write: the current visited cursor back to unvisited. -/
theorem xHl_heal (x : List Bool) (h M : ℕ) (E : List Bool) (hh : h < M) (hx : h < x.length) :
    writeAt (xHl x h M ++ E) (4 * h + 3) true = xHl x (h + 1) M ++ E := by
  induction x generalizing h M with
  | nil => simp at hx
  | cons b bs ih =>
    cases h with
    | zero =>
      cases M with
      | zero => omega
      | succ M =>
        show writeAt ((b :: b :: true :: false :: xHl bs 0 M) ++ E) 3 true = _
        rw [writeAt_of_lt true (by
            simp only [List.cons_append, List.length_cons]
            omega)]
        simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
        rfl
    | succ h =>
      cases M with
      | zero => omega
      | succ M =>
        have hx' : h < bs.length := by simpa using hx
        show writeAt ((b :: b :: true :: true :: xHl bs h M) ++ E) (4 * (h + 1) + 3) true = _
        have hlen : 4 * (h + 1) + 3 < ((b :: b :: true :: true :: xHl bs h M) ++ E).length := by
          simp only [List.cons_append, List.length_cons, List.length_append, xHl_length]
          omega
        rw [writeAt_of_lt true hlen,
          show 4 * (h + 1) + 3 = 4 * h + 3 + 1 + 1 + 1 + 1 from by ring]
        simp only [List.cons_append, List.set_cons_succ]
        have := ih h M (by omega) hx'
        rw [writeAt_of_lt true (by
            simp only [List.length_append, xHl_length]
            omega)] at this
        rw [this]
        rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX