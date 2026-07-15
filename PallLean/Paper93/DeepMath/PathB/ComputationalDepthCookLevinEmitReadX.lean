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

E5 (i) — the region's tape algebra: the `xVis` descriptor with its full `getD` suite (value cells
independent of the cursor state, cursor classification per visit status, the terminator), the saturation
law, the structural cursor-mark write, and the healing descriptor `xHl` with its equations, walk facts,
and heal write.

E5 (ii) — `readXMachine` (`Fin 33 × Bool`) runs `for k in range N: read the next input bit and splice it
(doubled) into the output`: find/mark the bound's pair `k`; walk the visited units to the first unvisited
cursor; mark it and **carry the unit's value in the finite control** (the phase encodes it — two emit
tracks) on the seek to the output terminator; splice the doubled bit; reset.  When the walk meets the
input terminator instead (a read past `|x|`), the carried value is `false` — exactly `getD`'s default, so
the emitted stream is uniformly `x.getD k false` (`bitsUpTo`).  Both the found and past-the-end rounds
cost the **same** clock, so the clock recursion is uniform (`rdRounds`).  **Top theorem**
(`readX_run`/`readX_halted`/`readX_output`): the machine halts by itself at the explicit clock (quadratic,
`rdClock_le`) with tape **exactly** `unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N))` — the first
`N` input bits spliced, the bound restored, **every cursor healed**.

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

theorem xHlE_val_hi (x : List Bool) (h M : ℕ) (E : List Bool) (i : ℕ) (hi : i < x.length) :
    (xHl x h M ++ E).getD (4 * i + 1) false = x.getD i false := by
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
          show ((b :: b :: true :: true :: xHl bs 0 0) ++ E).getD (4 * (i + 1) + 1) false = _
          rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 0 i hi'
        | succ M =>
          show ((b :: b :: true :: false :: xHl bs 0 M) ++ E).getD (4 * (i + 1) + 1) false = _
          rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 M i hi'
      | succ h =>
        cases M with
        | zero =>
          show ((b :: b :: true :: true :: xHl bs h 0) ++ E).getD (4 * (i + 1) + 1) false = _
          rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih h 0 i hi'
        | succ M =>
          show ((b :: b :: true :: true :: xHl bs h M) ++ E).getD (4 * (i + 1) + 1) false = _
          rw [show 4 * (i + 1) + 1 = 4 * i + 1 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih h M i hi'

theorem xHlE_cur_lo (x : List Bool) (h M : ℕ) (E : List Bool) (i : ℕ) (hi : i < x.length) :
    (xHl x h M ++ E).getD (4 * i + 2) false = true := by
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
          show ((b :: b :: true :: true :: xHl bs 0 0) ++ E).getD (4 * (i + 1) + 2) false = _
          rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 0 i hi'
        | succ M =>
          show ((b :: b :: true :: false :: xHl bs 0 M) ++ E).getD (4 * (i + 1) + 2) false = _
          rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih 0 M i hi'
      | succ h =>
        cases M with
        | zero =>
          show ((b :: b :: true :: true :: xHl bs h 0) ++ E).getD (4 * (i + 1) + 2) false = _
          rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
          simp only [List.cons_append, List.getD_cons_succ]
          exact ih h 0 i hi'
        | succ M =>
          show ((b :: b :: true :: true :: xHl bs h M) ++ E).getD (4 * (i + 1) + 2) false = _
          rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 1 + 1 + 1 + 1 from by ring]
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

/-! ## The machine (E5 (ii))

Control: `Fin 33 × Bool` (stored cell).  Phases: `0/1` find in the bound, `2/3` skip the bound, `4/5` an
input unit's value pair (dispatch: equal ⇒ the value routes to its cursor track, differ ⇒ the input
terminator, value `false`), `6/7`/`8/9` the cursor pair for carried value `false`/`true` (visited ⇒ next
unit, unvisited ⇒ mark and emit), `10/11`/`18/19` the input-remainder seeks, `12/13`/`20/21` the output
seeks, `14–17`/`22–25` the doubled-bit snocs (+ reset), `26/27` heal the bound, `28/29`+`30/31` the
cursor-healing walk (terminator ⇒ halt), `32` = halt. -/

def readXMachine : Machine where
  State := Fin 33 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 32)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((26, s.2), none, 3) else ((32, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((32, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if b = s.2 then (if s.2 then ((8, s.2), none, 1) else ((6, s.2), none, 1))
       else ((12, false), none, 1))
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if b then ((10, s.2), some false, 1) else ((4, s.2), none, 1))
    else if s.1 = 8 then ((9, b), none, 1)
    else if s.1 = 9 then
      (if b then ((18, s.2), some false, 1) else ((4, s.2), none, 1))
    else if s.1 = 10 then ((11, b), none, 1)
    else if s.1 = 11 then
      (if b = s.2 then ((10, s.2), none, 1) else ((12, s.2), none, 1))
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if b = s.2 then ((12, s.2), none, 1) else ((14, s.2), none, 0))
    else if s.1 = 14 then ((15, s.2), some false, 1)
    else if s.1 = 15 then ((16, s.2), some false, 1)
    else if s.1 = 16 then ((17, s.2), some false, 1)
    else if s.1 = 17 then ((0, s.2), some true, 3)
    else if s.1 = 18 then ((19, b), none, 1)
    else if s.1 = 19 then
      (if b = s.2 then ((18, s.2), none, 1) else ((20, s.2), none, 1))
    else if s.1 = 20 then ((21, b), none, 1)
    else if s.1 = 21 then
      (if b = s.2 then ((20, s.2), none, 1) else ((22, s.2), none, 0))
    else if s.1 = 22 then ((23, s.2), some true, 1)
    else if s.1 = 23 then ((24, s.2), some true, 1)
    else if s.1 = 24 then ((25, s.2), some false, 1)
    else if s.1 = 25 then ((0, s.2), some true, 3)
    else if s.1 = 26 then ((27, b), none, 1)
    else if s.1 = 27 then
      (if s.2 then (if b then ((32, s.2), none, 2) else ((26, true), some true, 1))
       else (if b then ((28, s.2), none, 1) else ((32, s.2), none, 2)))
    else if s.1 = 28 then ((29, b), none, 1)
    else if s.1 = 29 then
      (if b = s.2 then ((30, s.2), none, 1) else ((32, false), none, 2))
    else if s.1 = 30 then ((31, b), none, 1)
    else if s.1 = 31 then
      (if b then ((28, s.2), none, 1) else ((28, s.2), some true, 1))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_rx (t : List Bool) : init readXMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ### Pair-step lemmas -/

section Steps
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem rx_skipD (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run readXMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_markD (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_toRstD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(0, s), p, T⟩ = ⟨(26, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_skipW (h1 : T.getD p false = true) :
    run readXMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, readXMachine, moveHead]; rfl

theorem rx_crossW (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

/-- A visited unit: four steps through value dispatch and cursor, landing on the next unit. -/
theorem rx_four_visited {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = false) :
    run readXMachine 4 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e4 : step readXMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e4, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  cases v with
  | false =>
    have e5 : step readXMachine ⟨(5, false), p + 1, T⟩ = ⟨(6, false), p + 2, T⟩ := by
      simp [step, readXMachine, moveHead, h2']
    rw [e5]
    have e6 : step readXMachine ⟨(6, false), p + 2, T⟩ = ⟨(7, T.getD (p + 2) false), p + 3, T⟩ := by
      simp only [step, readXMachine, moveHead]; rfl
    rw [e6, h3]
    have h4' := h4
    rw [List.getD_eq_getElem?_getD] at h4'
    simp [step, readXMachine, moveHead, h4']
  | true =>
    have e5 : step readXMachine ⟨(5, true), p + 1, T⟩ = ⟨(8, true), p + 2, T⟩ := by
      simp [step, readXMachine, moveHead, h2']
    rw [e5]
    have e8 : step readXMachine ⟨(8, true), p + 2, T⟩ = ⟨(9, T.getD (p + 2) false), p + 3, T⟩ := by
      simp only [step, readXMachine, moveHead]; rfl
    rw [e8, h3]
    have h4' := h4
    rw [List.getD_eq_getElem?_getD] at h4'
    simp [step, readXMachine, moveHead, h4']

/-- The unvisited unit, value `false`: mark the cursor and enter the value-`false` emit track. -/
theorem rx_four_mark0 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run readXMachine 4 ⟨(4, s), p, T⟩ = ⟨(10, true), p + 4, writeAt T (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e4 : step readXMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e4, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have e5 : step readXMachine ⟨(5, false), p + 1, T⟩ = ⟨(6, false), p + 2, T⟩ := by
    simp [step, readXMachine, moveHead, h2']
  rw [e5]
  have e6 : step readXMachine ⟨(6, false), p + 2, T⟩ = ⟨(7, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e6, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, readXMachine, moveHead, h4']

/-- The unvisited unit, value `true`: mark and enter the value-`true` emit track. -/
theorem rx_four_mark1 (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run readXMachine 4 ⟨(4, s), p, T⟩ = ⟨(18, true), p + 4, writeAt T (p + 3) false⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e4 : step readXMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e4, h1]
  have h2' := h2
  rw [List.getD_eq_getElem?_getD] at h2'
  have e5 : step readXMachine ⟨(5, true), p + 1, T⟩ = ⟨(8, true), p + 2, T⟩ := by
    simp [step, readXMachine, moveHead, h2']
  rw [e5]
  have e8 : step readXMachine ⟨(8, true), p + 2, T⟩ = ⟨(9, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e8, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, readXMachine, moveHead, h4']

/-- The input terminator: past the end, the carried value is `false` and the emit seek begins. -/
theorem rx_two_toB0 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(4, s), p, T⟩ = ⟨(12, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e4 : step readXMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e4, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2']

theorem rx_seekA0 (h : T.getD p false = T.getD (p + 1) false) :
    run readXMachine 2 ⟨(10, s), p, T⟩ = ⟨(10, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_crossA0 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(10, s), p, T⟩ = ⟨(12, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2']

theorem rx_seekB0 (h : T.getD p false = T.getD (p + 1) false) :
    run readXMachine 2 ⟨(12, s), p, T⟩ = ⟨(12, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_detectB0 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(12, s), p, T⟩ = ⟨(14, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem rx_four_snoc0 :
    run readXMachine 4 ⟨(14, s), p, T⟩
      = ⟨(0, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e14 : step readXMachine ⟨(14, s), p, T⟩ = ⟨(15, s), p + 1, writeAt T p false⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  have e15 : ∀ p' T', step readXMachine ⟨(15, s), p', T'⟩
      = ⟨(16, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  have e16 : ∀ p' T', step readXMachine ⟨(16, s), p', T'⟩
      = ⟨(17, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  have e17 : ∀ p' T', step readXMachine ⟨(17, s), p', T'⟩
      = ⟨(0, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  rw [e14, e15, e16, e17]

theorem rx_seekA1 (h : T.getD p false = T.getD (p + 1) false) :
    run readXMachine 2 ⟨(18, s), p, T⟩ = ⟨(18, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_crossA1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(18, s), p, T⟩ = ⟨(20, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2']

theorem rx_seekB1 (h : T.getD p false = T.getD (p + 1) false) :
    run readXMachine 2 ⟨(20, s), p, T⟩ = ⟨(20, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0]
  have h2 := h.symm
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_detectB1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(20, s), p, T⟩ = ⟨(22, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2', show p + 1 - 1 = p from by omega]

theorem rx_four_snoc1 :
    run readXMachine 4 ⟨(22, s), p, T⟩
      = ⟨(0, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e22 : step readXMachine ⟨(22, s), p, T⟩ = ⟨(23, s), p + 1, writeAt T p true⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  have e23 : ∀ p' T', step readXMachine ⟨(23, s), p', T'⟩
      = ⟨(24, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  have e24 : ∀ p' T', step readXMachine ⟨(24, s), p', T'⟩
      = ⟨(25, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  have e25 : ∀ p' T', step readXMachine ⟨(25, s), p', T'⟩
      = ⟨(0, s), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, readXMachine, moveHead]; rfl
  rw [e22, e23, e24, e25]

theorem rx_healD (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run readXMachine 2 ⟨(26, s), p, T⟩ = ⟨(26, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(26, s), p, T⟩ = ⟨(27, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

theorem rx_crossHD (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(26, s), p, T⟩ = ⟨(28, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step readXMachine ⟨(26, s), p, T⟩ = ⟨(27, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, readXMachine, moveHead, h2]

/-- Heal a visited unit's cursor (four steps). -/
theorem rx_four_heal {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = false) :
    run readXMachine 4 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 4, writeAt T (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e28 : step readXMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e28, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e29 : step readXMachine ⟨(29, v), p + 1, T⟩ = ⟨(30, v), p + 2, T⟩ := by
    simp [step, readXMachine, moveHead, h2']
  rw [e29]
  have e30 : step readXMachine ⟨(30, v), p + 2, T⟩ = ⟨(31, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e30, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, readXMachine, moveHead, h4']

/-- Skip an unvisited unit in the heal walk (four steps, no write). -/
theorem rx_four_healSkip {v : Bool} (h1 : T.getD p false = v) (h2 : T.getD (p + 1) false = v)
    (h3 : T.getD (p + 2) false = true) (h4 : T.getD (p + 3) false = true) :
    run readXMachine 4 ⟨(28, s), p, T⟩ = ⟨(28, true), p + 4, T⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e28 : step readXMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e28, h1]
  have h2' := h2.symm
  rw [List.getD_eq_getElem?_getD] at h2'
  have e29 : step readXMachine ⟨(29, v), p + 1, T⟩ = ⟨(30, v), p + 2, T⟩ := by
    simp [step, readXMachine, moveHead, h2']
  rw [e29]
  have e30 : step readXMachine ⟨(30, v), p + 2, T⟩ = ⟨(31, T.getD (p + 2) false), p + 3, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e30, h3]
  have h4' := h4
  rw [List.getD_eq_getElem?_getD] at h4'
  simp [step, readXMachine, moveHead, h4']

/-- The heal walk meets the input terminator: halt. -/
theorem rx_two_healDone (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run readXMachine 2 ⟨(28, s), p, T⟩ = ⟨(32, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e28 : step readXMachine ⟨(28, s), p, T⟩ = ⟨(29, T.getD p false), p + 1, T⟩ := by
    simp only [step, readXMachine, moveHead]; rfl
  rw [e28, h1]
  have h2' : T.getD (p + 1) false ≠ false := by rw [h2]; simp
  rw [List.getD_eq_getElem?_getD] at h2'
  simp [step, readXMachine, moveHead, h2']

end Steps

/-! ### Scan run-invariants -/

theorem rx_skipDs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run readXMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_skipD hk.1 hk.2]
    rfl

theorem rx_skipWs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run readXMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_skipW (h k (by omega))]
    rfl

/-- The visited-unit walk. -/
theorem rx_vunits (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = false) :
    run readXMachine (4 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_four_visited hv1 hv2 hv3 hv4]
    rfl

theorem rx_seekA0s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run readXMachine (2 * k) ⟨(10, s), q, T⟩
      = ⟨(10, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_seekA0 (h k (by omega))]
    rfl

theorem rx_seekB0s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run readXMachine (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_seekB0 (h k (by omega))]
    rfl

theorem rx_seekA1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run readXMachine (2 * k) ⟨(18, s), q, T⟩
      = ⟨(18, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_seekA1 (h k (by omega))]
    rfl

theorem rx_seekB1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run readXMachine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_seekB1 (h k (by omega))]
    rfl

/-- The bound-restore invariant. -/
theorem rx_healDs (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run readXMachine (2 * i) ⟨(26, s), 0, hlT v 0 ++ E⟩
      = ⟨(26, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      rx_healD (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-- The cursor-heal walk (evolving, past the bound prefix). -/
theorem rx_healXs (A : List Bool) (N : ℕ) (x : List Bool) (M : ℕ) (E : List Bool)
    (ha : A.length = 2 * N + 2) (hM : M ≤ x.length) (s : Bool) (h'' : ℕ) (hh : h'' ≤ M) :
    run readXMachine (4 * h'') ⟨(28, s), 2 * N + 2, A ++ (xHl x 0 M ++ E)⟩
      = ⟨(28, if h'' = 0 then s else true), 2 * N + 2 + 4 * h'', A ++ (xHl x h'' M ++ E)⟩ := by
  induction h'' with
  | zero => rfl
  | succ h'' ih =>
    have hx : h'' < x.length := by omega
    have hv1 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'') false
        = x.getD h'' false := by
      rw [show 2 * N + 2 + 4 * h'' = 2 * N + 2 + (4 * h'') from rfl]
      exact liftJ A _ ha (xHlE_val_lo x h'' M E h'' hx)
    have hv2 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 1) false
        = x.getD h'' false := by
      rw [show 2 * N + 2 + 4 * h'' + 1 = 2 * N + 2 + (4 * h'' + 1) from by omega]
      exact liftJ A _ ha (xHlE_val_hi x h'' M E h'' hx)
    have hv3 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 2) false = true := by
      rw [show 2 * N + 2 + 4 * h'' + 2 = 2 * N + 2 + (4 * h'' + 2) from by omega]
      exact liftJ A _ ha (xHlE_cur_lo x h'' M E h'' hx)
    have hv4 : (A ++ (xHl x h'' M ++ E)).getD (2 * N + 2 + 4 * h'' + 3) false = false := by
      rw [show 2 * N + 2 + 4 * h'' + 3 = 2 * N + 2 + (4 * h'' + 3) from by omega]
      exact liftJ A _ ha (xHlE_cur_hi_at x h'' M E (by omega) hx)
    have hw : writeAt (A ++ (xHl x h'' M ++ E)) (2 * N + 2 + 4 * h'' + 3) true
        = A ++ (xHl x (h'' + 1) M ++ E) := by
      rw [show 2 * N + 2 + 4 * h'' + 3 = 2 * N + 2 + (4 * h'' + 3) from by omega,
        writeAt_append_right A _ (2 * N + 2) (4 * h'' + 3) true ha
          (by rw [List.length_append, xHl_length]; omega),
        xHl_heal x h'' M E (by omega) hx]
    rw [show 4 * (h'' + 1) = 4 * h'' + 4 from by ring, run_add, ih (by omega),
      rx_four_heal hv1 hv2 hv3 hv4, hw]
    rfl

/-- The unvisited tail of the heal walk (static scan). -/
theorem rx_healSkips (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → ∃ v, T.getD (q + 4 * i) false = v ∧ T.getD (q + 4 * i + 1) false = v
      ∧ T.getD (q + 4 * i + 2) false = true ∧ T.getD (q + 4 * i + 3) false = true) :
    run readXMachine (4 * k) ⟨(28, s), q, T⟩
      = ⟨(28, if k = 0 then s else true), q + 4 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := h k (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, run_add,
      ih (fun i hi => h i (by omega)), rx_four_healSkip hv1 hv2 hv3 hv4]
    rfl

/-! ## The rounds -/

/-- **A found round** (`k < |x|`): mark the bound's pair `k`, walk to the `k`-th unit, mark its cursor
carrying its value, seek out, splice the doubled bit. -/
theorem rx_round_found (N k : ℕ) (x OUT : List Bool) (hk : k < x.length) (hkN : k < N)
    (s : Bool) :
    run readXMachine (2 * N + 2 * k + 4 * x.length + 2 * OUT.length + 12)
      ⟨(0, s), 0, cntT N k ++ (xVis x k ++ encodeD OUT)⟩
      = ⟨(0, false), 0, cntT N (k + 1)
          ++ (xVis x (k + 1) ++ encodeD (OUT ++ [x.getD k false]))⟩ := by
  have hcb := cntT_length N (k + 1) (by omega : k + 1 ≤ N)
  have st1 := rx_skipDs (cntT N k ++ (xVis x k ++ encodeD OUT)) 0 k s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := rx_markD (s := if k = 0 then s else true) (p := 2 * k)
    (T := cntT N k ++ (xVis x k ++ encodeD OUT))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hkN] at st2
  have st3 := rx_skipWs (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)) 0 N true
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st3
  have st4 := rx_crossW (s := if N = 0 then true else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x k ++ encodeD OUT))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  simp only [ite_self] at st3 st4
  have st5 := rx_vunits (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)) (2 * N + 2) k false
    (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hcb (xVisE_val_lo x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hcb (xVisE_val_hi x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_lo x k i _ (by omega)), by
        rw [show 2 * N + 2 + 4 * i + 3 = 2 * N + 2 + (4 * i + 3) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_hi_vis x k i _ hi (by omega))⟩)
  -- shared facts for the mark/emit stages
  have hvlo : (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)).getD (2 * N + 2 + 4 * k) false
      = x.getD k false := liftJ _ _ hcb (xVisE_val_lo x k k _ hk)
  have hvhi : (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)).getD
      (2 * N + 2 + 4 * k + 1) false = x.getD k false := by
    rw [show 2 * N + 2 + 4 * k + 1 = 2 * N + 2 + (4 * k + 1) from by omega]
    exact liftJ _ _ hcb (xVisE_val_hi x k k _ hk)
  have hclo : (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)).getD
      (2 * N + 2 + 4 * k + 2) false = true := by
    rw [show 2 * N + 2 + 4 * k + 2 = 2 * N + 2 + (4 * k + 2) from by omega]
    exact liftJ _ _ hcb (xVisE_cur_lo x k k _ hk)
  have hchi : (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT)).getD
      (2 * N + 2 + 4 * k + 3) false = true := by
    rw [show 2 * N + 2 + 4 * k + 3 = 2 * N + 2 + (4 * k + 3) from by omega]
    exact liftJ _ _ hcb (xVisE_cur_hi_unvis x k k _ (le_refl k) hk)
  have hwmark : writeAt (cntT N (k + 1) ++ (xVis x k ++ encodeD OUT))
      (2 * N + 2 + 4 * k + 3) false
      = cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT) := by
    rw [show 2 * N + 2 + 4 * k + 3 = 2 * N + 2 + (4 * k + 3) from by omega,
      writeAt_append_right _ _ (2 * N + 2) (4 * k + 3) false hcb
        (by rw [List.length_append, xVis_length]; omega),
      xVis_mark x k _ hk]
  have hseekA : ∀ i, i < 2 * (x.length - k - 1) →
      (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
        (2 * N + 2 + 4 * k + 4 + 2 * i) false
      = (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
        (2 * N + 2 + 4 * k + 4 + 2 * i + 1) false := by
    intro i hi
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (j + j)) false = x.getD (k + 1 + j) false := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (j + j)
            = 2 * N + 2 + (4 * (k + 1 + j)) from by omega]
        exact liftJ _ _ hcb (xVisE_val_lo x (k + 1) (k + 1 + j) _ (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (j + j) + 1) false = x.getD (k + 1 + j) false := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (j + j) + 1
            = 2 * N + 2 + (4 * (k + 1 + j) + 1) from by omega]
        exact liftJ _ _ hcb (xVisE_val_hi x (k + 1) (k + 1 + j) _ (by omega))
      rw [e1, e2]
    · have e1 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1)) false = true := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1)
            = 2 * N + 2 + (4 * (k + 1 + j) + 2) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_lo x (k + 1) (k + 1 + j) _ (by omega))
      have e2 : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
          (2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1) + 1) false = true := by
        rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * j + 1) + 1
            = 2 * N + 2 + (4 * (k + 1 + j) + 3) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_hi_unvis x (k + 1) (k + 1 + j) _ (by omega) (by omega))
      rw [e1, e2]
  have htermlo : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
      (2 * N + 2 + 4 * x.length) false = false := by
    rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
    exact liftJ _ _ hcb (xVisE_term_lo x (k + 1) _)
  have htermhi : (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT)).getD
      (2 * N + 2 + 4 * x.length + 1) false = true := by
    rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
    exact liftJ _ _ hcb (xVisE_term_hi x (k + 1) _)
  have hq2 : (cntT N (k + 1)).length + (xVis x (k + 1)).length = 2 * N + 4 * x.length + 4 := by
    rw [hcb, xVis_length]; omega
  have hm1 := preD2_mark_lo (cntT N (k + 1)) (xVis x (k + 1)) OUT
    (2 * N + 4 * x.length + 4) hq2
  have hm2 := preD2_mark_hi (cntT N (k + 1)) (xVis x (k + 1)) OUT
    (2 * N + 4 * x.length + 4) hq2
  have hout := fun (i : ℕ) (hi : i < OUT.length) =>
    preD2_data_eq (cntT N (k + 1)) (xVis x (k + 1)) OUT (2 * N + 4 * x.length + 4) i hq2 hi
  have hsn := writes_snoc2 (cntT N (k + 1)) (xVis x (k + 1)) OUT
    (2 * N + 4 * x.length + 4) hq2
  -- assemble, casing on the read bit
  rw [show 2 * N + 2 * k + 4 * x.length + 2 * OUT.length + 12
      = 2 * k + (2 + (2 * N + (2 + (4 * k + (4 + (2 * (2 * (x.length - k - 1))
          + (2 + (2 * OUT.length + (2 + 4))))))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5]
  cases hv : x.getD k false with
  | false =>
    have st6 := rx_four_mark0 (s := if k = 0 then false else true) (p := 2 * N + 2 + 4 * k)
      (T := cntT N (k + 1) ++ (xVis x k ++ encodeD OUT))
      (by rw [hvlo, hv]) (by rw [hvhi, hv]) hclo hchi
    rw [hwmark] at st6
    have st7 := rx_seekA0s (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
      (2 * N + 2 + 4 * k + 4) (2 * (x.length - k - 1)) true hseekA
    rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * (x.length - k - 1))
        = 2 * N + 2 + 4 * x.length from by omega] at st7
    have st8 := rx_crossA0
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
        (2 * N + 2 + 4 * k + 4) true (2 * (x.length - k - 1)))
      (p := 2 * N + 2 + 4 * x.length) htermlo htermhi
    rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at st8
    have st9 := rx_seekB0s (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
      (2 * N + 4 * x.length + 4) OUT.length false hout
    have st10 := rx_detectB0
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
        (2 * N + 4 * x.length + 4) false OUT.length)
      (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length) hm1 hm2
    have st11 := rx_four_snoc0 (s := false)
      (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length)
      (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
    rw [hsn false] at st11
    rw [run_add, st6, run_add, st7, run_add, st8, run_add, st9, run_add, st10, st11]
  | true =>
    have st6 := rx_four_mark1 (s := if k = 0 then false else true) (p := 2 * N + 2 + 4 * k)
      (T := cntT N (k + 1) ++ (xVis x k ++ encodeD OUT))
      (by rw [hvlo, hv]) (by rw [hvhi, hv]) hclo hchi
    rw [hwmark] at st6
    have st7 := rx_seekA1s (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
      (2 * N + 2 + 4 * k + 4) (2 * (x.length - k - 1)) true hseekA
    rw [show 2 * N + 2 + 4 * k + 4 + 2 * (2 * (x.length - k - 1))
        = 2 * N + 2 + 4 * x.length from by omega] at st7
    have st8 := rx_crossA1
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
        (2 * N + 2 + 4 * k + 4) true (2 * (x.length - k - 1)))
      (p := 2 * N + 2 + 4 * x.length) htermlo htermhi
    rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at st8
    have st9 := rx_seekB1s (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
      (2 * N + 4 * x.length + 4) OUT.length false hout
    have st10 := rx_detectB1
      (s := storedD (cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
        (2 * N + 4 * x.length + 4) false OUT.length)
      (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length) hm1 hm2
    have st11 := rx_four_snoc1 (s := false)
      (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length)
      (T := cntT N (k + 1) ++ (xVis x (k + 1) ++ encodeD OUT))
    rw [hsn true] at st11
    rw [run_add, st6, run_add, st7, run_add, st8, run_add, st9, run_add, st10, st11]

/-- **A past-the-end round** (`|x| ≤ k`): every unit is visited; the walk meets the terminator and the
emitted bit is `getD`'s default. -/
theorem rx_round_past (N k : ℕ) (x OUT : List Bool) (hk : x.length ≤ k) (hkN : k < N)
    (s : Bool) :
    run readXMachine (2 * N + 2 * k + 4 * x.length + 2 * OUT.length + 12)
      ⟨(0, s), 0, cntT N k ++ (xVis x x.length ++ encodeD OUT)⟩
      = ⟨(0, false), 0, cntT N (k + 1)
          ++ (xVis x x.length ++ encodeD (OUT ++ [x.getD k false]))⟩ := by
  have hcb := cntT_length N (k + 1) (by omega : k + 1 ≤ N)
  have st1 := rx_skipDs (cntT N k ++ (xVis x x.length ++ encodeD OUT)) 0 k s
    (fun i hi => ⟨by simpa using cntE_mark_lo N k _ i hi,
                  by simpa using cntE_mark_hi N k _ i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := rx_markD (s := if k = 0 then s else true) (p := 2 * k)
    (T := cntT N k ++ (xVis x x.length ++ encodeD OUT))
    (cntE_data N k _ (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k _ (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k _ hkN] at st2
  have st3 := rx_skipWs (cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT)) 0 N true
    (fun i hi => by simpa using cntE_lo N (k + 1) _ i (by omega) hi)
  simp only [Nat.zero_add] at st3
  have st4 := rx_crossW (s := if N = 0 then true else true) (p := 2 * N)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT))
    (cntE_cm_lo N (k + 1) _ (by omega)) (cntE_cm_hi N (k + 1) _ (by omega))
  simp only [ite_self] at st3 st4
  have st5 := rx_vunits (cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT)) (2 * N + 2)
    x.length false (fun i hi => ⟨x.getD i false, by
        exact liftJ _ _ hcb (xVisE_val_lo x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 1 = 2 * N + 2 + (4 * i + 1) from by omega]
        exact liftJ _ _ hcb (xVisE_val_hi x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 2 = 2 * N + 2 + (4 * i + 2) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_lo x x.length i _ hi), by
        rw [show 2 * N + 2 + 4 * i + 3 = 2 * N + 2 + (4 * i + 3) from by omega]
        exact liftJ _ _ hcb (xVisE_cur_hi_vis x x.length i _ hi hi)⟩)
  have st6 := rx_two_toB0 (s := if x.length = 0 then false else true)
    (p := 2 * N + 2 + 4 * x.length)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hcb (xVisE_term_lo x x.length _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hcb (xVisE_term_hi x x.length _))
  rw [show 2 * N + 2 + 4 * x.length + 2 = 2 * N + 4 * x.length + 4 from by omega] at st6
  have hq2 : (cntT N (k + 1)).length + (xVis x x.length).length
      = 2 * N + 4 * x.length + 4 := by
    rw [hcb, xVis_length]; omega
  have st7 := rx_seekB0s (cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT))
    (2 * N + 4 * x.length + 4) OUT.length false
    (fun i hi => preD2_data_eq (cntT N (k + 1)) (xVis x x.length) OUT
      (2 * N + 4 * x.length + 4) i hq2 hi)
  have st8 := rx_detectB0
    (s := storedD (cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT))
      (2 * N + 4 * x.length + 4) false OUT.length)
    (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length)
    (preD2_mark_lo (cntT N (k + 1)) (xVis x x.length) OUT (2 * N + 4 * x.length + 4) hq2)
    (preD2_mark_hi (cntT N (k + 1)) (xVis x x.length) OUT (2 * N + 4 * x.length + 4) hq2)
  have st9 := rx_four_snoc0 (s := false) (p := 2 * N + 4 * x.length + 4 + 2 * OUT.length)
    (T := cntT N (k + 1) ++ (xVis x x.length ++ encodeD OUT))
  have hsn := writes_snoc2 (cntT N (k + 1)) (xVis x x.length) OUT
    (2 * N + 4 * x.length + 4) hq2 false
  rw [show [false] = [x.getD k false] from by rw [List.getD_eq_default _ _ hk]] at hsn
  rw [hsn] at st9
  rw [show 2 * N + 2 * k + 4 * x.length + 2 * OUT.length + 12
      = 2 * k + (2 + (2 * N + (2 + (4 * x.length + (2 + (2 * OUT.length + (2 + 4)))))))
      from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6,
    run_add, st7, run_add, st8, st9]

/-- Cumulative round clock. -/
def rdRounds (N X L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => rdRounds N X L k + (2 * N + 2 * k + 4 * X + 2 * (L + k) + 12)

/-- **Rounds invariant**: `k` bits read and spliced, the cursor at `min k |x|`. -/
theorem run_rd_rounds (N : ℕ) (x out : List Bool) (k : ℕ) (hk : k ≤ N) (s : Bool) :
    run readXMachine (rdRounds N x.length out.length k)
      ⟨(0, s), 0, cntT N 0 ++ (xVis x 0 ++ encodeD out)⟩
      = ⟨(0, if k = 0 then s else false), 0, cntT N k
          ++ (xVis x (min k x.length) ++ encodeD (out ++ bitsUpTo x k))⟩ := by
  induction k with
  | zero =>
    simp [bitsUpTo]
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge k x.length with hkx | hkx
    · have hrd := rx_round_found N k x (out ++ bitsUpTo x k) hkx (by omega)
        (if k = 0 then s else false)
      rw [show (out ++ bitsUpTo x k).length = out.length + k from by
          rw [List.length_append, bitsUpTo_length],
        List.append_assoc, show bitsUpTo x k ++ [x.getD k false] = bitsUpTo x (k + 1) from rfl]
        at hrd
      rw [show rdRounds N x.length out.length (k + 1)
          = rdRounds N x.length out.length k
              + (2 * N + 2 * k + 4 * x.length + 2 * (out.length + k) + 12) from rfl,
        run_add, ih (by omega), show min k x.length = k from by omega, hrd,
        show min (k + 1) x.length = k + 1 from by omega, if_neg (by omega)]
    · have hrd := rx_round_past N k x (out ++ bitsUpTo x k) hkx (by omega)
        (if k = 0 then s else false)
      rw [show (out ++ bitsUpTo x k).length = out.length + k from by
          rw [List.length_append, bitsUpTo_length],
        List.append_assoc, show bitsUpTo x k ++ [x.getD k false] = bitsUpTo x (k + 1) from rfl]
        at hrd
      rw [show rdRounds N x.length out.length (k + 1)
          = rdRounds N x.length out.length k
              + (2 * N + 2 * k + 4 * x.length + 2 * (out.length + k) + 12) from rfl,
        run_add, ih (by omega), show min k x.length = x.length from by omega, hrd,
        show min (k + 1) x.length = x.length from by omega, if_neg (by omega)]

/-- The full clock. -/
def rdClock (N X L : ℕ) : ℕ :=
  rdRounds N X L N + (2 * N + (2 + (2 * N + (2 + (4 * X + 2)))))

/-- **The x-splicer runs to completion.**  On `unaryD N ++ (xVis x 0 ++ encodeD out)` the machine halts by
itself at the explicit clock with tape **exactly**
`unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N))` — the first `N` input bits (default `false` past
the end) spliced doubled into the output, the bound restored, **every cursor healed**. -/
theorem readX_run (N : ℕ) (x out : List Bool) :
    run readXMachine (rdClock N x.length out.length)
      (init readXMachine (unaryD N ++ (xVis x 0 ++ encodeD out)))
      = ⟨(32, false), 2 * N + 2 + 4 * x.length + 1,
          unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N))⟩ := by
  rw [init_rx, ← cntT_zero, rdClock, run_add, run_rd_rounds N x out N (le_refl N) false,
    ite_self]
  have f1 := rx_skipDs (cntT N N ++ (xVis x (min N x.length)
      ++ encodeD (out ++ bitsUpTo x N))) 0 N false
    (fun i hi => ⟨by simpa using cntE_mark_lo N N _ i hi,
                  by simpa using cntE_mark_hi N N _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := rx_toRstD (s := if N = 0 then false else true) (p := 2 * N)
    (T := cntT N N ++ (xVis x (min N x.length) ++ encodeD (out ++ bitsUpTo x N)))
    (cntE_cm_lo N N _ (le_refl N)) (cntE_cm_hi N N _ (le_refl N))
  have f3 := rx_healDs N (xVis x (min N x.length) ++ encodeD (out ++ bitsUpTo x N)) false N
    (le_refl N)
  have f4 := rx_crossHD (s := if N = 0 then false else true) (p := 2 * N)
    (T := hlT N N ++ (xVis x (min N x.length) ++ encodeD (out ++ bitsUpTo x N)))
    (hlE_cm_lo N _) (hlE_cm_hi N _)
  have hua : (unaryD N).length = 2 * N + 2 := unaryD_length N
  have f5 := rx_healXs (unaryD N) N x (min N x.length) (encodeD (out ++ bitsUpTo x N)) hua
    (by omega) false (min N x.length) (le_refl _)
  rw [xHl_zero, xHl_sat x (min N x.length) (min N x.length) (le_refl _)] at f5
  have f6 := rx_healSkips (unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N)))
    (2 * N + 2 + 4 * min N x.length) (x.length - min N x.length)
    (if min N x.length = 0 then false else true)
    (fun i hi => ⟨x.getD (min N x.length + i) false, by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i
            = 2 * N + 2 + (4 * (min N x.length + i)) from by omega]
        exact liftJ _ _ hua (xVisE_val_lo x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 1
            = 2 * N + 2 + (4 * (min N x.length + i) + 1) from by omega]
        exact liftJ _ _ hua (xVisE_val_hi x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 2
            = 2 * N + 2 + (4 * (min N x.length + i) + 2) from by omega]
        exact liftJ _ _ hua (xVisE_cur_lo x 0 _ _ (by omega)), by
        rw [show 2 * N + 2 + 4 * min N x.length + 4 * i + 3
            = 2 * N + 2 + (4 * (min N x.length + i) + 3) from by omega]
        exact liftJ _ _ hua (xVisE_cur_hi_unvis x 0 _ _ (by omega) (by omega))⟩)
  rw [show 2 * N + 2 + 4 * min N x.length + 4 * (x.length - min N x.length)
      = 2 * N + 2 + 4 * x.length from by omega] at f6
  have f7 := rx_two_healDone
    (s := if x.length - min N x.length = 0 then (if min N x.length = 0 then false else true)
      else true)
    (p := 2 * N + 2 + 4 * x.length)
    (T := unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N)))
    (by rw [show 2 * N + 2 + 4 * x.length = 2 * N + 2 + (4 * x.length) from rfl]
        exact liftJ _ _ hua (xVisE_term_lo x 0 _))
    (by rw [show 2 * N + 2 + 4 * x.length + 1 = 2 * N + 2 + (4 * x.length + 1) from by omega]
        exact liftJ _ _ hua (xVisE_term_hi x 0 _))
  rw [show 2 * N + (2 + (2 * N + (2 + (4 * x.length + 2))))
      = 2 * N + (2 + (2 * N + (2 + (4 * min N x.length
          + (4 * (x.length - min N x.length) + 2))))) from by omega,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, run_add, f4, hlT_last, run_add, f5,
    run_add, f6, f7, cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem readX_halted (N : ℕ) (x out : List Bool) :
    readXMachine.halt
      (run readXMachine (rdClock N x.length out.length)
        (init readXMachine (unaryD N ++ (xVis x 0 ++ encodeD out)))).st = true := by
  rw [readX_run]; rfl

/-- **The x-splicer's output.** -/
theorem readX_output (N : ℕ) (x out : List Bool) :
    (run readXMachine (rdClock N x.length out.length)
      (init readXMachine (unaryD N ++ (xVis x 0 ++ encodeD out)))).tp
      = unaryD N ++ (xVis x 0 ++ encodeD (out ++ bitsUpTo x N)) := by
  rw [readX_run]

/-! ## Polynomial clock bounds -/

theorem rdRounds_le (N X L k : ℕ) (hk : k ≤ N) :
    rdRounds N X L k ≤ k * (4 * N + 4 * X + 2 * (L + N) + 12) := by
  induction k with
  | zero => simp [rdRounds]
  | succ k ih =>
    calc rdRounds N X L (k + 1)
        = rdRounds N X L k + (2 * N + 2 * k + 4 * X + 2 * (L + k) + 12) := rfl
      _ ≤ k * (4 * N + 4 * X + 2 * (L + N) + 12)
          + (4 * N + 4 * X + 2 * (L + N) + 12) :=
          Nat.add_le_add (ih (by omega)) (by omega)
      _ = (k + 1) * (4 * N + 4 * X + 2 * (L + N) + 12) := by ring

/-- **The clock is polynomial** (explicit, quadratic). -/
theorem rdClock_le (N X L : ℕ) :
    rdClock N X L ≤ N * (4 * N + 4 * X + 2 * (L + N) + 12) + (4 * N + 4 * X + 6) := by
  have h := rdRounds_le N X L N (le_refl N)
  rw [rdClock]
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX