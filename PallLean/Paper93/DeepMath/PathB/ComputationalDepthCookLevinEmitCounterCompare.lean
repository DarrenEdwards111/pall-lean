import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterIncr

/-!
# Cook–Levin M2 emitter, E1 (ii) — the unary counter comparison machine (`a ≤ b`)

Third brick of the emitter sub-project (`SCOPE_EMITTER.md` §3, E1).  The emitter's loop harness (E4) needs the
bound tests `t ≤ B`, `p ≤ P` on unary counters.  This file builds the **comparison** of two adjacent doubled
unary counters (`unaryD a ++ unaryD b`) as an actual `ComposableMachine`, and proves it **self-halting and
correct with a quadratic clock**.

The algorithm is the doubled-tape marking scheme: a `11` data pair can be **marked** to `10` (still detectably
distinct from data `11`, boundary `01`, and blank `00` — the four pair values are the tape's only alphabet).
Each **round** marks one unprocessed data pair in `A`, seeks across `A`'s `01` boundary, and marks one
unprocessed data pair in `B`, returning to the origin with the `reset` move.  Whichever counter exhausts first
decides: `A` exhausted first (its boundary reached in the find phase) ⇒ `a ≤ b`, accept; `B` exhausted first
⇒ `a > b`, reject.  Proved:

* the marked-tape descriptor `cmpT` with its full `getD` suite and the two structural mark-write lemmas;
* per-phase step lemmas, the two-step pair lemmas, and the three scan run-invariants;
* the **round invariant** (`run_round`): one round transforms `cmpT a b j j` to `cmpT a b (j+1) (j+1)` in
  exactly `2a + 2j + 4` steps;
* **the top theorems** (`compare_halts`, `compare_decides`): on `unaryD a ++ unaryD b` the machine halts by
  itself at the explicit clock `cmpClock a b` with `accept = decide (a ≤ b)`, and
  `cmpClock a b ≤ 3(a+b+2)²` (`cmpClock_le`) — a genuine self-terminating comparison with a quadratic clock.

Scope notes, per the standing rules: the comparison is **destructive** (the counters end marked); the emitter's
harness performs bound tests on scratch copies produced by the E1 copy brick (next), exactly as scoped —
copy-with-preservation plus destructive compare compose to a non-destructive bound test.  The spec is proved on
well-formed two-counter tapes, the same promise form as M1.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr

/-! ## Generic positioned append lemmas -/

/-- `getD` past a prefix of known length. -/
theorem getD_append_left_length' {α : Type} (l₁ l₂ : List α) {k : ℕ} (hk : l₁.length = k)
    (i : ℕ) (d : α) : (l₁ ++ l₂).getD (k + i) d = l₂.getD i d := by
  subst hk
  rw [List.getD_append_right (h := by omega), Nat.add_sub_cancel_left]

/-- `set` past a prefix of known length. -/
theorem set_append_left_length' {α : Type} (l₁ l₂ : List α) {k : ℕ} (hk : l₁.length = k)
    (i : ℕ) (w : α) : (l₁ ++ l₂).set (k + i) w = l₁ ++ l₂.set i w := by
  subst hk
  exact set_append_left_length l₁ l₂ i w

/-- Two leading cells as an append block. -/
theorem cons_cons_append {α : Type} (x y : α) (X : List α) :
    x :: y :: X = [x, y] ++ X := rfl

/-! ## The marked-pairs region -/

/-- `j` processed pairs: each a `10` — detectably distinct from data `11`, boundary `01`, and blank `00`. -/
def markedD : ℕ → List Bool
  | 0 => []
  | j + 1 => true :: false :: markedD j

theorem markedD_length (j : ℕ) : (markedD j).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (true :: false :: markedD j).length = 2 * (j + 1)
    simp only [List.length_cons, ih]
    omega

/-- Marked pairs are all identical, so appending one on the right is prepending one on the left. -/
theorem markedD_snoc (j : ℕ) : markedD j ++ [true, false] = markedD (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (true :: false :: markedD j) ++ [true, false] = true :: false :: markedD (j + 1)
    rw [List.cons_append, List.cons_append, ih]

/-- A processed pair's low cell reads `true`. -/
theorem markedD_getD_lo (j i : ℕ) (h : i < j) : (markedD j).getD (2 * i) false = true := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show (true :: false :: markedD j).getD (2 * (i + 1)) false = true
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i (by omega)

/-- A processed pair's high cell reads `false`. -/
theorem markedD_getD_hi (j i : ℕ) (h : i < j) : (markedD j).getD (2 * i + 1) false = false := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show (true :: false :: markedD j).getD (2 * (i + 1) + 1) false = false
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i (by omega)

/-! ## The two-counter marked tape -/

/-- The comparison tape with `jA` pairs of `A` and `jB` pairs of `B` processed:
`10^jA 11^(a-jA) 01 10^jB 11^(b-jB) 01` (right-associated for positional reasoning). -/
def cmpT (a b jA jB : ℕ) : List Bool :=
  markedD jA ++ (List.replicate (2 * (a - jA)) true ++ ([false, true]
    ++ (markedD jB ++ (List.replicate (2 * (b - jB)) true ++ [false, true]))))

/-- The unprocessed comparison tape is exactly the two adjacent counters. -/
theorem cmpT_zero (a b : ℕ) : cmpT a b 0 0 = unaryD a ++ unaryD b := by
  simp [cmpT, markedD, unaryD_eq, List.append_assoc]

theorem cmpT_length (a b jA jB : ℕ) (hA : jA ≤ a) (hB : jB ≤ b) :
    (cmpT a b jA jB).length = 2 * a + 2 * b + 4 := by
  simp only [cmpT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-! ### The `getD` suite -/

theorem cmpT_getD_Amark_lo (a b jA jB i : ℕ) (h : i < jA) :
    (cmpT a b jA jB).getD (2 * i) false = true := by
  rw [cmpT, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jA i h

theorem cmpT_getD_Amark_hi (a b jA jB i : ℕ) (h : i < jA) :
    (cmpT a b jA jB).getD (2 * i + 1) false = false := by
  rw [cmpT, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jA i h

theorem cmpT_getD_Adata (a b jA jB c : ℕ) (hA : jA ≤ a) (h1 : 2 * jA ≤ c) (h2 : c < 2 * a) :
    (cmpT a b jA jB).getD c false = true := by
  rw [cmpT, show c = 2 * jA + (c - 2 * jA) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem cmpT_getD_Aend_lo (a b jA jB : ℕ) (hA : jA ≤ a) :
    (cmpT a b jA jB).getD (2 * a) false = false := by
  rw [cmpT, show 2 * a = 2 * jA + (2 * (a - jA) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cmpT_getD_Aend_hi (a b jA jB : ℕ) (hA : jA ≤ a) :
    (cmpT a b jA jB).getD (2 * a + 1) false = true := by
  rw [cmpT, show 2 * a + 1 = 2 * jA + (2 * (a - jA) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cmpT_getD_Bmark_lo (a b jA jB i : ℕ) (hA : jA ≤ a) (h : i < jB) :
    (cmpT a b jA jB).getD (2 * a + 2 + 2 * i) false = true := by
  rw [cmpT, show 2 * a + 2 + 2 * i = 2 * jA + (2 * (a - jA) + (2 + 2 * i)) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jB i h

theorem cmpT_getD_Bmark_hi (a b jA jB i : ℕ) (hA : jA ≤ a) (h : i < jB) :
    (cmpT a b jA jB).getD (2 * a + 2 + 2 * i + 1) false = false := by
  rw [cmpT, show 2 * a + 2 + 2 * i + 1 = 2 * jA + (2 * (a - jA) + (2 + (2 * i + 1))) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jB i h

theorem cmpT_getD_Bdata (a b jA jB c : ℕ) (hA : jA ≤ a) (hB : jB ≤ b)
    (h1 : 2 * jB ≤ c) (h2 : c < 2 * b) :
    (cmpT a b jA jB).getD (2 * a + 2 + c) false = true := by
  rw [cmpT, show 2 * a + 2 + c = 2 * jA + (2 * (a - jA) + (2 + (2 * jB + (c - 2 * jB))))
      from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ (markedD_length jB),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem cmpT_getD_Bend_lo (a b jA jB : ℕ) (hA : jA ≤ a) (hB : jB ≤ b) :
    (cmpT a b jA jB).getD (2 * a + 2 + 2 * b) false = false := by
  rw [cmpT, show 2 * a + 2 + 2 * b
        = 2 * jA + (2 * (a - jA) + (2 + (2 * jB + (2 * (b - jB) + 0)))) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ (markedD_length jB),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cmpT_getD_Bend_hi (a b jA jB : ℕ) (hA : jA ≤ a) (hB : jB ≤ b) :
    (cmpT a b jA jB).getD (2 * a + 2 + 2 * b + 1) false = true := by
  rw [cmpT, show 2 * a + 2 + 2 * b + 1
        = 2 * jA + (2 * (a - jA) + (2 + (2 * jB + (2 * (b - jB) + 1)))) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    getD_append_left_length' _ _ (markedD_length jB),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ### The two structural mark-write lemmas -/

/-- Marking `A`'s next data pair (write `false` over the high cell of pair `jA`). -/
theorem cmpT_markA (a b jA jB : ℕ) (hja : jA < a) (hjb : jB ≤ b) :
    writeAt (cmpT a b jA jB) (2 * jA + 1) false = cmpT a b (jA + 1) jB := by
  rw [writeAt_of_lt false (by rw [cmpT_length a b jA jB (by omega) hjb]; omega), cmpT,
    set_append_left_length' _ _ (markedD_length jA),
    show 2 * (a - jA) = 2 * (a - jA - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show a - jA - 1 = a - (jA + 1) from by omega]
  rfl

/-- Marking `B`'s next data pair (write `false` over the high cell of pair `jB` of `B`). -/
theorem cmpT_markB (a b jA jB : ℕ) (hA : jA ≤ a) (hjb : jB < b) :
    writeAt (cmpT a b jA jB) (2 * a + 2 + 2 * jB + 1) false = cmpT a b jA (jB + 1) := by
  rw [writeAt_of_lt false (by rw [cmpT_length a b jA jB hA (by omega)]; omega), cmpT,
    show 2 * a + 2 + 2 * jB + 1 = 2 * jA + (2 * (a - jA) + (2 + (2 * jB + 1))) from by omega,
    set_append_left_length' _ _ (markedD_length jA),
    set_append_left_length' _ _ List.length_replicate,
    set_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl),
    set_append_left_length' _ _ (markedD_length jB),
    show 2 * (b - jB) = 2 * (b - jB - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append true false (List.replicate (2 * (b - jB - 1)) true ++ [false, true]),
    ← List.append_assoc (markedD jB) [true, false]
      (List.replicate (2 * (b - jB - 1)) true ++ [false, true]),
    markedD_snoc, show b - jB - 1 = b - (jB + 1) from by omega]
  rfl

/-! ## The comparison machine

Control: `State = Fin 8 × Bool` (stored low cell).  Phases: `0/1` find in `A` (skip `10`, mark `11` ⇒ seek,
boundary `01` ⇒ **accept**), `2/3` seek across `A`'s remaining data to its boundary, `4/5` find in `B` (skip
`10`, mark `11` and **reset** to the origin for the next round, boundary `01` ⇒ **reject**), `6` = accept halt,
`7` = reject halt. -/

def compareMachine : Machine where
  State := Fin 8 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 6) || decide (s.1 = 7)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
       else (if b then ((6, s.2), none, 2) else ((7, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then (if b then ((2, s.2), none, 1) else ((7, s.2), none, 2))
       else (if b then ((4, s.2), none, 1) else ((7, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if s.2 then (if b then ((0, s.2), some false, 3) else ((4, s.2), none, 1))
       else (if b then ((7, s.2), none, 2) else ((7, s.2), none, 2)))
    else ((s.1, s.2), none, 2)
  accept := fun s => decide (s.1 = 6)

theorem init_cmp (x : List Bool) : init compareMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

/-- Find-in-`A`, low cell: read, store, advance. -/
theorem step_c0 {s : Bool} {p : ℕ} {T : List Bool} :
    step compareMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, compareMachine, moveHead]; rfl

/-- Find-in-`A`, high cell over a `11` data pair: mark it (`11 ↦ 10`), advance, seek. -/
theorem step_c1_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(1, true), p, T⟩ = ⟨(2, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Find-in-`A`, high cell over a `10` processed pair: skip. -/
theorem step_c1_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step compareMachine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Find-in-`A`, high cell over the `01` boundary: `A` exhausted first ⇒ **accept**. -/
theorem step_c1_acc {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(1, false), p, T⟩ = ⟨(6, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Seek, low cell: read, store, advance. -/
theorem step_c2 {s : Bool} {p : ℕ} {T : List Bool} :
    step compareMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, compareMachine, moveHead]; rfl

/-- Seek, high cell over a `11` data pair: continue seeking. -/
theorem step_c3_data {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(3, true), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Seek, high cell over the `01` boundary: crossed into `B`'s region. -/
theorem step_c3_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(3, false), p, T⟩ = ⟨(4, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Find-in-`B`, low cell: read, store, advance. -/
theorem step_c4 {s : Bool} {p : ℕ} {T : List Bool} :
    step compareMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
  simp only [step, compareMachine, moveHead]; rfl

/-- Find-in-`B`, high cell over a `11` data pair: mark it and **reset** to the origin (next round). -/
theorem step_c5_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(5, true), p, T⟩ = ⟨(0, true), 0, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Find-in-`B`, high cell over a `10` processed pair: skip. -/
theorem step_c5_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step compareMachine ⟨(5, true), p, T⟩ = ⟨(4, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-- Find-in-`B`, high cell over the `01` boundary: `B` exhausted while `A` was not ⇒ **reject**. -/
theorem step_c5_rej {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step compareMachine ⟨(5, false), p, T⟩ = ⟨(7, false), p, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, compareMachine, moveHead, h]

/-! ### Pair-step lemmas -/

/-- Skip a `10` processed pair in the find-in-`A` phase. -/
theorem run_two_skip01 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run compareMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_skip h2]

/-- Mark a `11` data pair in the find-in-`A` phase and enter the seek. -/
theorem run_two_markA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_mark h2]

/-- Hit the `01` boundary in the find-in-`A` phase: accept. -/
theorem run_two_acc {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(0, s), p, T⟩ = ⟨(6, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_acc h2]

/-- Seek across a `11` data pair. -/
theorem run_two_seek {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c2, h1, step_c3_data h2]

/-- Cross the `01` boundary out of `A`'s region. -/
theorem run_two_cross {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c2, h1, step_c3_cross h2]

/-- Skip a `10` processed pair in the find-in-`B` phase. -/
theorem run_two_skip45 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run compareMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c4, h1, step_c5_skip h2]

/-- Mark a `11` data pair in the find-in-`B` phase and reset for the next round. -/
theorem run_two_markB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(4, s), p, T⟩ = ⟨(0, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_c4, h1, step_c5_mark h2]

/-- Hit the `01` boundary in the find-in-`B` phase: reject. -/
theorem run_two_rej {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run compareMachine 2 ⟨(4, s), p, T⟩ = ⟨(7, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c4, h1, step_c5_rej h2]

/-! ### Scan run-invariants -/

/-- Skip `k` processed pairs in the find-in-`A` phase. -/
theorem run_skip01 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run compareMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skip01 hk.1 hk.2]
    rfl

/-- Seek across `k` data pairs. -/
theorem run_seek (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run compareMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seek hk.1 hk.2]
    rfl

/-- Skip `k` processed pairs in the find-in-`B` phase. -/
theorem run_skip45 (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run compareMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skip45 hk.1 hk.2]
    rfl

/-! ## The round invariant -/

/-- **One full round.**  From the origin on `cmpT a b j j` (both counters unexhausted), `2a + 2j + 4` steps
mark one pair in each region and return to the origin: the tape advances to `cmpT a b (j+1) (j+1)`. -/
theorem run_round (a b j : ℕ) (hja : j < a) (hjb : j < b) (s : Bool) :
    run compareMachine (2 * a + 2 * j + 4) ⟨(0, s), 0, cmpT a b j j⟩
      = ⟨(0, true), 0, cmpT a b (j + 1) (j + 1)⟩ := by
  -- Stage 1: skip the `j` processed pairs of `A`.
  have st1 := run_skip01 (cmpT a b j j) 0 j s (fun i hi =>
    ⟨by simpa using cmpT_getD_Amark_lo a b j j i hi,
     by simpa using cmpT_getD_Amark_hi a b j j i hi⟩)
  simp only [Nat.zero_add] at st1
  -- Stage 2: mark `A`'s pair `j`.
  have st2 := run_two_markA (s := if j = 0 then s else true) (p := 2 * j) (T := cmpT a b j j)
    (cmpT_getD_Adata a b j j (2 * j) (by omega) (by omega) (by omega))
    (cmpT_getD_Adata a b j j (2 * j + 1) (by omega) (by omega) (by omega))
  rw [cmpT_markA a b j j hja (by omega)] at st2
  -- Stage 3: seek across `A`'s remaining `a - j - 1` data pairs.
  have st3 := run_seek (cmpT a b (j + 1) j) (2 * j + 2) (a - j - 1) true (fun i hi =>
    ⟨cmpT_getD_Adata a b (j + 1) j (2 * j + 2 + 2 * i) (by omega) (by omega) (by omega),
     cmpT_getD_Adata a b (j + 1) j (2 * j + 2 + 2 * i + 1) (by omega) (by omega) (by omega)⟩)
  rw [show 2 * j + 2 + 2 * (a - j - 1) = 2 * a from by omega] at st3
  simp only [ite_self] at st3
  -- Stage 4: cross `A`'s boundary.
  have st4 := run_two_cross (s := true) (p := 2 * a)
    (T := cmpT a b (j + 1) j)
    (cmpT_getD_Aend_lo a b (j + 1) j (by omega)) (cmpT_getD_Aend_hi a b (j + 1) j (by omega))
  -- Stage 5: skip the `j` processed pairs of `B`.
  have st5 := run_skip45 (cmpT a b (j + 1) j) (2 * a + 2) j false (fun i hi =>
    ⟨cmpT_getD_Bmark_lo a b (j + 1) j i (by omega) hi,
     cmpT_getD_Bmark_hi a b (j + 1) j i (by omega) hi⟩)
  -- Stage 6: mark `B`'s pair `j` and reset.
  have st6 := run_two_markB (s := if j = 0 then false else true) (p := 2 * a + 2 + 2 * j)
    (T := cmpT a b (j + 1) j)
    (cmpT_getD_Bdata a b (j + 1) j (2 * j) (by omega) (by omega) (by omega) (by omega))
    (cmpT_getD_Bdata a b (j + 1) j (2 * j + 1) (by omega) (by omega) (by omega) (by omega))
  rw [cmpT_markB a b (j + 1) j (by omega) hjb] at st6
  -- Assemble the round.
  rw [show 2 * a + 2 * j + 4 = 2 * j + (2 + (2 * (a - j - 1) + (2 + (2 * j + 2)))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4,
    show 2 * j + 2 = 2 * j + 2 from rfl, run_add, st5, st6]

/-! ## The rounds and their clock -/

/-- The cumulative clock of the first `k` rounds. -/
def cmpRounds (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cmpRounds a k + (2 * a + 2 * k + 4)

theorem cmpRounds_eq (a k : ℕ) : cmpRounds a k = 2 * a * k + k * k + 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cmpRounds]; rw [ih]; ring

/-- **Rounds invariant.**  While neither counter is exhausted, `k` rounds process `k` pairs of each. -/
theorem run_rounds (a b k : ℕ) (hka : k ≤ a) (hkb : k ≤ b) (s : Bool) :
    run compareMachine (cmpRounds a k) ⟨(0, s), 0, cmpT a b 0 0⟩
      = ⟨(0, if k = 0 then s else true), 0, cmpT a b k k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show cmpRounds a (k + 1) = cmpRounds a k + (2 * a + 2 * k + 4) from rfl, run_add,
      ih (by omega) (by omega), run_round a b k (by omega) (by omega), if_neg (by omega)]

/-! ## The endgames -/

/-- **Accept endgame** (`a ≤ b`): after `a` full rounds `A` is exhausted; the find phase skips its `a`
processed pairs, hits its `01` boundary, and accepts. -/
theorem compare_run_le (a b : ℕ) (hab : a ≤ b) :
    run compareMachine (cmpRounds a a + (2 * a + 2)) (init compareMachine (unaryD a ++ unaryD b))
      = ⟨(6, false), 2 * a + 1, cmpT a b a a⟩ := by
  rw [init_cmp, ← cmpT_zero, run_add, run_rounds a b a (le_refl a) hab false]
  have st1 := run_skip01 (cmpT a b a a) 0 a (if a = 0 then false else true) (fun i hi =>
    ⟨by simpa using cmpT_getD_Amark_lo a b a a i hi,
     by simpa using cmpT_getD_Amark_hi a b a a i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_acc (s := if a = 0 then (if a = 0 then false else true) else true)
    (p := 2 * a) (T := cmpT a b a a)
    (cmpT_getD_Aend_lo a b a a (le_refl a)) (cmpT_getD_Aend_hi a b a a (le_refl a))
  rw [show 2 * a + 2 = 2 * a + 2 from rfl, run_add, st1, st2]

/-- **Reject endgame** (`b < a`): after `b` full rounds `B` is exhausted but `A` is not; the find phase marks
`A`'s pair `b`, the seek crosses, and the find-in-`B` phase hits `B`'s `01` boundary and rejects.  The total
clock is exactly `cmpRounds a (b + 1)` — one more round's worth, the round that fails at `B`. -/
theorem compare_run_gt (a b : ℕ) (hab : b < a) :
    run compareMachine (cmpRounds a (b + 1)) (init compareMachine (unaryD a ++ unaryD b))
      = ⟨(7, false), 2 * a + 2 + 2 * b + 1, cmpT a b (b + 1) b⟩ := by
  rw [init_cmp, ← cmpT_zero,
    show cmpRounds a (b + 1)
        = cmpRounds a b + (2 * b + (2 + (2 * (a - b - 1) + (2 + (2 * b + 2))))) from by
      simp only [cmpRounds]; omega,
    run_add, run_rounds a b b (by omega) (le_refl b) false]
  -- Stage 1: skip the `b` processed pairs of `A`.
  have st1 := run_skip01 (cmpT a b b b) 0 b (if b = 0 then false else true) (fun i hi =>
    ⟨by simpa using cmpT_getD_Amark_lo a b b b i hi,
     by simpa using cmpT_getD_Amark_hi a b b b i hi⟩)
  simp only [Nat.zero_add] at st1
  -- Stage 2: mark `A`'s pair `b` (it exists: `b < a`).
  have st2 := run_two_markA (s := if b = 0 then (if b = 0 then false else true) else true)
    (p := 2 * b) (T := cmpT a b b b)
    (cmpT_getD_Adata a b b b (2 * b) (by omega) (by omega) (by omega))
    (cmpT_getD_Adata a b b b (2 * b + 1) (by omega) (by omega) (by omega))
  rw [cmpT_markA a b b b hab (le_refl b)] at st2
  -- Stage 3: seek across `A`'s remaining data pairs.
  have st3 := run_seek (cmpT a b (b + 1) b) (2 * b + 2) (a - b - 1) true (fun i hi =>
    ⟨cmpT_getD_Adata a b (b + 1) b (2 * b + 2 + 2 * i) (by omega) (by omega) (by omega),
     cmpT_getD_Adata a b (b + 1) b (2 * b + 2 + 2 * i + 1) (by omega) (by omega) (by omega)⟩)
  rw [show 2 * b + 2 + 2 * (a - b - 1) = 2 * a from by omega] at st3
  simp only [ite_self] at st3
  -- Stage 4: cross `A`'s boundary.
  have st4 := run_two_cross (s := true) (p := 2 * a)
    (T := cmpT a b (b + 1) b)
    (cmpT_getD_Aend_lo a b (b + 1) b (by omega)) (cmpT_getD_Aend_hi a b (b + 1) b (by omega))
  -- Stage 5: skip the `b` processed pairs of `B`.
  have st5 := run_skip45 (cmpT a b (b + 1) b) (2 * a + 2) b false (fun i hi =>
    ⟨cmpT_getD_Bmark_lo a b (b + 1) b i (by omega) hi,
     cmpT_getD_Bmark_hi a b (b + 1) b i (by omega) hi⟩)
  -- Stage 6: hit `B`'s boundary — reject.
  have st6 := run_two_rej (s := if b = 0 then false else true) (p := 2 * a + 2 + 2 * b)
    (T := cmpT a b (b + 1) b)
    (cmpT_getD_Bend_lo a b (b + 1) b (by omega) (le_refl b))
    (cmpT_getD_Bend_hi a b (b + 1) b (by omega) (le_refl b))
  rw [run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, st6]

/-! ## The packaged comparison: self-halting, correct, quadratic clock -/

/-- The comparison's explicit clock. -/
def cmpClock (a b : ℕ) : ℕ :=
  if a ≤ b then cmpRounds a a + (2 * a + 2) else cmpRounds a (b + 1)

/-- **The comparison halts by itself** at its clock. -/
theorem compare_halts (a b : ℕ) :
    compareMachine.halt
      (run compareMachine (cmpClock a b) (init compareMachine (unaryD a ++ unaryD b))).st
      = true := by
  rw [cmpClock]
  rcases le_or_gt a b with hab | hab
  · rw [if_pos hab, compare_run_le a b hab]; rfl
  · rw [if_neg (by omega), compare_run_gt a b hab]; rfl

/-- **The comparison is correct**: the accept bit at the clock is exactly `decide (a ≤ b)`. -/
theorem compare_decides (a b : ℕ) :
    compareMachine.accept
      (run compareMachine (cmpClock a b) (init compareMachine (unaryD a ++ unaryD b))).st
      = decide (a ≤ b) := by
  rw [cmpClock]
  rcases le_or_gt a b with hab | hab
  · rw [if_pos hab, compare_run_le a b hab]
    simp [compareMachine, hab]
  · rw [if_neg (by omega), compare_run_gt a b hab]
    simp [compareMachine]
    omega

/-- **The clock is quadratic**: `cmpClock a b ≤ 3(a + b + 2)²`. -/
theorem cmpClock_le (a b : ℕ) : cmpClock a b ≤ 3 * (a + b + 2) * (a + b + 2) := by
  rw [cmpClock]
  rcases le_or_gt a b with hab | hab
  · rw [if_pos hab, cmpRounds_eq]
    nlinarith
  · rw [if_neg (by omega), cmpRounds_eq]
    nlinarith

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
