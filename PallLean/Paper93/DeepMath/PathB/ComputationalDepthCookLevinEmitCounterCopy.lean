import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterCompare

/-!
# Cook–Levin M2 emitter, E1 (iii) — the unary counter copy machine (with preservation)

Fourth brick of the emitter sub-project (`SCOPE_EMITTER.md` §3, E1), completing the counter ops.  The
comparison brick is destructive, so the harness needs **copy-with-preservation**: on tape `unaryD n`, produce
`unaryD n ++ unaryD n` — the original counter intact, its copy appended after it.

The algorithm composes the two doubled-tape boundary mechanisms: the `10` **processed mark** (as in the
comparison) and the `00` **blank end** (reads past the tape end return `false`, so a blank pair is the
detectable end of the grown copy region — no terminator needed while it grows).  Three passes:

1. **Copy rounds** (`run_copy_round`): find the next unprocessed `11` pair of `A` (skipping `10`s), mark it,
   seek right across everything (`A`'s rest, its `01` boundary, the copy so far — all high cells read `true`)
   to the first blank pair, append a `11` pair there, reset.  Round `j` costs exactly `2n + 2j + 6` steps.
2. **Restore pass** (`run_restore`): when the find phase hits `A`'s `01` boundary, all of `A` is marked and the
   copy is complete; heal `A`'s `10` pairs back to `11` left-to-right — this is what makes the copy
   **preserving**.
3. **Terminator write**: seek across the copy's `11` pairs to the blank end and write the copy's own `01`
   boundary; halt.

Proved: the two tape descriptors (`cpyT` for the rounds, `resT` for the restore) with full `getD` suites and
the four structural write lemmas; all step/pair-step lemmas and four scan run-invariants; the round and rounds
invariants with an explicit clock (`cpyRounds`, closed form proved); and **the top theorems**
(`copy_run`/`copy_halted`/`copy_output`): the machine **halts by itself** at the explicit clock
`cpyClock n = 3n² + 11n + 6` (`cpyClock_eq`, bounded by `3(n+2)²` in `cpyClock_le`) with tape **exactly**
`unaryD n ++ unaryD n` — copy and preservation in one equation.

Same well-formed-input promise form as M1 and the other E1 bricks.  With increment, comparison, and copy all
landed, E1 is complete; next is E3 (template emitters).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare

/-! ## Two more generic append lemmas -/

/-- `getD` at exactly a prefix's length. -/
theorem getD_append_length' {α : Type} (l₁ l₂ : List α) {k : ℕ} (hk : l₁.length = k) (d : α) :
    (l₁ ++ l₂).getD k d = l₂.getD 0 d := by
  subst hk
  rw [List.getD_append_right (h := le_refl _), Nat.sub_self]

/-- One past the tape end, `writeAt` pads a `false` cell then appends the write — exactly a `01` pair when
`w = true`. -/
theorem writeAt_append_end1 (l : List Bool) (w : Bool) :
    writeAt l (l.length + 1) w = l ++ [false, w] := by
  unfold writeAt
  rw [show l.length + 1 + 1 - l.length = 2 from by omega,
    show List.replicate 2 false = [false, false] from rfl,
    set_append_left_length' l [false, false] rfl 1 w]
  rfl

/-! ## The rounds descriptor `cpyT` -/

/-- The copy tape with `jA` pairs of `A` processed and `jC` pairs copied:
`10^jA 11^(n-jA) 01 11^jC` — the copy region has **no terminator**; the tape end is its detectable boundary. -/
def cpyT (n jA jC : ℕ) : List Bool :=
  markedD jA ++ (List.replicate (2 * (n - jA)) true ++ ([false, true]
    ++ List.replicate (2 * jC) true))

/-- The initial copy tape is exactly the input counter. -/
theorem cpyT_zero (n : ℕ) : cpyT n 0 0 = unaryD n := by
  simp [cpyT, markedD, unaryD_eq]

theorem cpyT_length (n jA jC : ℕ) (hA : jA ≤ n) :
    (cpyT n jA jC).length = 2 * n + 2 + 2 * jC := by
  simp only [cpyT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-! ### The `getD` suite -/

theorem cpyT_getD_Amark_lo (n jA jC i : ℕ) (h : i < jA) :
    (cpyT n jA jC).getD (2 * i) false = true := by
  rw [cpyT, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo jA i h

theorem cpyT_getD_Amark_hi (n jA jC i : ℕ) (h : i < jA) :
    (cpyT n jA jC).getD (2 * i + 1) false = false := by
  rw [cpyT, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi jA i h

theorem cpyT_getD_Adata (n jA jC c : ℕ) (hA : jA ≤ n) (h1 : 2 * jA ≤ c) (h2 : c < 2 * n) :
    (cpyT n jA jC).getD c false = true := by
  rw [cpyT, show c = 2 * jA + (c - 2 * jA) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem cpyT_getD_marker_lo (n jA jC : ℕ) (hA : jA ≤ n) :
    (cpyT n jA jC).getD (2 * n) false = false := by
  rw [cpyT, show 2 * n = 2 * jA + (2 * (n - jA) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cpyT_getD_marker_hi (n jA jC : ℕ) (hA : jA ≤ n) :
    (cpyT n jA jC).getD (2 * n + 1) false = true := by
  rw [cpyT, show 2 * n + 1 = 2 * jA + (2 * (n - jA) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cpyT_getD_C (n jA jC c : ℕ) (hA : jA ≤ n) (h1 : 2 * n + 2 ≤ c)
    (h2 : c < 2 * n + 2 + 2 * jC) :
    (cpyT n jA jC).getD c false = true := by
  rw [cpyT, show c = 2 * jA + (2 * (n - jA) + (2 + (c - 2 * n - 2))) from by omega,
    getD_append_left_length' _ _ (markedD_length jA),
    getD_append_left_length' _ _ List.length_replicate,
    getD_append_left_length' _ _ (show ([false, true] : List Bool).length = 2 from rfl)]
  exact List.getD_replicate _ (h := by omega)

theorem cpyT_getD_pastEnd (n jA jC c : ℕ) (hA : jA ≤ n) (hc : 2 * n + 2 + 2 * jC ≤ c) :
    (cpyT n jA jC).getD c false = false :=
  List.getD_eq_default _ _ (by rw [cpyT_length n jA jC hA]; omega)

/-! ### The two structural write lemmas of the rounds -/

/-- Marking `A`'s next data pair. -/
theorem cpyT_mark (n j : ℕ) (hj : j < n) :
    writeAt (cpyT n j j) (2 * j + 1) false = cpyT n (j + 1) j := by
  rw [writeAt_of_lt false (by rw [cpyT_length n j j (by omega)]; omega), cpyT,
    set_append_left_length' _ _ (markedD_length j),
    show 2 * (n - j) = 2 * (n - j - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show n - j - 1 = n - (j + 1) from by omega]
  rfl

/-- Growing the copy: the two `true` writes at the blank end append a `11` pair. -/
theorem cpyT_grow (n j : ℕ) (hj : j < n) :
    writeAt (writeAt (cpyT n (j + 1) j) (2 * n + 2 * j + 2) true) (2 * n + 2 * j + 3) true
      = cpyT n (j + 1) (j + 1) := by
  have hl1 : (cpyT n (j + 1) j).length = 2 * n + 2 * j + 2 := by
    rw [cpyT_length n (j + 1) j (by omega)]; ring
  have hl2 : (cpyT n (j + 1) j ++ [true]).length = 2 * n + 2 * j + 3 := by
    rw [List.length_append, cpyT_length n (j + 1) j (by omega),
      show ([true] : List Bool).length = 1 from rfl]
    ring
  rw [← hl1, writeAt_append_end, ← hl2, writeAt_append_end]
  simp only [cpyT, List.append_assoc, List.cons_append, List.nil_append]
  rw [show (true :: [true] : List Bool) = List.replicate 2 true from rfl, ← List.replicate_add,
    show 2 * j + 2 = 2 * (j + 1) from by ring]

/-! ## The restore descriptor `resT` -/

/-- The restore tape with `i` pairs of `A` healed: `11^i 10^(n-i) 01 11^n`. -/
def resT (n i : ℕ) : List Bool :=
  List.replicate (2 * i) true ++ (markedD (n - i) ++ ([false, true]
    ++ List.replicate (2 * n) true))

/-- The restore pass starts on the fully-marked, fully-copied tape. -/
theorem resT_zero (n : ℕ) : resT n 0 = cpyT n n n := by
  simp [resT, cpyT]

theorem resT_length (n i : ℕ) (hi : i ≤ n) : (resT n i).length = 4 * n + 2 := by
  simp only [resT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-! ### The `getD` suite -/

theorem resT_getD_pair_lo (n i : ℕ) (h : i < n) : (resT n i).getD (2 * i) false = true := by
  rw [resT, getD_append_length' _ _ List.length_replicate,
    show n - i = (n - i - 1) + 1 from by omega]
  rfl

theorem resT_getD_pair_hi (n i : ℕ) (h : i < n) : (resT n i).getD (2 * i + 1) false = false := by
  rw [resT, getD_append_left_length' _ _ List.length_replicate,
    show n - i = (n - i - 1) + 1 from by omega]
  rfl

theorem resT_getD_marker_lo (n : ℕ) : (resT n n).getD (2 * n) false = false := by
  rw [resT, Nat.sub_self, getD_append_length' _ _ List.length_replicate]
  rfl

theorem resT_getD_marker_hi (n : ℕ) : (resT n n).getD (2 * n + 1) false = true := by
  rw [resT, Nat.sub_self, getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem resT_getD_C (n c : ℕ) (h1 : 2 * n + 2 ≤ c) (h2 : c < 4 * n + 2) :
    (resT n n).getD c false = true := by
  rw [resT, Nat.sub_self, show c = 2 * n + (c - 2 * n) from by omega,
    getD_append_left_length' _ _ List.length_replicate]
  show (([false, true] ++ List.replicate (2 * n) true) : List Bool).getD (c - 2 * n) false = true
  rw [List.getD_append_right (h := by
      rw [show ([false, true] : List Bool).length = 2 from rfl]; omega),
    show ([false, true] : List Bool).length = 2 from rfl]
  exact List.getD_replicate _ (h := by omega)

theorem resT_getD_pastEnd (n c : ℕ) (hc : 4 * n + 2 ≤ c) :
    (resT n n).getD c false = false :=
  List.getD_eq_default _ _ (by rw [resT_length n n (le_refl n)]; omega)

/-! ### The two structural write lemmas of the endgame -/

/-- Healing `A`'s next processed pair (`10 ↦ 11`). -/
theorem resT_heal (n i : ℕ) (hi : i < n) :
    writeAt (resT n i) (2 * i + 1) true = resT n (i + 1) := by
  rw [writeAt_of_lt true (by rw [resT_length n i (by omega)]; omega), resT,
    set_append_left_length' _ _ List.length_replicate,
    show n - i = (n - i - 1) + 1 from by omega]
  simp only [markedD, List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc,
    show ([true, true] : List Bool) = List.replicate 2 true from rfl, ← List.replicate_add,
    show 2 * i + 2 = 2 * (i + 1) from by ring,
    show n - i - 1 = n - (i + 1) from by omega]
  rfl

/-- The final write at the blank end appends the copy's own `01` terminator: the tape is **exactly** the two
adjacent counters — copy and preservation in one equation. -/
theorem resT_finish (n : ℕ) :
    writeAt (resT n n) (4 * n + 3) true = unaryD n ++ unaryD n := by
  have hl : (resT n n).length = 4 * n + 2 := resT_length n n (le_refl n)
  rw [show 4 * n + 3 = 4 * n + 2 + 1 from by omega, ← hl, writeAt_append_end1]
  simp [resT, markedD, unaryD_eq, List.append_assoc]

/-! ## The copy machine

Control: `State = Fin 11 × Bool` (stored low cell).  Phases: `0/1` find in `A` (skip `10`, mark `11` ⇒ seek,
boundary `01` ⇒ restore), `2/3` seek to the blank end (skip any pair with a `true` high cell — data and
boundary alike; blank `00` ⇒ back up to grow), `4/5` the two grow writes (append a `11` pair, reset), `6/7`
restore (heal `10` ⇒ continue, boundary `01` ⇒ seek the copy's end), `8/9` seek the copy's blank end (`11` ⇒
skip, `00` ⇒ write the terminator's high cell and halt), `10` = halt. -/

def copyMachine : Machine where
  State := Fin 11 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 10)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, true), some false, 1) else ((0, s.2), none, 1))
       else (if b then ((6, s.2), none, 3) else ((10, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if b then ((2, true), none, 1)
       else (if s.2 then ((10, s.2), none, 2) else ((4, s.2), none, 0)))
    else if s.1 = 4 then ((5, s.2), some true, 1)
    else if s.1 = 5 then ((0, s.2), some true, 3)
    else if s.1 = 6 then ((7, b), none, 1)
    else if s.1 = 7 then
      (if s.2 then (if b then ((10, s.2), none, 2) else ((6, true), some true, 1))
       else (if b then ((8, s.2), none, 1) else ((10, s.2), none, 2)))
    else if s.1 = 8 then ((9, b), none, 1)
    else if s.1 = 9 then
      (if s.2 then (if b then ((8, true), none, 1) else ((10, s.2), none, 2))
       else (if b then ((10, s.2), none, 2) else ((10, s.2), some true, 2)))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_cpy (x : List Bool) : init copyMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

/-- Find, low cell: read, store, advance. -/
theorem step_c0 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Find, high cell over a `11` data pair: mark it, enter the seek. -/
theorem step_c1_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step copyMachine ⟨(1, true), p, T⟩ = ⟨(2, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Find, high cell over a `10` processed pair: skip. -/
theorem step_c1_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step copyMachine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Find, high cell over the `01` boundary: `A` fully processed — reset into the restore pass. -/
theorem step_c1_restore {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step copyMachine ⟨(1, false), p, T⟩ = ⟨(6, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Seek, low cell: read, store, advance. -/
theorem step_c2 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Seek, high cell `true` (data pair or boundary alike): continue seeking. -/
theorem step_c3_skip {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step copyMachine ⟨(3, s), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Seek, blank pair (`00`): the tape end — back up to its low cell to grow. -/
theorem step_c3_endW {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step copyMachine ⟨(3, false), p, T⟩ = ⟨(4, false), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- First grow write: the new pair's low `true`, appended at the tape end. -/
theorem step_c4 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(4, s), p, T⟩ = ⟨(5, s), p + 1, writeAt T p true⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Second grow write: the new pair's high `true`; reset for the next round. -/
theorem step_c5 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(5, s), p, T⟩ = ⟨(0, s), 0, writeAt T p true⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Restore, low cell: read, store, advance. -/
theorem step_c6 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(6, s), p, T⟩ = ⟨(7, T.getD p false), p + 1, T⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Restore, high cell over a `10` processed pair: heal it back to `11`. -/
theorem step_c7_heal {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step copyMachine ⟨(7, true), p, T⟩ = ⟨(6, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Restore, high cell over the `01` boundary: `A` fully healed — seek the copy's end. -/
theorem step_c7_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step copyMachine ⟨(7, false), p, T⟩ = ⟨(8, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Copy-seek, low cell: read, store, advance. -/
theorem step_c8 {s : Bool} {p : ℕ} {T : List Bool} :
    step copyMachine ⟨(8, s), p, T⟩ = ⟨(9, T.getD p false), p + 1, T⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

/-- Copy-seek, high cell over a `11` data pair: skip. -/
theorem step_c9_skip {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step copyMachine ⟨(9, true), p, T⟩ = ⟨(8, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-- Copy-seek, blank pair: write the terminator's high `true` (padding writes its low `false`) and halt. -/
theorem step_c9_finish {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step copyMachine ⟨(9, false), p, T⟩ = ⟨(10, false), p, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, copyMachine, moveHead, h]

/-! ### Pair-step lemmas -/

/-- Skip a `10` processed pair in the find phase. -/
theorem run_two_skipF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run copyMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_skip h2]

/-- Mark a `11` data pair in the find phase and enter the seek. -/
theorem run_two_mark {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run copyMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_mark h2]

/-- Hit the `01` boundary in the find phase: reset into the restore pass. -/
theorem run_two_toRestore {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run copyMachine 2 ⟨(0, s), p, T⟩ = ⟨(6, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c0, h1, step_c1_restore h2]

/-- Seek across any pair whose high cell is `true` (data and boundary alike). -/
theorem run_two_seekE {s : Bool} {p : ℕ} {T : List Bool}
    (h2 : T.getD (p + 1) false = true) :
    run copyMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c2, step_c3_skip h2]

/-- Detect the blank end and grow the copy by one `11` pair, resetting for the next round. -/
theorem run_four_grow {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run copyMachine 4 ⟨(2, s), p, T⟩
      = ⟨(0, false), 0, writeAt (writeAt T p true) (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_c2, h1, step_c3_endW h2,
    show p + 1 - 1 = p from by omega, step_c4, step_c5]

/-- Heal a `10` processed pair in the restore pass. -/
theorem run_two_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run copyMachine 2 ⟨(6, s), p, T⟩ = ⟨(6, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_c6, h1, step_c7_heal h2]

/-- Cross the `01` boundary out of the restored region. -/
theorem run_two_cross67 {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run copyMachine 2 ⟨(6, s), p, T⟩ = ⟨(8, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c6, h1, step_c7_cross h2]

/-- Skip a `11` pair of the copy region. -/
theorem run_two_seekC {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run copyMachine 2 ⟨(8, s), p, T⟩ = ⟨(8, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_c8, h1, step_c9_skip h2]

/-- Detect the copy's blank end, write its `01` terminator, halt. -/
theorem run_two_finish {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = false) :
    run copyMachine 2 ⟨(8, s), p, T⟩ = ⟨(10, false), p + 1, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_c8, h1, step_c9_finish h2]

/-! ### Scan run-invariants -/

/-- Skip `k` processed pairs in the find phase. -/
theorem run_findSkip (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run copyMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipF hk.1 hk.2]
    rfl

/-- Seek across `k` pairs with `true` high cells. -/
theorem run_seekE (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i + 1) false = true) :
    run copyMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekE (h k (by omega))]
    rfl

/-- **Restore invariant** (evolving tape): `2i` steps heal the first `i` processed pairs. -/
theorem run_restore (n : ℕ) (s : Bool) (i : ℕ) (hi : i ≤ n) :
    run copyMachine (2 * i) ⟨(6, s), 0, resT n 0⟩
      = ⟨(6, if i = 0 then s else true), 2 * i, resT n i⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_heal (resT_getD_pair_lo n i (by omega)) (resT_getD_pair_hi n i (by omega)),
      resT_heal n i (by omega)]
    rfl

/-- Skip `k` pairs of the copy region. -/
theorem run_seekCs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run copyMachine (2 * k) ⟨(8, s), q, T⟩
      = ⟨(8, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekC hk.1 hk.2]
    rfl

/-! ## The round invariant -/

/-- **One copy round.**  From the origin on `cpyT n j j`, `2n + 2j + 6` steps mark `A`'s pair `j`, seek to the
blank end, append a `11` pair to the copy, and reset. -/
theorem run_copy_round (n j : ℕ) (hj : j < n) (s : Bool) :
    run copyMachine (2 * n + 2 * j + 6) ⟨(0, s), 0, cpyT n j j⟩
      = ⟨(0, false), 0, cpyT n (j + 1) (j + 1)⟩ := by
  -- Stage 1: skip the `j` processed pairs of `A`.
  have st1 := run_findSkip (cpyT n j j) 0 j s (fun i hi =>
    ⟨by simpa using cpyT_getD_Amark_lo n j j i hi,
     by simpa using cpyT_getD_Amark_hi n j j i hi⟩)
  simp only [Nat.zero_add] at st1
  -- Stage 2: mark `A`'s pair `j`.
  have st2 := run_two_mark (s := if j = 0 then s else true) (p := 2 * j) (T := cpyT n j j)
    (cpyT_getD_Adata n j j (2 * j) (by omega) (by omega) (by omega))
    (cpyT_getD_Adata n j j (2 * j + 1) (by omega) (by omega) (by omega))
  rw [cpyT_mark n j hj] at st2
  -- Stage 3: seek across `A`'s rest, its boundary, and the copy so far — `n` pairs, all high cells `true`.
  have st3 := run_seekE (cpyT n (j + 1) j) (2 * j + 2) n true (fun i hi => by
    rcases Nat.lt_trichotomy i (n - j - 1) with h | h | h
    · exact cpyT_getD_Adata n (j + 1) j (2 * j + 2 + 2 * i + 1) (by omega) (by omega) (by omega)
    · rw [show 2 * j + 2 + 2 * i + 1 = 2 * n + 1 from by omega]
      exact cpyT_getD_marker_hi n (j + 1) j (by omega)
    · exact cpyT_getD_C n (j + 1) j (2 * j + 2 + 2 * i + 1) (by omega) (by omega) (by omega))
  rw [show 2 * j + 2 + 2 * n = 2 * n + 2 * j + 2 from by ring] at st3
  simp only [ite_self] at st3
  -- Stage 4: detect the blank end and grow the copy.
  have st4 := run_four_grow (s := true) (p := 2 * n + 2 * j + 2) (T := cpyT n (j + 1) j)
    (cpyT_getD_pastEnd n (j + 1) j (2 * n + 2 * j + 2) (by omega) (by omega))
    (cpyT_getD_pastEnd n (j + 1) j (2 * n + 2 * j + 2 + 1) (by omega) (by omega))
  rw [show 2 * n + 2 * j + 2 + 1 = 2 * n + 2 * j + 3 from by omega, cpyT_grow n j hj] at st4
  -- Assemble the round.
  rw [show 2 * n + 2 * j + 6 = 2 * j + (2 + (2 * n + 4)) from by omega,
    run_add, st1, run_add, st2, run_add, st3, st4]

/-! ## The rounds and their clock -/

/-- The cumulative clock of the first `k` copy rounds. -/
def cpyRounds (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cpyRounds n k + (2 * n + 2 * k + 6)

theorem cpyRounds_eq (n k : ℕ) : cpyRounds n k = 2 * n * k + k * k + 5 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cpyRounds]; rw [ih]; ring

/-- **Rounds invariant.**  `k` rounds process and copy `k` pairs. -/
theorem run_copy_rounds (n k : ℕ) (hk : k ≤ n) (s : Bool) :
    run copyMachine (cpyRounds n k) ⟨(0, s), 0, cpyT n 0 0⟩
      = ⟨(0, if k = 0 then s else false), 0, cpyT n k k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show cpyRounds n (k + 1) = cpyRounds n k + (2 * n + 2 * k + 6) from rfl, run_add,
      ih (by omega), run_copy_round n k (by omega), if_neg (by omega)]

/-! ## The packaged copy: self-halting, preserving, quadratic clock -/

/-- The copy's explicit clock: `n` rounds, then the find-to-restore transit, the restore pass, and the
terminator seek — `3n² + 11n + 6` in closed form (`cpyClock_eq`). -/
def cpyClock (n : ℕ) : ℕ := cpyRounds n n + (2 * n + (2 + (2 * n + (2 + (2 * n + 2)))))

/-- **The copy runs to completion.**  On tape `unaryD n`, after exactly `cpyClock n` steps the machine is in
the halt phase with tape **exactly** `unaryD n ++ unaryD n` — the original counter preserved, its copy after
it. -/
theorem copy_run (n : ℕ) :
    run copyMachine (cpyClock n) (init copyMachine (unaryD n))
      = ⟨(10, false), 4 * n + 3, unaryD n ++ unaryD n⟩ := by
  rw [init_cpy, ← cpyT_zero, cpyClock, run_add, run_copy_rounds n n (le_refl n) false,
    ite_self]
  -- Find phase hits `A`'s boundary: into the restore pass.
  have st1 := run_findSkip (cpyT n n n) 0 n false (fun i hi =>
    ⟨by simpa using cpyT_getD_Amark_lo n n n i hi,
     by simpa using cpyT_getD_Amark_hi n n n i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toRestore (s := if n = 0 then false else true) (p := 2 * n)
    (T := cpyT n n n)
    (cpyT_getD_marker_lo n n n (le_refl n)) (cpyT_getD_marker_hi n n n (le_refl n))
  -- The restore pass heals all of `A`.
  have st3 := run_restore n false n (le_refl n)
  -- Cross the boundary and seek the copy's blank end.
  have st4 := run_two_cross67 (s := if n = 0 then false else true) (p := 2 * n) (T := resT n n)
    (resT_getD_marker_lo n) (resT_getD_marker_hi n)
  have st5 := run_seekCs (resT n n) (2 * n + 2) n false (fun i hi =>
    ⟨resT_getD_C n (2 * n + 2 + 2 * i) (by omega) (by omega),
     resT_getD_C n (2 * n + 2 + 2 * i + 1) (by omega) (by omega)⟩)
  rw [show 2 * n + 2 + 2 * n = 4 * n + 2 from by ring] at st5
  -- Write the copy's terminator and halt.
  have st6 := run_two_finish (s := if n = 0 then false else true) (p := 4 * n + 2)
    (T := resT n n)
    (resT_getD_pastEnd n (4 * n + 2) (by omega))
    (resT_getD_pastEnd n (4 * n + 2 + 1) (by omega))
  rw [show 4 * n + 2 + 1 = 4 * n + 3 from by omega, resT_finish n] at st6
  -- Assemble the endgame.
  rw [run_add, st1, run_add, st2, ← resT_zero, run_add, st3, run_add, st4, run_add, st5, st6,
    cpyT_zero]

/-- The copy machine **halts by itself** at its clock. -/
theorem copy_halted (n : ℕ) :
    copyMachine.halt (run copyMachine (cpyClock n) (init copyMachine (unaryD n))).st = true := by
  rw [copy_run]; rfl

/-- **Copy with preservation**: the output tape is exactly the original counter followed by its copy. -/
theorem copy_output (n : ℕ) :
    (run copyMachine (cpyClock n) (init copyMachine (unaryD n))).tp = unaryD n ++ unaryD n := by
  rw [copy_run]

/-- Closed form of the clock. -/
theorem cpyClock_eq (n : ℕ) : cpyClock n = 3 * n * n + 11 * n + 6 := by
  rw [cpyClock, cpyRounds_eq]; ring

/-- **The clock is quadratic**: `cpyClock n ≤ 3(n + 2)²`. -/
theorem cpyClock_le (n : ℕ) : cpyClock n ≤ 3 * (n + 2) * (n + 2) := by
  rw [cpyClock_eq]; nlinarith

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
