import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryDupMachine

/-!
# The multiplication sub-arc, brick 4b: the compare machine

**The branch selector** for `Nat.pair`: on two doubled blocks

  `[T,T]^t [F,F] [T,T]^p [F,F] rest`

`cmpMachine` decides `t < p` by lockstep alternating consumption — each round marks the
first live unit of block 1, hunts to its terminator, crosses, and marks the first live
unit of block 2; whichever block exhausts first decides.  The answer is delivered in
the **accept bit**: block 1 exhausted with block 2 still live → `true`; block 2
exhausted (or both simultaneously) → `false`.

`cmpM_run` is a single grand induction on block 1's live count (generalizing the marked
prefix and block 2), producing `⟨(10, decide (t' < p')), _, cmpFinal i t' p' rest⟩`
with the exact per-branch final tape packaged in `cmpFinal` (an `if`-definition that
telescopes one round at a time, `cmpFinal_succ`).  The blocks are left in their
consumed state — the pair-assembly re-derives what it needs; counts are preserved in
the marks.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryCmpMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The machine -/

/-- States: `0`/`1` block-1 seek+mark (to the exhausted path at its terminator),
`2`/`3` hunt, `4` cross, `5`/`6` block-2 seek+mark (halt `false` at its terminator),
`7` the exhausted-path cross, `8`/`9` block-2 liveness check (halt `true` on a live
unit, `false` at the terminator), `10` halt. -/
def cmpMachine : Machine where
  State := Fin 11 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 10)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((7, s.2), none, 1))
    else if s.1 = 1 then
      (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, s.2), none, 1))
    else if s.1 = 3 then ((2, s.2), none, 1)
    else if s.1 = 4 then ((5, s.2), none, 1)
    else if s.1 = 5 then (if b then ((6, s.2), none, 1) else ((10, false), none, 2))
    else if s.1 = 6 then
      (if b then ((0, s.2), some false, 3) else ((5, s.2), none, 1))
    else if s.1 = 7 then ((8, s.2), none, 1)
    else if s.1 = 8 then (if b then ((9, s.2), none, 1) else ((10, false), none, 2))
    else if s.1 = 9 then (if b then ((10, true), none, 2) else ((8, s.2), none, 1))
    else ((10, s.2), none, 2)
  accept := fun s => s.2

theorem step_S10_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S10_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(0, ans), p, x⟩ = ⟨(7, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S11_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S11_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_H0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_H0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(2, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_H1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step cmpMachine ⟨(3, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, moveHead]; rfl

theorem step_C1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step cmpMachine ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, moveHead]; rfl

theorem step_S20_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(5, ans), p, x⟩ = ⟨(6, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S20_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(5, ans), p, x⟩ = ⟨(10, false), p, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S21_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(6, ans), p, x⟩ = ⟨(0, ans), 0, writeAt x p false⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S21_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(6, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_Xc {ans : Bool} {p : ℕ} {x : List Bool} :
    step cmpMachine ⟨(7, ans), p, x⟩ = ⟨(8, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, moveHead]; rfl

theorem step_S30_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(8, ans), p, x⟩ = ⟨(9, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S30_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(8, ans), p, x⟩ = ⟨(10, false), p, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S31_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cmpMachine ⟨(9, ans), p, x⟩ = ⟨(10, true), p, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

theorem step_S31_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cmpMachine ⟨(9, ans), p, x⟩ = ⟨(8, ans), p + 1, x⟩ := by
  simp only [step, cmpMachine, h, moveHead]; rfl

/-! ## Walks -/

/-- Block-1 seek over marked units (states `0`/`1`). -/
theorem walkS1 (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run cmpMachine (2 * j)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run cmpMachine (2 * (j + 1))
        ⟨(0, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(0, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_S10_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_S11_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- Hunt over any units (states `2`/`3`). -/
theorem walkHunt (us : List Bool) : ∀ (P Z : List Bool) (ans : Bool),
    run cmpMachine (2 * us.length) ⟨(2, ans), P.length, P ++ (flat2 us ++ Z)⟩
      = ⟨(2, ans), P.length + 2 * us.length, P ++ (flat2 us ++ Z)⟩ := by
  induction us with
  | nil => intro P Z ans; simp [flat2, run_zero]
  | cons u us ih =>
    intro P Z ans
    show run cmpMachine (2 * (us.length + 1))
        ⟨(2, ans), P.length, P ++ (true :: u :: (flat2 us ++ Z))⟩
      = ⟨(2, ans), P.length + 2 * (us.length + 1), P ++ (true :: u :: (flat2 us ++ Z))⟩
    rw [show P.length + 2 * (us.length + 1) = (P ++ [true, u]).length + 2 * us.length
        from by simp; omega]
    rw [show 2 * (us.length + 1) = 2 + 2 * us.length from by omega, run_add, run_two,
      step_H0_T (getD_at P true _), step_H1,
      show P.length + 1 + 1 = (P ++ [true, u]).length from by simp,
      show P ++ (true :: u :: (flat2 us ++ Z))
        = (P ++ [true, u]) ++ (flat2 us ++ Z) from by simp,
      ih (P ++ [true, u]) Z ans]

/-- Block-2 seek over marked units (states `5`/`6`). -/
theorem walkS2 (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run cmpMachine (2 * j)
      ⟨(5, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(5, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run cmpMachine (2 * (j + 1))
        ⟨(5, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(5, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_S20_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_S21_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- Block-2 liveness check over marked units (states `8`/`9`). -/
theorem walkS3 (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run cmpMachine (2 * j)
      ⟨(8, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(8, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run cmpMachine (2 * (j + 1))
        ⟨(8, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(8, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_S30_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_S31_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-! ## The tape, the outcome, and the grand run -/

/-- The compare tape: block 1 (`i` marked, `k` live), block 2 (`j` marked, `m` live). -/
def cmpTape (i k j m : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate i false) ++ (flat2 (List.replicate k true)
    ++ false :: false :: (flat2 (List.replicate j false)
      ++ (flat2 (List.replicate m true) ++ false :: false :: rest)))

/-- The exact per-branch final tape. -/
def cmpFinal (i t' p' : ℕ) (rest : List Bool) : List Bool :=
  if t' < p' then cmpTape (i + t') 0 (i + t') (p' - t') rest
  else if p' < t' then cmpTape (i + p' + 1) (t' - p' - 1) (i + p') 0 rest
  else cmpTape (i + t') 0 (i + t') 0 rest

/-- One-round telescoping of the outcome tape. -/
theorem cmpFinal_succ (i t' p' : ℕ) (rest : List Bool) :
    cmpFinal (i + 1) t' p' rest = cmpFinal i (t' + 1) (p' + 1) rest := by
  rcases Nat.lt_trichotomy t' p' with h | h | h
  · rw [cmpFinal, if_pos h, cmpFinal, if_pos (by omega)]
    congr 1 <;> omega
  · subst h
    rw [cmpFinal, if_neg (by omega), if_neg (by omega),
      cmpFinal, if_neg (by omega), if_neg (by omega)]
    congr 1 <;> omega
  · rw [cmpFinal, if_neg (by omega), if_pos h,
      cmpFinal, if_neg (by omega), if_pos (by omega)]
    congr 1 <;> omega

/- **Next piece (4b-part-2)**: `cmpM_run` — the four-case grand induction (both
exhausted / block-2 live / block-2 exhausts first / full round + IH), producing
`⟨(10, decide (t' < p')), _, cmpFinal i t' p' rest⟩`.  The composition chains hit a
rewrite-ordering interaction between the walk-clock normalizations and the
position-shows (the `2·i`-to-length conversions corrupt the remaining segment clocks
in a way that needs staged `have`-computation rather than one rw-chain); the staged
restructure is the next brick. -/

end PallLean.Paper93.DeepMath.PathB.UnaryCmpMachine
