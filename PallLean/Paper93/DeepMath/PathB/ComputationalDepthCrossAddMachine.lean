import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryCopyMachine

/-!
# The crossing select-add

The pair-assembly arms must add *different* operands (`p`, then `t`, then `tag`) into one
accumulator, but every prior op works on the operand block immediately before the
accumulator.  `crossAddMachine` is the select-add that reaches a chosen operand: it is
`copyMachine` with the seek extended to **cross block separators** — on reading the single
`[F]` separator between operand blocks it peeks ahead and, if another block follows, crosses
into it; only the double `[F,F]` accumulator terminator stops the seek.  So a live block
sitting behind fully-consumed (marked) blocks is still reached and added.

This brick lands the machine, its step laws, and the **crossing seek walk** (`walkCross`):
the seek skips a dead block `[T,F]^d` and crosses its `[F]` separator, arriving at the next
block in seek state.  The grand round lemma assembling these into the full select-add builds
on top (next brick), reusing `copyMachine`'s mark/hunt/deposit fabric verbatim.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossAddMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine (getD_run)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- States: `0` seek (unit start), `1` mark cell, `2`/`3` hunt, `4` cross the acc marker's
second cell, `5` acc walk + deposit, `6` halt, `7` **separator peek** — the crossing
extension: after the seek reads a single `[F]`, decide next block (`T`) vs acc terminator
(`F`). -/
def crossAddMachine : Machine where
  State := Fin 8 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 6)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((7, s.2), none, 1))
    else if s.1 = 1 then
      (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, s.2), none, 1))
    else if s.1 = 3 then ((2, s.2), none, 1)
    else if s.1 = 4 then ((5, s.2), none, 1)
    else if s.1 = 5 then
      (if b then ((5, s.2), none, 1) else ((0, s.2), some true, 3))
    else if s.1 = 7 then (if b then ((0, s.2), none, 2) else ((6, s.2), none, 2))
    else ((6, s.2), none, 2)
  accept := fun s => s.2

theorem step_A0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step crossAddMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_A0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step crossAddMachine ⟨(0, ans), p, x⟩ = ⟨(7, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_A1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step crossAddMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_A1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step crossAddMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_B0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step crossAddMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_B0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step crossAddMachine ⟨(2, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_B1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step crossAddMachine ⟨(3, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, moveHead]; rfl

theorem step_cross {ans : Bool} {p : ℕ} {x : List Bool} :
    step crossAddMachine ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, moveHead]; rfl

theorem step_C_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step crossAddMachine ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_C_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step crossAddMachine ⟨(5, ans), p, x⟩ = ⟨(0, ans), 0, writeAt x p true⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

/-- Separator peek: another block (`T`) continues the seek at that cell; the acc terminator
(`F`) halts. -/
theorem step_peek_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step crossAddMachine ⟨(7, ans), p, x⟩ = ⟨(0, ans), p, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

theorem step_peek_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step crossAddMachine ⟨(7, ans), p, x⟩ = ⟨(6, ans), p, x⟩ := by
  simp only [step, crossAddMachine, h, moveHead]; rfl

/-! ## Walks -/

/-- Seek over marked (dead) units: two steps each, tape unchanged. -/
theorem walkMarked (d : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run crossAddMachine (2 * d)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate d false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * d, P ++ (flat2 (List.replicate d false) ++ Z)⟩ := by
  induction d with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ d ih =>
    intro P Z ans
    show run crossAddMachine (2 * (d + 1))
        ⟨(0, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate d false) ++ Z))⟩
      = ⟨(0, ans), P.length + 2 * (d + 1),
          P ++ (true :: false :: (flat2 (List.replicate d false) ++ Z))⟩
    rw [show P.length + 2 * (d + 1) = (P ++ [true, false]).length + 2 * d from by
      simp; omega]
    rw [show 2 * (d + 1) = 2 + 2 * d from by omega, run_add, run_two,
      step_A0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate d false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate d false) ++ Z) from by simp,
      step_A1_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate d false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate d false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- **The crossing walk**: the seek skips a dead block `[T,F]^d`, crosses its `[F]`
separator, and arrives — still seeking — at the following block (whose first cell is `T`). -/
theorem walkCross (d : ℕ) (P Z : List Bool) (ans : Bool)
    (hnext : (P ++ (flat2 (List.replicate d false) ++ false :: Z)).getD
      (P.length + 2 * d + 1) false = true) :
    run crossAddMachine (2 * d + 2)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate d false) ++ false :: Z)⟩
      = ⟨(0, ans), P.length + 2 * d + 1,
          P ++ (flat2 (List.replicate d false) ++ false :: Z)⟩ := by
  have hw := walkMarked d P (false :: Z) ans
  rw [show 2 * d + 2 = 2 * d + 1 + 1 from by omega, run_add, run_add, hw, run_one, run_one,
    show P ++ (flat2 (List.replicate d false) ++ false :: Z)
      = (P ++ flat2 (List.replicate d false)) ++ false :: Z from by simp,
    show P.length + 2 * d = (P ++ flat2 (List.replicate d false)).length from by
      simp [DIndexMachine.flat2_length],
    step_A0_F (getD_at _ false _),
    step_peek_T (by
      rw [show (P ++ flat2 (List.replicate d false)).length + 1
          = P.length + 2 * d + 1 from by simp [DIndexMachine.flat2_length],
        show (P ++ flat2 (List.replicate d false)) ++ false :: Z
          = P ++ (flat2 (List.replicate d false) ++ false :: Z) from by simp]
      exact hnext)]

/-- Hunt over live units (states `2`/`3`): two steps each. -/
theorem walkLive (k : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run crossAddMachine (2 * k)
      ⟨(2, ans), P.length, P ++ (flat2 (List.replicate k true) ++ Z)⟩
      = ⟨(2, ans), P.length + 2 * k, P ++ (flat2 (List.replicate k true) ++ Z)⟩ := by
  induction k with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ k ih =>
    intro P Z ans
    show run crossAddMachine (2 * (k + 1))
        ⟨(2, ans), P.length, P ++ (true :: true :: (flat2 (List.replicate k true) ++ Z))⟩
      = ⟨(2, ans), P.length + 2 * (k + 1),
          P ++ (true :: true :: (flat2 (List.replicate k true) ++ Z))⟩
    rw [show P.length + 2 * (k + 1) = (P ++ [true, true]).length + 2 * k from by
      simp; omega]
    rw [show 2 * (k + 1) = 2 + 2 * k from by omega, run_add, run_two,
      step_B0_T (getD_at P true _), step_B1,
      show P.length + 1 + 1 = (P ++ [true, true]).length from by simp,
      show P ++ (true :: true :: (flat2 (List.replicate k true) ++ Z))
        = (P ++ [true, true]) ++ (flat2 (List.replicate k true) ++ Z) from by simp,
      ih (P ++ [true, true]) Z ans]

/-- The acc-run walk (state `5`): `getD`-conditioned. -/
theorem walkC : ∀ (m : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < m, x.getD (p + i) false = true) →
    run crossAddMachine m ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + m, x⟩
  | 0, x, p, ans, _ => rfl
  | m + 1, x, p, ans, h => by
    rw [show m + 1 = 1 + m from by omega, run_add, run_one,
      step_C_T (by simpa using h 0 (by omega)),
      walkC m x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + m) = p + 1 + m from by omega]

/-- The crossing-select tape: one dead block `[T,F]^d`, its `[F]` separator, then a partially
consumed live block (`j` marked, `k` live), the acc terminator, acc `1^(s+j)`, and frontier
zeros. -/
def crossTape (d j k s : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate d false) ++ false :: UnaryCopyMachine.copyTape j k s rest

/-- The dead prefix the seek crosses each round. -/
def deadPrefix (d : ℕ) : List Bool := flat2 (List.replicate d false) ++ [false]

theorem deadPrefix_length (d : ℕ) : (deadPrefix d).length = 2 * d + 1 := by
  simp [deadPrefix, DIndexMachine.flat2_length]

theorem crossTape_eq (d j k s : ℕ) (rest : List Bool) :
    crossTape d j k s rest = deadPrefix d ++ UnaryCopyMachine.copyTape j k s rest := by
  simp [crossTape, deadPrefix]

/-- **The dead-prefix crossing**, as a run from the tape start: the seek skips the `d` dead
units and crosses the `[F]` separator, landing in seek state at the live-block region (whose
first cell is `T`). -/
theorem run_cross (d : ℕ) (tail : List Bool) (ans : Bool)
    (htail : tail.getD 0 false = true) :
    run crossAddMachine (2 * d + 2)
      ⟨(0, ans), 0, flat2 (List.replicate d false) ++ false :: tail⟩
      = ⟨(0, ans), (deadPrefix d).length, deadPrefix d ++ tail⟩ := by
  have hget : (flat2 (List.replicate d false) ++ false :: tail).getD (2 * d + 1) false = true := by
    rw [show (2 * d + 1 : ℕ) = (flat2 (List.replicate d false)).length + 1 from by
        simp [DIndexMachine.flat2_length],
      show flat2 (List.replicate d false) ++ false :: tail
        = (flat2 (List.replicate d false) ++ [false]) ++ tail from by simp,
      List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp),
      show (flat2 (List.replicate d false)).length + 1
          - (flat2 (List.replicate d false) ++ [false]).length = 0 from by simp,
      ← List.getD_eq_getElem?_getD]
    exact htail
  have hc := walkCross d [] tail ans (by simpa using hget)
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hc
  rw [hc, deadPrefix_length]
  simp [deadPrefix, List.append_assoc]

/-- The machine halts at state `6`. -/
theorem crossAdd_halt (ans : Bool) : crossAddMachine.halt ((6 : Fin 8), ans) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CrossAddMachine
