import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryCopyMachine

/-!
# The multiplication sub-arc, brick 3: the multiplier

**One combined machine** (the loop count is input-dependent, so the outer iteration
cannot be a fixed `seq`-chain; the heal sweep is a phase of this machine, not a
separate one).  Layout:

  `[outer units]^a [F,F] [inner units]^b [F,F] 1^s 0^(a·b+1) rest`

Per **outer round**: consume the first live outer unit; then run **inner rounds** — from
the reset, skip the whole outer block (unit-counting is phase-local: cross at the first
`F` head-cell), seek the first live inner unit, mark it, hunt to the inner terminator,
cross, walk the run, deposit a `1` at the frontier — until the inner block is exhausted;
then the **heal phase** re-arms the inner block (`[T,F] ↦ [T,T]` sweep) and returns to
the outer seek.  When the outer block exhausts, halt.  Net effect: the run grows by
`a·b`, consuming `a·b` frontier zeros.

Morph-arc convention: exact well-formed run lemmas (`mulM_run` at the top), pipeline-
internal.  Walk fabric: unit walks with growing prefix (`walkSkip`/`walkO`/`walkI`/
`walkHunt`/`walkHS` cell0-driven, `walkHeal` mutating), `getD`-conditioned run walk
(`walkRun`), frontier-zeros telescoping `z = k + w`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryMulMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine (getD_run)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The machine -/

/-- States: `0`/`1` outer seek+mark (halt at outer terminator), `2`/`3`/`4` phase-I
outer skip and cross, `5`/`6` inner seek+mark (to heal at inner terminator), `7`/`8`/`9`
hunt and cross, `10` run walk and deposit, `12`/`13`/`14` phase-H outer skip and cross,
`15`/`16` heal sweep, `17` halt. -/
def mulMachine : Machine where
  State := Fin 18 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 17)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((17, s.2), none, 2))
    else if s.1 = 1 then
      (if b then ((2, s.2), some false, 3) else ((0, s.2), none, 1))
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, s.2), none, 1))
    else if s.1 = 3 then ((2, s.2), none, 1)
    else if s.1 = 4 then ((5, s.2), none, 1)
    else if s.1 = 5 then (if b then ((6, s.2), none, 1) else ((12, s.2), none, 3))
    else if s.1 = 6 then
      (if b then ((7, s.2), some false, 1) else ((5, s.2), none, 1))
    else if s.1 = 7 then (if b then ((8, s.2), none, 1) else ((9, s.2), none, 1))
    else if s.1 = 8 then ((7, s.2), none, 1)
    else if s.1 = 9 then ((10, s.2), none, 1)
    else if s.1 = 10 then
      (if b then ((10, s.2), none, 1) else ((2, s.2), some true, 3))
    else if s.1 = 12 then (if b then ((13, s.2), none, 1) else ((14, s.2), none, 1))
    else if s.1 = 13 then ((12, s.2), none, 1)
    else if s.1 = 14 then ((15, s.2), none, 1)
    else if s.1 = 15 then (if b then ((16, s.2), none, 1) else ((0, s.2), none, 3))
    else if s.1 = 16 then ((15, s.2), some true, 1)
    else ((17, s.2), none, 2)
  accept := fun s => s.2

theorem step_O0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_O0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(0, ans), p, x⟩ = ⟨(17, ans), p, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_O1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), 0, writeAt x p false⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_O1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_IS0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_IS0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(2, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_IS1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(3, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_ISc {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_I0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(5, ans), p, x⟩ = ⟨(6, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_I0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(5, ans), p, x⟩ = ⟨(12, ans), 0, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_I1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(6, ans), p, x⟩ = ⟨(7, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_I1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(6, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_Ih0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(7, ans), p, x⟩ = ⟨(8, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_Ih0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(7, ans), p, x⟩ = ⟨(9, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_Ih1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(8, ans), p, x⟩ = ⟨(7, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_Ihc {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(9, ans), p, x⟩ = ⟨(10, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_IR_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(10, ans), p, x⟩ = ⟨(10, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_IR_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(10, ans), p, x⟩ = ⟨(2, ans), 0, writeAt x p true⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_HS0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(12, ans), p, x⟩ = ⟨(13, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_HS0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(12, ans), p, x⟩ = ⟨(14, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_HS1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(13, ans), p, x⟩ = ⟨(12, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_HSc {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(14, ans), p, x⟩ = ⟨(15, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

theorem step_HH0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step mulMachine ⟨(15, ans), p, x⟩ = ⟨(16, ans), p + 1, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_HH0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step mulMachine ⟨(15, ans), p, x⟩ = ⟨(0, ans), 0, x⟩ := by
  simp only [step, mulMachine, h, moveHead]; rfl

theorem step_HH1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step mulMachine ⟨(16, ans), p, x⟩ = ⟨(15, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, mulMachine, moveHead]; rfl

/-! ## Walks -/

/-- Phase-I outer skip: over any units, cell0-driven. -/
theorem walkSkip (us : List Bool) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * us.length) ⟨(2, ans), P.length, P ++ (flat2 us ++ Z)⟩
      = ⟨(2, ans), P.length + 2 * us.length, P ++ (flat2 us ++ Z)⟩ := by
  induction us with
  | nil => intro P Z ans; simp [flat2, run_zero]
  | cons u us ih =>
    intro P Z ans
    show run mulMachine (2 * (us.length + 1))
        ⟨(2, ans), P.length, P ++ (true :: u :: (flat2 us ++ Z))⟩
      = ⟨(2, ans), P.length + 2 * (us.length + 1),
          P ++ (true :: u :: (flat2 us ++ Z))⟩
    rw [show P.length + 2 * (us.length + 1) = (P ++ [true, u]).length + 2 * us.length
        from by simp; omega]
    rw [show 2 * (us.length + 1) = 2 + 2 * us.length from by omega, run_add, run_two,
      step_IS0_T (getD_at P true _), step_IS1,
      show P.length + 1 + 1 = (P ++ [true, u]).length from by simp,
      show P ++ (true :: u :: (flat2 us ++ Z))
        = (P ++ [true, u]) ++ (flat2 us ++ Z) from by simp,
      ih (P ++ [true, u]) Z ans]

/-- Hunt: over any units, cell0-driven. -/
theorem walkHunt (us : List Bool) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * us.length) ⟨(7, ans), P.length, P ++ (flat2 us ++ Z)⟩
      = ⟨(7, ans), P.length + 2 * us.length, P ++ (flat2 us ++ Z)⟩ := by
  induction us with
  | nil => intro P Z ans; simp [flat2, run_zero]
  | cons u us ih =>
    intro P Z ans
    show run mulMachine (2 * (us.length + 1))
        ⟨(7, ans), P.length, P ++ (true :: u :: (flat2 us ++ Z))⟩
      = ⟨(7, ans), P.length + 2 * (us.length + 1),
          P ++ (true :: u :: (flat2 us ++ Z))⟩
    rw [show P.length + 2 * (us.length + 1) = (P ++ [true, u]).length + 2 * us.length
        from by simp; omega]
    rw [show 2 * (us.length + 1) = 2 + 2 * us.length from by omega, run_add, run_two,
      step_Ih0_T (getD_at P true _), step_Ih1,
      show P.length + 1 + 1 = (P ++ [true, u]).length from by simp,
      show P ++ (true :: u :: (flat2 us ++ Z))
        = (P ++ [true, u]) ++ (flat2 us ++ Z) from by simp,
      ih (P ++ [true, u]) Z ans]

/-- Phase-H outer skip: over any units, cell0-driven. -/
theorem walkHS (us : List Bool) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * us.length) ⟨(12, ans), P.length, P ++ (flat2 us ++ Z)⟩
      = ⟨(12, ans), P.length + 2 * us.length, P ++ (flat2 us ++ Z)⟩ := by
  induction us with
  | nil => intro P Z ans; simp [flat2, run_zero]
  | cons u us ih =>
    intro P Z ans
    show run mulMachine (2 * (us.length + 1))
        ⟨(12, ans), P.length, P ++ (true :: u :: (flat2 us ++ Z))⟩
      = ⟨(12, ans), P.length + 2 * (us.length + 1),
          P ++ (true :: u :: (flat2 us ++ Z))⟩
    rw [show P.length + 2 * (us.length + 1) = (P ++ [true, u]).length + 2 * us.length
        from by simp; omega]
    rw [show 2 * (us.length + 1) = 2 + 2 * us.length from by omega, run_add, run_two,
      step_HS0_T (getD_at P true _), step_HS1,
      show P.length + 1 + 1 = (P ++ [true, u]).length from by simp,
      show P ++ (true :: u :: (flat2 us ++ Z))
        = (P ++ [true, u]) ++ (flat2 us ++ Z) from by simp,
      ih (P ++ [true, u]) Z ans]

/-- Outer seek over marked units. -/
theorem walkO (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * j)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run mulMachine (2 * (j + 1))
        ⟨(0, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(0, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_O0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_O1_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- Inner seek over marked units. -/
theorem walkI (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * j)
      ⟨(5, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(5, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run mulMachine (2 * (j + 1))
        ⟨(5, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(5, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_I0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_I1_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- The run walk: `getD`-conditioned. -/
theorem walkRun : ∀ (m : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < m, x.getD (p + i) false = true) →
    run mulMachine m ⟨(10, ans), p, x⟩ = ⟨(10, ans), p + m, x⟩
  | 0, x, p, ans, _ => rfl
  | m + 1, x, p, ans, h => by
    rw [show m + 1 = 1 + m from by omega, run_add, run_one,
      step_IR_T (by simpa using h 0 (by omega)),
      walkRun m x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + m) = p + 1 + m from by omega]

/-- The heal sweep: flips marked units back to live, two steps each. -/
theorem walkHeal (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run mulMachine (2 * j)
      ⟨(15, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(15, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j true) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run mulMachine (2 * (j + 1))
        ⟨(15, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(15, ans), P.length + 2 * (j + 1),
          P ++ (flat2 (List.replicate (j + 1) true) ++ Z)⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, true]).length + 2 * j from by
      simp; omega,
      show flat2 (List.replicate (j + 1) true)
        = true :: true :: flat2 (List.replicate j true) from by
        rw [List.replicate_succ]
        rfl]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_HH0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_HH1, writeAt_boundary,
      show (P ++ [true]).length + 1 = (P ++ [true, true]).length from by simp,
      show (P ++ [true]) ++ true :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, true]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, true]) Z ans]
    simp [List.append_assoc]

/-! ## The tape and the phase lemmas -/

/-- The multiplier tape: outer units `ob` (as a liveness list), the inner block
(`j` marked + `k` live), the run, the frontier zeros. -/
def mulTape (ob : List Bool) (j k s z : ℕ) (rest : List Bool) : List Bool :=
  flat2 ob ++ false :: false ::
    (flat2 (List.replicate j false) ++ (flat2 (List.replicate k true)
      ++ false :: false :: (List.replicate s true
        ++ (List.replicate z false ++ rest))))

/-- **One inner round**: mark the first live inner unit, deposit one `1`. -/
theorem innerRound (ob : List Bool) (j k s z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ 2 * ob.length + 2 * j + 2 * k + s + 9 ∧
      run mulMachine t ⟨(2, ans), 0, mulTape ob j (k + 1) s (z + 1) rest⟩
        = ⟨(2, ans), 0, mulTape ob (j + 1) k (s + 1) z rest⟩ := by
  refine ⟨2 * ob.length + (2 + (2 * j + (2 + (2 * k + (2 + (s + 1)))))), by omega, ?_⟩
  have hwS := walkSkip ob []
    (false :: false ::
      (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
        ++ false :: false :: (List.replicate s true
          ++ (false :: (List.replicate z false ++ rest))))))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwS
  have hHunt := walkHunt (List.replicate k true)
    (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)) ++ [true, false])
    (false :: false :: (List.replicate s true
      ++ (false :: (List.replicate z false ++ rest)))) ans
  rw [List.length_replicate] at hHunt
  rw [show (⟨(2, ans), 0, mulTape ob j (k + 1) s (z + 1) rest⟩ : Cfg mulMachine)
      = ⟨(2, ans), 0, flat2 ob ++ (false :: false ::
          (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest)))))))⟩ from by
      simp [mulTape, flat2, List.replicate_succ],
    run_add, hwS, run_add, run_two,
    show (2 * ob.length : ℕ) = (flat2 ob).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    step_IS0_F (getD_at (flat2 ob) false _),
    show (flat2 ob).length + 1 = (flat2 ob ++ [false]).length from by simp; try omega,
    show flat2 ob ++ (false :: false ::
        (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest)))))))
      = (flat2 ob ++ [false]) ++ false ::
          (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest)))))) from by simp,
    step_ISc,
    show (flat2 ob ++ [false]).length + 1 = (flat2 ob ++ [false, false]).length from by
      simp,
    show (flat2 ob ++ [false]) ++ false ::
        (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest))))))
      = (flat2 ob ++ [false, false])
          ++ (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest)))))) from by simp,
    run_add, walkI j (flat2 ob ++ [false, false]) _ ans,
    run_add, run_two,
    show (flat2 ob ++ [false, false]).length + 2 * j
      = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    show (flat2 ob ++ [false, false])
        ++ (flat2 (List.replicate j false) ++ (true :: true :: (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest))))))
      = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ true :: (true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest))))) from by simp,
    step_I0_T (getD_at _ true _),
    show ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)).length + 1
      = (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true]).length from by simp; try omega,
    show ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
        ++ true :: (true :: (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest)))))
      = (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)) ++ [true])
          ++ true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest)))) from by simp,
    step_I1_T (getD_at _ true _), writeAt_boundary,
    show ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)) ++ [true]))
        ++ false :: (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest))))
      = (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false])
          ++ (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate s true
              ++ (false :: (List.replicate z false ++ rest)))) from by simp,
    show (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
        ++ [true]).length + 1
      = ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false])).length from by simp; omega,
    run_add, hHunt,
    run_add, run_two,
    show ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false])).length + 2 * k
      = (((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false])) ++ flat2 (List.replicate k true)).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    show (((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
        ++ [true, false])
        ++ (flat2 (List.replicate k true)
          ++ false :: false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest))))
      = ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true))
          ++ false :: (false :: (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest)))) from by simp,
    step_Ih0_F (getD_at _ false _), step_Ihc,
    show ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true)).length + 1 + 1
      = (((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true))
          ++ [false, false]).length from by simp; omega,
    show ((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
        ++ [true, false]) ++ flat2 (List.replicate k true))
        ++ false :: (false :: (List.replicate s true
          ++ (false :: (List.replicate z false ++ rest))))
      = (((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true)) ++ [false, false])
          ++ (List.replicate s true
            ++ (false :: (List.replicate z false ++ rest))) from by simp,
    run_add, walkRun s _ _ ans (fun i hi => getD_run _ _ s i hi),
    run_one,
    show (((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true))
          ++ [false, false]).length + s
      = ((((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true)) ++ [false, false])
          ++ List.replicate s true).length from by simp; try omega,
    show ((((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
        ++ [true, false]) ++ flat2 (List.replicate k true)) ++ [false, false]))
        ++ (List.replicate s true ++ (false :: (List.replicate z false ++ rest)))
      = (((((((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
          ++ [true, false]) ++ flat2 (List.replicate k true)) ++ [false, false]))
          ++ List.replicate s true)
          ++ false :: (List.replicate z false ++ rest) from by simp,
    step_IR_F (getD_at _ false _), writeAt_boundary]
  have hrun1 : List.replicate s true ++ true :: (List.replicate z false ++ rest)
      = List.replicate (s + 1) true ++ (List.replicate z false ++ rest) := by
    have hm : List.replicate (s + 1) true = List.replicate s true ++ [true] := by
      rw [List.replicate_succ']
    rw [hm]
    simp
  have hin1 : flat2 (List.replicate (j + 1) false)
      = flat2 (List.replicate j false) ++ [true, false] := by
    have := List.replicate_succ' (n := j) (a := false)
    rw [this, flat2_append]
    rfl
  show (⟨(2, ans), 0, _⟩ : Cfg mulMachine) = _
  rw [show (⟨(2, ans), 0, mulTape ob (j + 1) k (s + 1) z rest⟩ : Cfg mulMachine)
      = ⟨(2, ans), 0, flat2 ob ++ false :: false ::
          ((flat2 (List.replicate j false) ++ [true, false])
            ++ (flat2 (List.replicate k true)
              ++ false :: false :: ((List.replicate s true ++ [true])
                ++ (List.replicate z false ++ rest))))⟩ from by
      simp only [mulTape, hin1]
      have hm : List.replicate (s + 1) true = List.replicate s true ++ [true] := by
        rw [List.replicate_succ']
      rw [hm]]
  simp [List.append_assoc]

/-- **The inner phase**: all `k` live inner units consumed, control at the heal entry. -/
theorem innerPhase : ∀ (k : ℕ) (ob : List Bool) (j s z : ℕ) (rest : List Bool)
    (ans : Bool),
    ∃ t, t ≤ (k + 1) * (2 * ob.length + 2 * (j + k) + s + k + 12) ∧
      run mulMachine t ⟨(2, ans), 0, mulTape ob j k s (z + k) rest⟩
        = ⟨(12, ans), 0, mulTape ob (j + k) 0 (s + k) z rest⟩ := by
  intro k
  induction k with
  | zero =>
    intro ob j s z rest ans
    refine ⟨2 * ob.length + (2 + (2 * j + 1)), by omega, ?_⟩
    have hwS := walkSkip ob []
      (false :: false ::
        (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
          ++ false :: false :: (List.replicate s true
            ++ (List.replicate z false ++ rest))))) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwS
    rw [show (⟨(2, ans), 0, mulTape ob j 0 s (z + 0) rest⟩ : Cfg mulMachine)
        = ⟨(2, ans), 0, flat2 ob ++ (false :: false ::
            (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
              ++ false :: false :: (List.replicate s true
                ++ (List.replicate z false ++ rest)))))⟩ from by simp [mulTape],
      run_add, hwS, run_add, run_two,
      show (2 * ob.length : ℕ) = (flat2 ob).length from by
        simp [DIndexMachine.flat2_length]; try omega,
      step_IS0_F (getD_at (flat2 ob) false _),
      show (flat2 ob).length + 1 = (flat2 ob ++ [false]).length from by simp; try omega,
      show flat2 ob ++ (false :: false ::
          (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
            ++ false :: false :: (List.replicate s true
              ++ (List.replicate z false ++ rest)))))
        = (flat2 ob ++ [false]) ++ false ::
            (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
              ++ false :: false :: (List.replicate s true
                ++ (List.replicate z false ++ rest)))) from by simp,
      step_ISc,
      show (flat2 ob ++ [false]).length + 1 = (flat2 ob ++ [false, false]).length from by
        simp,
      show (flat2 ob ++ [false]) ++ false ::
          (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
            ++ false :: false :: (List.replicate s true
              ++ (List.replicate z false ++ rest))))
        = (flat2 ob ++ [false, false])
            ++ (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
              ++ false :: false :: (List.replicate s true
                ++ (List.replicate z false ++ rest)))) from by simp,
      run_add, walkI j (flat2 ob ++ [false, false]) _ ans, run_one,
      show (flat2 ob ++ [false, false]).length + 2 * j
        = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false)).length from by
        simp [DIndexMachine.flat2_length]; try omega,
      show (flat2 ob ++ [false, false])
          ++ (flat2 (List.replicate j false) ++ (flat2 (List.replicate 0 true)
            ++ false :: false :: (List.replicate s true
              ++ (List.replicate z false ++ rest))))
        = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate j false))
            ++ false :: (false :: (List.replicate s true
              ++ (List.replicate z false ++ rest))) from by simp [flat2],
      step_I0_F (getD_at _ false _)]
    simp [mulTape, flat2, List.append_assoc]
  | succ k ih =>
    intro ob j s z rest ans
    obtain ⟨t₁, ht₁, hr₁⟩ := innerRound ob j k s (z + k) rest ans
    obtain ⟨t₂, ht₂, hr₂⟩ := ih ob (j + 1) (s + 1) z rest ans
    refine ⟨t₁ + t₂, by
      have hexp : (k + 1 + 1) * (2 * ob.length + 2 * (j + (k + 1)) + s + (k + 1) + 12)
          = (k + 1) * (2 * ob.length + 2 * (j + (k + 1)) + s + (k + 1) + 12)
            + (2 * ob.length + 2 * (j + (k + 1)) + s + (k + 1) + 12) := by ring
      have hmono : (k + 1) * (2 * ob.length + 2 * (j + 1 + k) + (s + 1) + k + 12)
          ≤ (k + 1) * (2 * ob.length + 2 * (j + (k + 1)) + s + (k + 1) + 12) :=
        Nat.mul_le_mul_left _ (by omega)
      omega, ?_⟩
    rw [run_add,
      show mulTape ob j (k + 1) s (z + (k + 1)) rest
        = mulTape ob j (k + 1) s (z + k + 1) rest from by
        rw [show z + (k + 1) = z + k + 1 from by omega],
      hr₁, hr₂,
      show j + 1 + k = j + (k + 1) from by omega,
      show s + 1 + k = s + (k + 1) from by omega]

/-- **The heal phase**: the inner block re-armed, control back at the outer seek. -/
theorem healPhase (ob : List Bool) (b s z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ 2 * ob.length + 2 * b + 4 ∧
      run mulMachine t ⟨(12, ans), 0, mulTape ob b 0 s z rest⟩
        = ⟨(0, ans), 0, mulTape ob 0 b s z rest⟩ := by
  refine ⟨2 * ob.length + (2 + (2 * b + 1)), by omega, ?_⟩
  have hwS := walkHS ob []
    (false :: false ::
      (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
        ++ (List.replicate z false ++ rest)))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwS
  rw [show (⟨(12, ans), 0, mulTape ob b 0 s z rest⟩ : Cfg mulMachine)
      = ⟨(12, ans), 0, flat2 ob ++ (false :: false ::
          (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
            ++ (List.replicate z false ++ rest))))⟩ from by simp [mulTape, flat2],
    run_add, hwS, run_add, run_two,
    show (2 * ob.length : ℕ) = (flat2 ob).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    step_HS0_F (getD_at (flat2 ob) false _),
    show (flat2 ob).length + 1 = (flat2 ob ++ [false]).length from by simp; try omega,
    show flat2 ob ++ (false :: false ::
        (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
          ++ (List.replicate z false ++ rest))))
      = (flat2 ob ++ [false]) ++ false ::
          (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
            ++ (List.replicate z false ++ rest))) from by simp,
    step_HSc,
    show (flat2 ob ++ [false]).length + 1 = (flat2 ob ++ [false, false]).length from by
      simp,
    show (flat2 ob ++ [false]) ++ false ::
        (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
          ++ (List.replicate z false ++ rest)))
      = (flat2 ob ++ [false, false])
          ++ (flat2 (List.replicate b false) ++ false :: false :: (List.replicate s true
            ++ (List.replicate z false ++ rest))) from by simp,
    run_add, walkHeal b (flat2 ob ++ [false, false]) _ ans, run_one,
    show (flat2 ob ++ [false, false]).length + 2 * b
      = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate b true)).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    show (flat2 ob ++ [false, false])
        ++ (flat2 (List.replicate b true) ++ false :: false :: (List.replicate s true
          ++ (List.replicate z false ++ rest)))
      = ((flat2 ob ++ [false, false]) ++ flat2 (List.replicate b true))
          ++ false :: (false :: (List.replicate s true
            ++ (List.replicate z false ++ rest))) from by simp,
    step_HH0_F (getD_at _ false _)]
  simp [mulTape, flat2, List.append_assoc]

/-- **One outer round**: consume a live outer unit, run the inner phase, heal. -/
theorem outerRound (i a b s z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ (b + 3) * (2 * (i + a) + 2 * b + s + b + 22) ∧
      run mulMachine t
        ⟨(0, ans), 0, mulTape (List.replicate i false ++ List.replicate (a + 1) true)
          0 b s (z + b) rest⟩
        = ⟨(0, ans), 0, mulTape (List.replicate (i + 1) false ++ List.replicate a true)
            0 b (s + b) z rest⟩ := by
  obtain ⟨t₂, ht₂, hr₂⟩ := innerPhase b
    (List.replicate (i + 1) false ++ List.replicate a true) 0 s z rest ans
  obtain ⟨t₃, ht₃, hr₃⟩ := healPhase
    (List.replicate (i + 1) false ++ List.replicate a true) b (s + b) z rest ans
  have hsplit : flat2 (List.replicate i false ++ List.replicate (a + 1) true)
      = flat2 (List.replicate i false)
          ++ true :: true :: flat2 (List.replicate a true) := by
    rw [flat2_append, List.replicate_succ]
    rfl
  have hfold : (flat2 (List.replicate i false) ++ [true])
      ++ false :: flat2 (List.replicate a true)
      = flat2 (List.replicate (i + 1) false ++ List.replicate a true) := by
    rw [flat2_append]
    have h1 : flat2 (List.replicate (i + 1) false)
        = flat2 (List.replicate i false) ++ [true, false] := by
      have := List.replicate_succ' (n := i) (a := false)
      rw [this, flat2_append]
      rfl
    rw [h1]
    simp
  refine ⟨2 * i + (2 + (t₂ + t₃)), by
    have hlen : (List.replicate (i + 1) false ++ List.replicate a true).length
        = i + 1 + a := by simp
    rw [hlen] at ht₂ ht₃
    have hmono : (b + 1) * (2 * (i + 1 + a) + 2 * (0 + b) + s + b + 12)
        ≤ (b + 1) * (2 * (i + a) + 2 * b + s + b + 22) := by
      refine Nat.mul_le_mul_left _ (by omega)
    have hexp : (b + 3) * (2 * (i + a) + 2 * b + s + b + 22)
        = (b + 1) * (2 * (i + a) + 2 * b + s + b + 22)
          + 2 * (2 * (i + a) + 2 * b + s + b + 22) := by ring
    omega, ?_⟩
  have hwO := walkO i []
    (true :: (true :: (flat2 (List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest))))))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwO
  rw [run_add,
    show (⟨(0, ans), 0, mulTape (List.replicate i false ++ List.replicate (a + 1) true)
        0 b s (z + b) rest⟩ : Cfg mulMachine)
      = ⟨(0, ans), 0, flat2 (List.replicate i false)
          ++ (true :: (true :: (flat2 (List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest)))))))⟩ from by
      simp [mulTape, hsplit],
    hwO, run_add, run_two,
    show (2 * i : ℕ) = (flat2 (List.replicate i false)).length from by
      simp [DIndexMachine.flat2_length],
    step_O0_T (getD_at _ true _),
    show (flat2 (List.replicate i false)).length + 1
      = (flat2 (List.replicate i false) ++ [true]).length from by simp,
    show flat2 (List.replicate i false)
        ++ (true :: (true :: (flat2 (List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest)))))))
      = (flat2 (List.replicate i false) ++ [true])
          ++ true :: (flat2 (List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest))))) from by simp,
    step_O1_T (getD_at _ true _), writeAt_boundary,
    show (flat2 (List.replicate i false) ++ [true])
        ++ false :: (flat2 (List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest)))))
      = mulTape (List.replicate (i + 1) false ++ List.replicate a true)
          0 b s (z + b) rest from by
      show _ = flat2 (List.replicate (i + 1) false ++ List.replicate a true) ++ false :: false ::
      (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
        ++ false :: false :: (List.replicate s true
          ++ (List.replicate (z + b) false ++ rest))))
      rw [← hfold]
      simp,
    run_add, hr₂,
    show (0 : ℕ) + b = b from by omega,
    hr₃]

/-- **The grand run**: all `a` outer units consumed, the run grown by `a·b`. -/
theorem mulM_rounds : ∀ (a i b s z : ℕ) (rest : List Bool) (ans : Bool),
    ∃ t, t ≤ (a + 1) * ((b + 3) * (2 * (i + a) + 2 * b + (s + a * b) + b + 22))
        + 2 * (i + a) + 1 ∧
      run mulMachine t
        ⟨(0, ans), 0, mulTape (List.replicate i false ++ List.replicate a true)
          0 b s (z + a * b) rest⟩
        = ⟨(17, ans), 2 * (i + a),
            mulTape (List.replicate (i + a) false) 0 b (s + a * b) z rest⟩ := by
  intro a
  induction a with
  | zero =>
    intro i b s z rest ans
    refine ⟨2 * i + 1, by omega, ?_⟩
    have hwO := walkO i []
      (false :: false ::
        (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
          ++ false :: false :: (List.replicate s true
            ++ (List.replicate (z + 0 * b) false ++ rest))))) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwO
    rw [run_add, run_one,
      show (⟨(0, ans), 0, mulTape (List.replicate i false ++ List.replicate 0 true)
          0 b s (z + 0 * b) rest⟩ : Cfg mulMachine)
        = ⟨(0, ans), 0, flat2 (List.replicate i false)
            ++ (false :: false ::
              (flat2 (List.replicate 0 false) ++ (flat2 (List.replicate b true)
                ++ false :: false :: (List.replicate s true
                  ++ (List.replicate (z + 0 * b) false ++ rest)))))⟩ from by
        simp [mulTape],
      hwO,
      show (2 * i : ℕ) = (flat2 (List.replicate i false)).length from by
        simp [DIndexMachine.flat2_length],
      step_O0_F (getD_at _ false _)]
    simp [mulTape, DIndexMachine.flat2_length]
  | succ a ih =>
    intro i b s z rest ans
    obtain ⟨t₁, ht₁, hr₁⟩ := outerRound i a b s (z + a * b) rest ans
    obtain ⟨t₂, ht₂, hr₂⟩ := ih (i + 1) b (s + b) z rest ans
    refine ⟨t₁ + t₂, by
      have hX : (b + 3) * (2 * (i + a) + 2 * b + s + b + 22)
          ≤ (b + 3) * (2 * (i + (a + 1)) + 2 * b + (s + (a + 1) * b) + b + 22) := by
        refine Nat.mul_le_mul_left _ (by
          have : a * b + b = (a + 1) * b := by ring
          omega)
      have hY : (a + 1) * ((b + 3) * (2 * (i + 1 + a) + 2 * b + (s + b + a * b) + b + 22))
          ≤ (a + 1) * ((b + 3) * (2 * (i + (a + 1)) + 2 * b + (s + (a + 1) * b) + b + 22)) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by
          have : s + b + a * b = s + (a + 1) * b := by ring
          omega))
      have hexp : (a + 1 + 1) * ((b + 3) * (2 * (i + (a + 1)) + 2 * b
            + (s + (a + 1) * b) + b + 22))
          = (a + 1) * ((b + 3) * (2 * (i + (a + 1)) + 2 * b + (s + (a + 1) * b) + b + 22))
            + (b + 3) * (2 * (i + (a + 1)) + 2 * b + (s + (a + 1) * b) + b + 22) := by
        ring
      omega, ?_⟩
    rw [run_add,
      show z + (a + 1) * b = z + a * b + b from by ring_nf,
      hr₁, hr₂,
      show i + 1 + a = i + (a + 1) from by omega,
      show s + b + a * b = s + (a + 1) * b from by ring_nf]

/-- **The multiplier**: on `[T,T]^a [F,F] [T,T]^b [F,F] 1^s 0^(z+a·b) rest`, the run
grows by `a·b` and the machine halts with the outer block consumed and the inner block
healed. -/
theorem mulM_run (a b s z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ (a + 1) * ((b + 3) * (2 * a + 2 * b + (s + a * b) + b + 22)) + 2 * a + 1 ∧
      run mulMachine t
        ⟨(0, ans), 0, mulTape (List.replicate a true) 0 b s (z + a * b) rest⟩
        = ⟨(17, ans), 2 * a, mulTape (List.replicate a false) 0 b (s + a * b) z rest⟩ := by
  have h := mulM_rounds a 0 b s z rest ans
  simpa using h

end PallLean.Paper93.DeepMath.PathB.UnaryMulMachine
