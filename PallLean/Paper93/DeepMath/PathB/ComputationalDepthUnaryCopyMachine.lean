import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryAddMachine

/-!
# The multiplication sub-arc, brick 2: the copy machine

**The shuttle.**  `copyMachine` copies a doubled-unit block's count into a plain unary
accumulator: on

  `[T,T]^k [F,F] 1^s 0 rest`   (k live units, accumulator seeded at `s ≥ 0`)

it consumes the units one per round — mark the first live unit (`[T,T] ↦ [T,F]`), walk
right past the block's terminator and the accumulator to the frontier (the first `0`
after the `1`-run), deposit a `1`, reset — and halts when no live unit remains, leaving

  `[T,F]^k [F,F] 1^(s+k) 0 rest`.

The marks are the record: the multiplier (next brick) re-arms the block with the heal
sweep, and iterating copy-heal over a second counter block is multiplication.

**Convention (morph-arc precedent).**  `copyMachine` is *pipeline-internal*: it is
specified by an exact run lemma on its well-formed tapes (`copyM_rounds`, a grand
induction over the live count with marked-prefix generalization), not by a
`Transduces`-on-all-inputs claim — garbage-totality is owed only at the assembled
pipeline's outer boundary, exactly as the emitter arc's machines were specified.  The
walk fabric: unit-list walks with growing prefix for the marked/live blocks,
`getD`-conditioned walks (`walkC`) for the accumulator run.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The machine -/

/-- States: `0` seek the first live unit (halt at the terminator), `1` its mark cell,
`2`/`3` walk the remaining units to the terminator, `4` cross, `5` walk the
accumulator to the frontier and deposit, `6` halt. -/
def copyMachine : Machine where
  State := Fin 7 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 6)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((6, s.2), none, 2))
    else if s.1 = 1 then
      (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, s.2), none, 1))
    else if s.1 = 3 then ((2, s.2), none, 1)
    else if s.1 = 4 then ((5, s.2), none, 1)
    else if s.1 = 5 then
      (if b then ((5, s.2), none, 1) else ((0, s.2), some true, 3))
    else ((6, s.2), none, 2)
  accept := fun s => s.2

theorem step_A0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step copyMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_A0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step copyMachine ⟨(0, ans), p, x⟩ = ⟨(6, ans), p, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_A1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step copyMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_A1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step copyMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_B0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step copyMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_B0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step copyMachine ⟨(2, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_B1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step copyMachine ⟨(3, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

theorem step_cross {ans : Bool} {p : ℕ} {x : List Bool} :
    step copyMachine ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, moveHead]; rfl

theorem step_C_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step copyMachine ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

theorem step_C_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step copyMachine ⟨(5, ans), p, x⟩ = ⟨(0, ans), 0, writeAt x p true⟩ := by
  simp only [step, copyMachine, h, moveHead]; rfl

/-! ## Walks -/

/-- Seek over marked units `[T,F]`: two steps each, tape unchanged. -/
theorem walkMarked (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run copyMachine (2 * j)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run copyMachine (2 * (j + 1))
        ⟨(0, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(0, ans), P.length + 2 * (j + 1),
          P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
    rw [show P.length + 2 * (j + 1) = (P ++ [true, false]).length + 2 * j from by
      simp; omega]
    rw [show 2 * (j + 1) = 2 + 2 * j from by omega, run_add, run_two,
      step_A0_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z) from by simp,
      step_A1_F (getD_at (P ++ [true]) false _),
      show (P ++ [true]).length + 1 = (P ++ [true, false]).length from by simp,
      show (P ++ [true]) ++ false :: (flat2 (List.replicate j false) ++ Z)
        = (P ++ [true, false]) ++ (flat2 (List.replicate j false) ++ Z) from by simp,
      ih (P ++ [true, false]) Z ans]

/-- Seek over live units `[T,T]` in the terminator hunt: two steps each. -/
theorem walkLive (k : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run copyMachine (2 * k)
      ⟨(2, ans), P.length, P ++ (flat2 (List.replicate k true) ++ Z)⟩
      = ⟨(2, ans), P.length + 2 * k, P ++ (flat2 (List.replicate k true) ++ Z)⟩ := by
  induction k with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ k ih =>
    intro P Z ans
    show run copyMachine (2 * (k + 1))
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

/-- Walk the accumulator run: `getD`-conditioned. -/
theorem walkC : ∀ (m : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < m, x.getD (p + i) false = true) →
    run copyMachine m ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + m, x⟩
  | 0, x, p, ans, _ => rfl
  | m + 1, x, p, ans, h => by
    rw [show m + 1 = 1 + m from by omega, run_add, run_one,
      step_C_T (by simpa using h 0 (by omega)),
      walkC m x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + m) = p + 1 + m from by omega]

/-! ## The well-formed tape and the grand run lemma -/

/-- Read inside the accumulator run. -/
theorem getD_run (P Z : List Bool) (m i : ℕ) (hi : i < m) :
    (P ++ (List.replicate m true ++ Z)).getD (P.length + i) false = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show P.length + i - P.length = i from by omega,
    List.getElem?_append_left (by simpa using hi), List.getElem?_replicate]
  simp [hi]

/-- The copy tape: `j` marked units, `k` live units, the terminator, the accumulator
run (seed `s` plus the `j` deposits so far), and `k+1` frontier zeros (one is consumed
per remaining round, one survives as the final frontier). -/
def copyTape (j k s : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate j false) ++ (flat2 (List.replicate k true)
    ++ false :: false :: (List.replicate (s + j) true
      ++ (List.replicate (k + 1) false ++ rest)))

/-- **The grand run lemma**: from any mixed state, the machine consumes the `k` live
units one per round, deposits `k` ones into the run, and halts at the terminator. -/
theorem copyM_rounds : ∀ (k j s : ℕ) (rest : List Bool) (ans : Bool),
    ∃ t ≤ (k + 1) * (3 * (j + k) + s + 10) + 2 * (j + k) + 1,
      run copyMachine t ⟨(0, ans), 0, copyTape j k s rest⟩
        = ⟨(6, ans), 2 * (j + k), copyTape (j + k) 0 s rest⟩ := by
  intro k
  induction k with
  | zero =>
    intro j s rest ans
    refine ⟨2 * j + 1, by omega, ?_⟩
    have hw := walkMarked j [] (flat2 (List.replicate 0 true)
      ++ false :: false :: (List.replicate (s + j) true
        ++ (List.replicate 1 false ++ rest))) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hw
    rw [run_add, run_one,
      show (⟨(0, ans), 0, copyTape j 0 s rest⟩ : Cfg copyMachine)
        = ⟨(0, ans), 0, flat2 (List.replicate j false)
            ++ (flat2 (List.replicate 0 true)
              ++ false :: false :: (List.replicate (s + j) true
                ++ (List.replicate 1 false ++ rest)))⟩ from rfl,
      hw]
    have hread : (flat2 (List.replicate j false)
        ++ (flat2 (List.replicate 0 true)
          ++ false :: false :: (List.replicate (s + j) true
            ++ (List.replicate 1 false ++ rest)))).getD (2 * j) false = false := by
      rw [show (2 * j : ℕ) = (flat2 (List.replicate j false)).length from by
        simp [DIndexMachine.flat2_length]]
      have := getD_at (flat2 (List.replicate j false)) false
        (false :: (List.replicate (s + j) true ++ (List.replicate 1 false ++ rest)))
      simp [flat2] at this ⊢
    rw [step_A0_F hread]
    simp [copyTape, flat2]
  | succ k ih =>
    intro j s rest ans
    obtain ⟨t', ht', hrun'⟩ := ih (j + 1) s rest ans
    refine ⟨2 * j + (2 + (2 * k + (1 + (1 + ((s + j) + (1 + t')))))), by
      have hb : (k + 1) * (3 * (j + 1 + k) + s + 10)
          ≤ (k + 1) * (3 * (j + (k + 1)) + s + 10) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : (k + 1 + 1) * (3 * (j + (k + 1)) + s + 10)
          = (k + 1) * (3 * (j + (k + 1)) + s + 10)
            + (3 * (j + (k + 1)) + s + 10) := by ring
      omega, ?_⟩
    rw [show (2 * (j + (k + 1)) : ℕ) = 2 * (j + 1 + k) from by omega,
      show (j + (k + 1) : ℕ) = j + 1 + k from by omega]
    have hwM := walkMarked j []
      (true :: true :: (flat2 (List.replicate k true)
        ++ false :: false :: (List.replicate (s + j) true
          ++ (List.replicate (k + 2) false ++ rest)))) ans
    simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwM
    rw [show (⟨(0, ans), 0, copyTape j (k + 1) s rest⟩ : Cfg copyMachine)
        = ⟨(0, ans), 0, flat2 (List.replicate j false)
            ++ (true :: true :: (flat2 (List.replicate k true)
              ++ false :: false :: (List.replicate (s + j) true
                ++ (List.replicate (k + 2) false ++ rest))))⟩ from by
        simp [copyTape, flat2, List.replicate_succ],
      run_add, hwM, run_add, run_two,
      show (2 * j : ℕ) = (flat2 (List.replicate j false)).length from by
        simp [DIndexMachine.flat2_length],
      step_A0_T (getD_at (flat2 (List.replicate j false)) true _),
      show (flat2 (List.replicate j false)).length + 1
        = (flat2 (List.replicate j false) ++ [true]).length from by simp,
      show flat2 (List.replicate j false)
          ++ (true :: true :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate (s + j) true
              ++ (List.replicate (k + 2) false ++ rest))))
        = (flat2 (List.replicate j false) ++ [true])
            ++ true :: (flat2 (List.replicate k true)
              ++ false :: false :: (List.replicate (s + j) true
                ++ (List.replicate (k + 2) false ++ rest))) from by simp,
      step_A1_T (getD_at (flat2 (List.replicate j false) ++ [true]) true _),
      writeAt_boundary]
    rw [show (flat2 (List.replicate j false) ++ [true])
          ++ false :: (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate (s + j) true
              ++ (List.replicate (k + 2) false ++ rest)))
        = flat2 (List.replicate (j + 1) false)
            ++ (flat2 (List.replicate k true)
              ++ false :: false :: (List.replicate (s + j) true
                ++ (List.replicate (k + 2) false ++ rest))) from by
        have hsplit : flat2 (List.replicate (j + 1) false)
            = flat2 (List.replicate j false) ++ [true, false] := by
          rw [List.replicate_succ', flat2_append]
          rfl
        rw [hsplit]
        simp,
      show (flat2 (List.replicate j false) ++ [true]).length + 1
        = (flat2 (List.replicate (j + 1) false)).length from by
        simp [DIndexMachine.flat2_length]
        omega,
      run_add, walkLive k (flat2 (List.replicate (j + 1) false)) _ ans,
      run_add, run_one,
      show (flat2 (List.replicate (j + 1) false)).length + 2 * k
        = (flat2 (List.replicate (j + 1) false)
            ++ flat2 (List.replicate k true)).length from by
        simp [DIndexMachine.flat2_length],
      show flat2 (List.replicate (j + 1) false)
          ++ (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate (s + j) true
              ++ (List.replicate (k + 2) false ++ rest)))
        = (flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ false :: (false :: (List.replicate (s + j) true
              ++ (List.replicate (k + 2) false ++ rest))) from by simp,
      step_B0_F (getD_at _ false _),
      run_add, run_one, step_cross]
    rw [show (flat2 (List.replicate (j + 1) false)
            ++ flat2 (List.replicate k true)).length + 1 + 1
        = ((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false]).length from by simp; omega,
      show (flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
          ++ false :: (false :: (List.replicate (s + j) true
            ++ (List.replicate (k + 2) false ++ rest)))
        = ((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false])
            ++ (List.replicate (s + j) true
              ++ (List.replicate (k + 2) false ++ rest)) from by simp,
      run_add,
      walkC (s + j) _ _ ans (fun i hi => getD_run _ _ (s + j) i hi),
      run_add, run_one]
    rw [show ((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false]).length + (s + j)
        = (((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false]) ++ List.replicate (s + j) true).length from by
        simp; omega,
      show ((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false])
          ++ (List.replicate (s + j) true
            ++ (List.replicate (k + 2) false ++ rest))
        = (((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false]) ++ List.replicate (s + j) true)
            ++ false :: (List.replicate (k + 1) false ++ rest) from by
        simp [List.replicate_succ],
      step_C_F (getD_at _ false _),
      writeAt_boundary]
    rw [show (((flat2 (List.replicate (j + 1) false) ++ flat2 (List.replicate k true))
            ++ [false, false]) ++ List.replicate (s + j) true)
          ++ true :: (List.replicate (k + 1) false ++ rest)
        = copyTape (j + 1) k s rest from by
        simp only [copyTape, List.append_assoc, List.cons_append, List.nil_append]
        have hm : List.replicate (s + j + 1) true
            = List.replicate (s + j) true ++ [true] := by
          rw [List.replicate_succ']
        rw [show s + (j + 1) = s + j + 1 from by omega, hm]
        simp [List.append_assoc],
      hrun']

end PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine
