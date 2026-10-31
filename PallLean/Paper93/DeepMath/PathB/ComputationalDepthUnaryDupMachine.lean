import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryMulMachine

/-!
# The multiplication sub-arc, brick 4a: the duplicator

**The squaring enabler.**  `dupMachine` copies a doubled block as *new doubled units*
at the frontier and then heals its source: on

  `[T,T]^a [F,F] 0^(2a+w) rest`

it deposits `a` fresh `[T,T]` units after the terminator (each round: mark a source
unit, hunt to the terminator, cross, walk the deposited units — a contiguous `T`-run —
to the frontier, write `T,T`, reset) and, once the source is exhausted, sweeps it back
to fully live, halting with

  `[T,T]^a [F,F] [T,T]^a 0^w rest`.

With `w ≥ 2` the leftover zeros read as the copy's own `[F,F]` terminator, so
`dup ⨟ mul` is squaring: the healed source is `mul`'s outer block and the copy its
inner block, verbatim.  Same fabric as `copyMachine`/`mulMachine`: unit walks with
growing prefix, `getD`-conditioned frontier walk (via `flat2_replicate_true`), zeros
telescoping two per round.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryDupMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 flat2_append getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.UnaryCopyMachine (getD_run)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- Doubled all-live blocks are contiguous `T`-runs. -/
theorem flat2_replicate_true (s : ℕ) :
    flat2 (List.replicate s true) = List.replicate (2 * s) true := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show true :: true :: flat2 (List.replicate s true)
      = List.replicate (2 * (s + 1)) true
    rw [ih, show 2 * (s + 1) = 2 * s + 1 + 1 from by omega,
      List.replicate_succ, List.replicate_succ]

/-! ## The machine -/

/-- States: `0`/`1` source seek+mark (to heal at the terminator), `2`/`3` hunt,
`4` cross, `5` frontier walk + first deposit cell, `7` second deposit cell,
`8`/`9` heal sweep, `6` halt. -/
def dupMachine : Machine where
  State := Fin 10 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 6)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((8, s.2), none, 3))
    else if s.1 = 1 then
      (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, s.2), none, 1))
    else if s.1 = 3 then ((2, s.2), none, 1)
    else if s.1 = 4 then ((5, s.2), none, 1)
    else if s.1 = 5 then
      (if b then ((5, s.2), none, 1) else ((7, s.2), some true, 1))
    else if s.1 = 7 then ((0, s.2), some true, 3)
    else if s.1 = 8 then (if b then ((9, s.2), none, 1) else ((6, s.2), none, 2))
    else if s.1 = 9 then ((8, s.2), some true, 1)
    else ((6, s.2), none, 2)
  accept := fun s => s.2

theorem step_A0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dupMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_A0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dupMachine ⟨(0, ans), p, x⟩ = ⟨(8, ans), 0, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_A1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dupMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_A1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dupMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_B0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dupMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_B0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dupMachine ⟨(2, ans), p, x⟩ = ⟨(4, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_B1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dupMachine ⟨(3, ans), p, x⟩ = ⟨(2, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, moveHead]; rfl

theorem step_cross {ans : Bool} {p : ℕ} {x : List Bool} :
    step dupMachine ⟨(4, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, moveHead]; rfl

theorem step_C_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dupMachine ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_C_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dupMachine ⟨(5, ans), p, x⟩ = ⟨(7, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_D {ans : Bool} {p : ℕ} {x : List Bool} :
    step dupMachine ⟨(7, ans), p, x⟩ = ⟨(0, ans), 0, writeAt x p true⟩ := by
  simp only [step, dupMachine, moveHead]; rfl

theorem step_HH0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step dupMachine ⟨(8, ans), p, x⟩ = ⟨(9, ans), p + 1, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_HH0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step dupMachine ⟨(8, ans), p, x⟩ = ⟨(6, ans), p, x⟩ := by
  simp only [step, dupMachine, h, moveHead]; rfl

theorem step_HH1 {ans : Bool} {p : ℕ} {x : List Bool} :
    step dupMachine ⟨(9, ans), p, x⟩ = ⟨(8, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, dupMachine, moveHead]; rfl

/-! ## Walks -/

/-- Seek over marked source units. -/
theorem walkA (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run dupMachine (2 * j)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j false) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run dupMachine (2 * (j + 1))
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

/-- Hunt over any units. -/
theorem walkHunt (us : List Bool) : ∀ (P Z : List Bool) (ans : Bool),
    run dupMachine (2 * us.length) ⟨(2, ans), P.length, P ++ (flat2 us ++ Z)⟩
      = ⟨(2, ans), P.length + 2 * us.length, P ++ (flat2 us ++ Z)⟩ := by
  induction us with
  | nil => intro P Z ans; simp [flat2, run_zero]
  | cons u us ih =>
    intro P Z ans
    show run dupMachine (2 * (us.length + 1))
        ⟨(2, ans), P.length, P ++ (true :: u :: (flat2 us ++ Z))⟩
      = ⟨(2, ans), P.length + 2 * (us.length + 1), P ++ (true :: u :: (flat2 us ++ Z))⟩
    rw [show P.length + 2 * (us.length + 1) = (P ++ [true, u]).length + 2 * us.length
        from by simp; omega]
    rw [show 2 * (us.length + 1) = 2 + 2 * us.length from by omega, run_add, run_two,
      step_B0_T (getD_at P true _), step_B1,
      show P.length + 1 + 1 = (P ++ [true, u]).length from by simp,
      show P ++ (true :: u :: (flat2 us ++ Z))
        = (P ++ [true, u]) ++ (flat2 us ++ Z) from by simp,
      ih (P ++ [true, u]) Z ans]

/-- The frontier walk over deposited units: `getD`-conditioned. -/
theorem walkC : ∀ (m : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < m, x.getD (p + i) false = true) →
    run dupMachine m ⟨(5, ans), p, x⟩ = ⟨(5, ans), p + m, x⟩
  | 0, x, p, ans, _ => rfl
  | m + 1, x, p, ans, h => by
    rw [show m + 1 = 1 + m from by omega, run_add, run_one,
      step_C_T (by simpa using h 0 (by omega)),
      walkC m x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + m) = p + 1 + m from by omega]

/-- The heal sweep. -/
theorem walkHeal (j : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run dupMachine (2 * j)
      ⟨(8, ans), P.length, P ++ (flat2 (List.replicate j false) ++ Z)⟩
      = ⟨(8, ans), P.length + 2 * j, P ++ (flat2 (List.replicate j true) ++ Z)⟩ := by
  induction j with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ j ih =>
    intro P Z ans
    show run dupMachine (2 * (j + 1))
        ⟨(8, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate j false) ++ Z))⟩
      = ⟨(8, ans), P.length + 2 * (j + 1),
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

/-! ## The tape and the grand run -/

/-- The duplicator tape: `j` marked + `k` live source units, `s` deposited copy units,
`z` frontier zeros. -/
def dupTape (j k s z : ℕ) (rest : List Bool) : List Bool :=
  flat2 (List.replicate j false) ++ (flat2 (List.replicate k true)
    ++ false :: false :: (flat2 (List.replicate s true)
      ++ (List.replicate z false ++ rest)))

/-- **One round**: mark a source unit, deposit a fresh `[T,T]` unit at the frontier. -/
theorem dupRound (j k s z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ 2 * j + 2 * k + 2 * s + 9 ∧
      run dupMachine t ⟨(0, ans), 0, dupTape j (k + 1) s (z + 2) rest⟩
        = ⟨(0, ans), 0, dupTape (j + 1) k (s + 1) z rest⟩ := by
  refine ⟨2 * j + (2 + (2 * k + (2 + (2 * s + (1 + 1))))), by omega, ?_⟩
  have hwA := walkA j []
    (true :: (true :: (flat2 (List.replicate k true)
      ++ false :: false :: (flat2 (List.replicate s true)
        ++ (false :: (false :: (List.replicate z false ++ rest))))))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwA
  have hHunt := walkHunt (List.replicate k true)
    ((flat2 (List.replicate j false) ++ [true, false]))
    (false :: false :: (flat2 (List.replicate s true)
      ++ (false :: (false :: (List.replicate z false ++ rest))))) ans
  rw [List.length_replicate] at hHunt
  rw [run_add,
    show (⟨(0, ans), 0, dupTape j (k + 1) s (z + 2) rest⟩ : Cfg dupMachine)
      = ⟨(0, ans), 0, flat2 (List.replicate j false)
          ++ (true :: (true :: (flat2 (List.replicate k true)
            ++ false :: false :: (flat2 (List.replicate s true)
              ++ (false :: (false :: (List.replicate z false ++ rest)))))))⟩ from by
      simp [dupTape, flat2, List.replicate_succ],
    hwA, run_add, run_two,
    show (2 * j : ℕ) = (flat2 (List.replicate j false)).length from by
      simp [DIndexMachine.flat2_length],
    step_A0_T (getD_at _ true _),
    show (flat2 (List.replicate j false)).length + 1
      = (flat2 (List.replicate j false) ++ [true]).length from by simp,
    show flat2 (List.replicate j false)
        ++ (true :: (true :: (flat2 (List.replicate k true)
          ++ false :: false :: (flat2 (List.replicate s true)
            ++ (false :: (false :: (List.replicate z false ++ rest)))))))
      = (flat2 (List.replicate j false) ++ [true])
          ++ true :: (flat2 (List.replicate k true)
            ++ false :: false :: (flat2 (List.replicate s true)
              ++ (false :: (false :: (List.replicate z false ++ rest))))) from by simp,
    step_A1_T (getD_at _ true _), writeAt_boundary,
    show (flat2 (List.replicate j false) ++ [true])
        ++ false :: (flat2 (List.replicate k true)
          ++ false :: false :: (flat2 (List.replicate s true)
            ++ (false :: (false :: (List.replicate z false ++ rest)))))
      = (flat2 (List.replicate j false) ++ [true, false])
          ++ (flat2 (List.replicate k true)
            ++ false :: false :: (flat2 (List.replicate s true)
              ++ (false :: (false :: (List.replicate z false ++ rest))))) from by simp,
    show (flat2 (List.replicate j false) ++ [true]).length + 1
      = (flat2 (List.replicate j false) ++ [true, false]).length from by
      simp
      try omega,
    run_add, hHunt, run_add, run_two,
    show (flat2 (List.replicate j false) ++ [true, false]).length + 2 * k
      = ((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)).length from by
      simp [DIndexMachine.flat2_length]; try omega,
    show (flat2 (List.replicate j false) ++ [true, false])
        ++ (flat2 (List.replicate k true)
          ++ false :: false :: (flat2 (List.replicate s true)
            ++ (false :: (false :: (List.replicate z false ++ rest)))))
      = ((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true))
          ++ false :: (false :: (flat2 (List.replicate s true)
            ++ (false :: (false :: (List.replicate z false ++ rest))))) from by simp,
    step_B0_F (getD_at _ false _), step_cross,
    show ((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)).length + 1 + 1
      = (((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false]).length from by
      simp; try omega,
    show ((flat2 (List.replicate j false) ++ [true, false])
        ++ flat2 (List.replicate k true))
        ++ false :: (false :: (flat2 (List.replicate s true)
          ++ (false :: (false :: (List.replicate z false ++ rest)))))
      = (((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false])
          ++ (List.replicate (2 * s) true
            ++ (false :: (false :: (List.replicate z false ++ rest)))) from by
      rw [← flat2_replicate_true]
      simp,
    run_add,
    walkC (2 * s) _ _ ans (fun i hi => getD_run _ _ (2 * s) i hi),
    run_add, run_one, run_one,
    show (((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false]).length + 2 * s
      = ((((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false])
          ++ List.replicate (2 * s) true).length from by
      simp
      try omega,
    show ((((flat2 (List.replicate j false) ++ [true, false])
        ++ flat2 (List.replicate k true)) ++ [false, false]))
        ++ (List.replicate (2 * s) true
          ++ (false :: (false :: (List.replicate z false ++ rest))))
      = (((((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false]))
          ++ List.replicate (2 * s) true)
          ++ false :: (false :: (List.replicate z false ++ rest)) from by simp,
    step_C_F (getD_at _ false _), writeAt_boundary,
    show ((((((flat2 (List.replicate j false) ++ [true, false])
        ++ flat2 (List.replicate k true)) ++ [false, false]))
        ++ List.replicate (2 * s) true))
        ++ true :: (false :: (List.replicate z false ++ rest))
      = (((((((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false]))
          ++ List.replicate (2 * s) true)) ++ [true])
          ++ false :: (List.replicate z false ++ rest) from by simp,
    show ((((((flat2 (List.replicate j false) ++ [true, false])
        ++ flat2 (List.replicate k true)) ++ [false, false]))
        ++ List.replicate (2 * s) true)).length + 1
      = (((((((flat2 (List.replicate j false) ++ [true, false])
          ++ flat2 (List.replicate k true)) ++ [false, false]))
          ++ List.replicate (2 * s) true)) ++ [true]).length from by simp; try omega,
    step_D, writeAt_boundary]
  have hmerge : List.replicate (2 * s) true ++ [true] ++ (true :: (List.replicate z false ++ rest))
      = List.replicate (2 * (s + 1)) true ++ (List.replicate z false ++ rest) := by
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 from by omega]
    have h1 : List.replicate (2 * s + 1 + 1) true
        = List.replicate (2 * s + 1) true ++ [true] := by
      rw [List.replicate_succ']
    have h2 : List.replicate (2 * s + 1) true
        = List.replicate (2 * s) true ++ [true] := by
      rw [List.replicate_succ']
    rw [h1, h2]
    simp
  rw [show (⟨(0, ans), 0, dupTape (j + 1) k (s + 1) z rest⟩ : Cfg dupMachine)
      = ⟨(0, ans), 0, ((flat2 (List.replicate j false) ++ [true, false])
          ++ (flat2 (List.replicate k true)
            ++ false :: false :: (List.replicate (2 * (s + 1)) true
              ++ (List.replicate z false ++ rest))))⟩ from by
      simp only [dupTape]
      have hj1 : flat2 (List.replicate (j + 1) false)
          = flat2 (List.replicate j false) ++ [true, false] := by
        have := List.replicate_succ' (n := j) (a := false)
        rw [this, flat2_append]
        rfl
      rw [hj1, ← flat2_replicate_true]
      try simp]
  simp [List.append_assoc, hmerge]

/-- **The copy phase**: all `k` live source units duplicated. -/
theorem dupPhase : ∀ (k j s z : ℕ) (rest : List Bool) (ans : Bool),
    ∃ t, t ≤ (k + 1) * (2 * (j + k) + 2 * (s + k) + 12) ∧
      run dupMachine t ⟨(0, ans), 0, dupTape j k s (z + 2 * k) rest⟩
        = ⟨(0, ans), 0, dupTape (j + k) 0 (s + k) z rest⟩ := by
  intro k
  induction k with
  | zero =>
    intro j s z rest ans
    exact ⟨0, by omega, by simp⟩
  | succ k ih =>
    intro j s z rest ans
    obtain ⟨t₁, ht₁, hr₁⟩ := dupRound j k s (z + 2 * k) rest ans
    obtain ⟨t₂, ht₂, hr₂⟩ := ih (j + 1) (s + 1) z rest ans
    refine ⟨t₁ + t₂, by
      have hmono : (k + 1) * (2 * (j + 1 + k) + 2 * (s + 1 + k) + 12)
          ≤ (k + 1) * (2 * (j + (k + 1)) + 2 * (s + (k + 1)) + 12) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : (k + 1 + 1) * (2 * (j + (k + 1)) + 2 * (s + (k + 1)) + 12)
          = (k + 1) * (2 * (j + (k + 1)) + 2 * (s + (k + 1)) + 12)
            + (2 * (j + (k + 1)) + 2 * (s + (k + 1)) + 12) := by ring
      omega, ?_⟩
    rw [run_add,
      show z + 2 * (k + 1) = z + 2 * k + 2 from by omega,
      hr₁, hr₂,
      show j + 1 + k = j + (k + 1) from by omega,
      show s + 1 + k = s + (k + 1) from by omega]

/-- **The duplicator**: source copied as fresh doubled units and healed. -/
theorem dupM_run (a z : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ (a + 1) * (4 * a + 12) + 4 * a + 3 ∧
      run dupMachine t ⟨(0, ans), 0, dupTape 0 a 0 (z + 2 * a) rest⟩
        = ⟨(6, ans), 2 * a, dupTape 0 a a z rest⟩ := by
  obtain ⟨t₁, ht₁, hr₁⟩ := dupPhase a 0 0 z rest ans
  refine ⟨t₁ + (2 * a + (1 + (2 * a + 1))), by
    have hmono : (a + 1) * (2 * (0 + a) + 2 * (0 + a) + 12)
        ≤ (a + 1) * (4 * a + 12) := Nat.mul_le_mul_left _ (by omega)
    omega, ?_⟩
  have hwA := walkA a []
    (false :: false :: (flat2 (List.replicate a true)
      ++ (List.replicate z false ++ rest))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwA
  have hwH := walkHeal a []
    (false :: false :: (flat2 (List.replicate a true)
      ++ (List.replicate z false ++ rest))) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hwH
  rw [run_add, hr₁,
    show (⟨(0, ans), 0, dupTape (0 + a) 0 (0 + a) z rest⟩ : Cfg dupMachine)
      = ⟨(0, ans), 0, flat2 (List.replicate a false)
          ++ (false :: false :: (flat2 (List.replicate a true)
            ++ (List.replicate z false ++ rest)))⟩ from by
      simp [dupTape, flat2],
    run_add, hwA, run_add, run_one,
    show (2 * a : ℕ) = (flat2 (List.replicate a false)).length from by
      simp [DIndexMachine.flat2_length],
    step_A0_F (getD_at _ false _),
    show ((flat2 (List.replicate a false)).length : ℕ) = 2 * a from by
      simp [DIndexMachine.flat2_length],
    run_add, hwH, run_one,
    show (2 * a : ℕ) = (flat2 (List.replicate a true)).length from by
      simp [DIndexMachine.flat2_length],
    step_HH0_F (getD_at _ false _)]
  simp [dupTape, flat2, DIndexMachine.flat2_length]

end PallLean.Paper93.DeepMath.PathB.UnaryDupMachine
