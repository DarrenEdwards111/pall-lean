import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnaryCmpMachine

/-!
# The heal adapter

The sub-arc's primitives *consume* their operands, marking each live unit `[T,T] ↦ [T,F]`;
the marks preserve the count.  To reuse an operand in a later operation — e.g. an assembly
arm reusing `p` after the compare marked it — the marked block must be **healed** back to
live.  `healMachine` is that standalone adapter: a 3-state sweep flipping `[T,F] ↦ [T,T]`
until the block terminator.

`healM_run` (well-formed): `[T,F]^k [F] rest ↦ [T,T]^k [F] rest`, halting at the terminator
in `2k+1` steps.  The walk (`healWalk`) is the mutating growing-prefix pattern; the machine
is `Transduces`-free (pipeline-internal), specified by its exact run lemma.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryHealMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (flat2 getD_at getD_beyond
  writeAt_boundary run_one run_two)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- States: `0` scan a unit's first cell (halt at the terminator), `1` heal its mark cell,
`2` halt. -/
def healMachine : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((2, s.2), none, 2))
    else if s.1 = 1 then ((0, s.2), some true, 1)
    else ((2, s.2), none, 2)
  accept := fun s => s.2

theorem step_scan_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step healMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, healMachine, h, moveHead]; rfl

theorem step_scan_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step healMachine ⟨(0, ans), p, x⟩ = ⟨(2, ans), p, x⟩ := by
  simp only [step, healMachine, h, moveHead]; rfl

theorem step_heal {ans : Bool} {p : ℕ} {x : List Bool} :
    step healMachine ⟨(1, ans), p, x⟩ = ⟨(0, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, healMachine, moveHead]; rfl

/-- **The heal sweep**: over `k` marked units, flipping each to live. -/
theorem healWalk (k : ℕ) : ∀ (P Z : List Bool) (ans : Bool),
    run healMachine (2 * k)
      ⟨(0, ans), P.length, P ++ (flat2 (List.replicate k false) ++ Z)⟩
      = ⟨(0, ans), P.length + 2 * k, P ++ (flat2 (List.replicate k true) ++ Z)⟩ := by
  induction k with
  | zero => intro P Z ans; simp [flat2, run_zero]
  | succ k ih =>
    intro P Z ans
    show run healMachine (2 * (k + 1))
        ⟨(0, ans), P.length, P ++ (true :: false :: (flat2 (List.replicate k false) ++ Z))⟩
      = ⟨(0, ans), P.length + 2 * (k + 1),
          P ++ (flat2 (List.replicate (k + 1) true) ++ Z)⟩
    rw [show P.length + 2 * (k + 1) = (P ++ [true, true]).length + 2 * k from by
      simp; omega,
      show flat2 (List.replicate (k + 1) true)
        = true :: true :: flat2 (List.replicate k true) from by
        rw [List.replicate_succ]; rfl]
    rw [show 2 * (k + 1) = 2 + 2 * k from by omega, run_add, run_two,
      step_scan_T (getD_at P true _),
      show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ (true :: false :: (flat2 (List.replicate k false) ++ Z))
        = (P ++ [true]) ++ false :: (flat2 (List.replicate k false) ++ Z) from by simp,
      step_heal, writeAt_boundary,
      show (P ++ [true]).length + 1 = (P ++ [true, true]).length from by simp,
      show (P ++ [true]) ++ true :: (flat2 (List.replicate k false) ++ Z)
        = (P ++ [true, true]) ++ (flat2 (List.replicate k false) ++ Z) from by simp,
      ih (P ++ [true, true]) Z ans]
    simp [List.append_assoc]

/-- **The heal machine** heals a marked block back to live, halting at the terminator. -/
theorem healM_run (k : ℕ) (rest : List Bool) (ans : Bool) :
    ∃ t, t ≤ 2 * k + 1 ∧
      run healMachine t ⟨(0, ans), 0, flat2 (List.replicate k false) ++ (false :: rest)⟩
        = ⟨(2, ans), 2 * k, flat2 (List.replicate k true) ++ (false :: rest)⟩ := by
  refine ⟨2 * k + 1, by omega, ?_⟩
  have hw := healWalk k [] (false :: rest) ans
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at hw
  rw [run_add, hw, run_one,
    show (2 * k : ℕ) = (flat2 (List.replicate k true)).length from by
      simp [DIndexMachine.flat2_length],
    step_scan_F (getD_at _ false _)]

/-- The heal machine halts at state `2` (so it composes). -/
theorem heal_halt (ans : Bool) : healMachine.halt ((2 : Fin 3), ans) = true := rfl

end PallLean.Paper93.DeepMath.PathB.UnaryHealMachine
