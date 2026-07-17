import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSchemaComplete

/-!
# S3a: the space-kill frame and the odometer — opening the brute-force decider arc

**Step 5, brick S3a.**  The first candidate audit targets the *space measure*
`rowMax` (maximal trace-row length).  Mathematically it cannot be SAT-hard — brute
force decides any NP boundary in polynomial space — but proving that in the model
requires a concrete brute-force decider machine.  This brick sets the frame and lands
the arc's first engine:

* `rowMax`, with `sizeDominated_rowMax` — the space measure is in S1's family, so it is
  generically sound by the transfer theorem; the only question is hardness.
* `SATPolySpace SATV` — **the explicit engineering fence** (true mathematics, machine
  pending): the verifier's boundary has a decider with polynomially bounded worst-case
  row length.  `rowMax_not_hard`: under the fence, `rowMax` is *not* SAT-hard — the
  first candidate kill, pinning that a contentful `μ` must see more than space.
* **The odometer** (`incrMachine`): in-place binary increment, LSB-first —
  `incr` (`[] ↦ [1]`, `0·r ↦ 1·r`, `1·r ↦ 0·incr r`) — with a full run lemma
  (`incr_walk`), totality on all inputs (the all-ones overflow *extends the tape by one
  cell*, exactly matching `incr`'s spec), and `incrMachine_transduces` at clock `n+2`.
  This is the witness-enumeration driver of the brute-force loop.

**The brute-force arc roadmap** (each in the established marking fabric): odometer
(this brick) → restoring lookup (mark, read, *unmark*) → CNF evaluator over an
enumerated assignment → loop composition (evaluate, increment, repeat; accept on first
success, reject on odometer overflow) → `SATPolySpace` discharged → `rowMax` killed
unconditionally.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceSpaceKill

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (getD_at getD_beyond writeAt_boundary
  run_one run_two)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The space measure and the kill frame -/

/-- The space measure: maximal row length of the trace. -/
def rowMax (tr : List (List Bool)) : ℕ := (tr.map List.length).foldr max 0

theorem foldr_max_le_sum : ∀ l : List ℕ, l.foldr max 0 ≤ l.sum
  | [] => Nat.le_refl 0
  | a :: l => by
    show max a (l.foldr max 0) ≤ a + l.sum
    have := foldr_max_le_sum l
    omega

/-- The space measure is size-dominated — S1's transfer theorem applies, so
`traceInv rowMax` is generically sound. -/
theorem sizeDominated_rowMax : SizeDominated rowMax := by
  intro tr
  unfold rowMax traceSize
  have := foldr_max_le_sum (tr.map List.length)
  omega

/-- **The engineering fence** (mathematically true — brute force — machine pending):
the boundary has a decider of polynomially bounded worst-case row length. -/
def SATPolySpace (SATV : NPObs) : Prop :=
  ∃ M T, Decides M (acceptBool SATV) T ∧ PolyBounded (traceInv rowMax M)

/-- **The space-kill, modulo the fence**: `rowMax` cannot be SAT-hard.  A contentful
trace measure must see more than space. -/
theorem rowMax_not_hard (SATV : NPObs) (h : SATPolySpace SATV) :
    ¬ InvHard SATV (traceInv rowMax) := by
  intro hH
  obtain ⟨M, T, hD, hPB⟩ := h
  exact hH M T hD hPB

/-! ## The odometer: in-place binary increment (LSB first) -/

/-- Binary increment, least-significant bit first; all-ones overflows into one more
cell. -/
def incr : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incr r

theorem incr_length_le (x : List Bool) : (incr x).length ≤ x.length + 1 := by
  induction x with
  | nil => exact Nat.le_refl 1
  | cons b r ih =>
    cases b
    · exact Nat.le_succ _
    · show (false :: incr r).length ≤ (true :: r).length + 1
      simp only [List.length_cons]
      omega

/-- The odometer: state `0` scans; a `1` is flipped to `0` (carry), the first `0` (or
the void — tape extension) is flipped to `1` and the machine halts. -/
def incrMachine : Machine where
  State := Fin 2 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 1)
  δ := fun s b =>
    if s.1 = 0 then
      (if b then ((0, s.2), some false, 1) else ((1, s.2), some true, 2))
    else ((1, s.2), none, 2)
  accept := fun s => s.2

theorem step_carry {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step incrMachine ⟨(0, ans), p, x⟩ = ⟨(0, ans), p + 1, writeAt x p false⟩ := by
  simp only [step, incrMachine, h, moveHead]; rfl

theorem step_flip {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step incrMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p, writeAt x p true⟩ := by
  simp only [step, incrMachine, h, moveHead]; rfl

/-- Writing one past the end extends the tape by a single cell. -/
theorem writeAt_extend (P : List Bool) (w : Bool) :
    writeAt P P.length w = P ++ [w] := by
  unfold writeAt
  have h1 : P.length + 1 - P.length = 1 := by omega
  rw [h1]
  show (P ++ [false]).set P.length w = P ++ [w]
  rw [List.set_append_right _ _ (Nat.le_refl _)]
  simp

/-- **The odometer walk**: from any position boundary, the machine realizes `incr` on
the suffix, on *every* input (the all-ones overflow extends the tape). -/
theorem incr_walk : ∀ (x P : List Bool) (ans : Bool),
    ∃ t ≤ x.length + 1, ∃ p,
      run incrMachine t ⟨(0, ans), P.length, P ++ x⟩ = ⟨(1, ans), p, P ++ incr x⟩
  | [], P, ans => by
    refine ⟨1, by omega, P.length, ?_⟩
    rw [run_one, step_flip (getD_beyond _ _ (by simp)),
      show P ++ ([] : List Bool) = P from by simp, writeAt_extend]
    rfl
  | false :: r, P, ans => by
    refine ⟨1, by omega, P.length, ?_⟩
    rw [run_one, step_flip (getD_at P false r), writeAt_boundary]
    rfl
  | true :: r, P, ans => by
    obtain ⟨t, ht, p, hrun⟩ := incr_walk r (P ++ [false]) ans
    refine ⟨1 + t, by simp only [List.length_cons]; omega, p, ?_⟩
    rw [run_add, run_one, step_carry (getD_at P true r), writeAt_boundary,
      show P ++ false :: r = (P ++ [false]) ++ r from by simp,
      show P.length + 1 = (P ++ [false]).length from by simp,
      hrun,
      show (P ++ [false]) ++ incr r = P ++ false :: incr r from by simp]
    rfl

/-- **The odometer transduces `incr`** within clock `n + 2`, on all inputs. -/
theorem incrMachine_transduces : Transduces incrMachine incr (fun n => n + 2) := by
  intro x
  obtain ⟨t, ht, p, hrun⟩ := by
    have h := incr_walk x [] false
    simpa using h
  have hrun0 : run incrMachine t (init incrMachine x) = ⟨(1, false), p, incr x⟩ := hrun
  have hhalt : incrMachine.halt (run incrMachine t (init incrMachine x)).st = true := by
    rw [hrun0]
    rfl
  have hstable : run incrMachine (x.length + 2) (init incrMachine x)
      = run incrMachine t (init incrMachine x) :=
    run_stable incrMachine x (by omega) hhalt
  constructor
  · show incrMachine.halt (run incrMachine (x.length + 2) (init incrMachine x)).st = true
    rw [hstable, hrun0]
    rfl
  · show transOut incrMachine x (x.length + 2) = incr x
    unfold transOut
    rw [hstable, hrun0]

/-- The increment is polynomial-time computable — the enumeration driver is in the
model's P. -/
theorem incr_polyComputable : PolyComputable incr :=
  ⟨incrMachine, fun n => n + 2, ⟨3, 1, fun n => by
    show n + 2 ≤ 3 * (n + 1) ^ 1
    have : (n + 1) ^ 1 = n + 1 := pow_one _
    omega⟩, incrMachine_transduces⟩

end PallLean.Paper93.DeepMath.PathB.TraceSpaceKill
