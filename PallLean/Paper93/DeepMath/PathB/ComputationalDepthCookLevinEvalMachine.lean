import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Cook–Levin M1 — a concrete Boolean-evaluator `ComposableMachine` in the faithful P

Per `SCOPE_COOKLEVIN.md`, sub-mountain M1 is: a concrete evaluator machine so a SAT verifier is in
`ComposableMachine.InP`.  The faithful low-level model has a real subtlety — the tape has **no end-of-input
marker** (positions past the input read `false` by `getD`), and `Decides` requires the machine to genuinely
**halt**.  So a machine must self-delimit and halt on the false-padding.

This file builds the first genuine non-constant language in `ComposableMachine.InP` (and the *conjunction* backbone
of a CNF evaluator): the machine scans self-delimiting `(flag, value)` pairs and computes the **AND** of the
values, halting as soon as it reads a `false` flag (which the padding supplies).  `encode bs` = `bs` as such pairs;
`satAnd (encode bs) = bs.all id` (`satAnd_encode`), and `InP satAnd` (`satAnd_inP`).

This is not full CNF (no clause-`OR` nesting, no variable→value lookup — the random-access piece scoped in
`SCOPE_COOKLEVIN.md`).  It is the honest first climb of M1: a real halting poly-time machine, proved correct.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- The evaluator's control: `State = Fin 3 × Bool`, phase `0`=read-flag, `1`=read-value, `2`=halted, paired
with the running AND accumulator. -/
def evalMachine : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, true)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then
      (if b then ((1, s.2), none, 1) else ((2, s.2), none, 2))
    else if s.1 = 1 then
      ((0, s.2 && b), none, 1)
    else
      ((2, s.2), none, 2)
  accept := fun s => s.2

/-- Reading a `true` flag: advance to read the value. -/
theorem step_flag_true {A : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step evalMachine ⟨(0, A), p, x⟩ = ⟨(1, A), p + 1, x⟩ := by
  simp only [step, evalMachine, h, moveHead]
  rfl

/-- Reading a `false` flag (or the padding): halt with the accumulator. -/
theorem step_flag_false {A : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step evalMachine ⟨(0, A), p, x⟩ = ⟨(2, A), p, x⟩ := by
  simp only [step, evalMachine, h, moveHead]
  rfl

/-- Reading a value: fold it into the AND accumulator, advance to the next flag. -/
theorem step_val {A : Bool} {p : ℕ} {x : List Bool} :
    step evalMachine ⟨(1, A), p, x⟩ = ⟨(0, A && x.getD p false), p + 1, x⟩ := by
  simp only [step, evalMachine, moveHead]
  rfl

/-- A halted (`phase 2`) configuration is a fixed point. -/
theorem halted_phase2 {A : Bool} {c : Cfg evalMachine} (h : c.st = (2, A)) :
    evalMachine.halt c.st = true := by
  rw [h]; rfl

/-! ## Semantics and the run-invariant -/

/-- The AND of the values of the first `j` `(flag,value)` pairs. -/
def prefixAnd (x : List Bool) : ℕ → Bool
  | 0 => true
  | j + 1 => prefixAnd x j && x.getD (2 * j + 1) false

/-- Reading past the input returns the `false` padding. -/
theorem getD_pad (x : List Bool) {n : ℕ} (h : x.length ≤ n) : x.getD n false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Some even position holds a `false` flag (the padding does, by position `2·|x|`). -/
theorem flagFalse_exists (x : List Bool) : ∃ j, x.getD (2 * j) false = false :=
  ⟨x.length, getD_pad x (by omega)⟩

/-- The machine's halt time index: the least pair-index whose flag is `false`. -/
def firstFalseFlag (x : List Bool) : ℕ := Nat.find (flagFalse_exists x)

/-- The decided language: AND of the values up to the first `false` flag. -/
def satAnd (x : List Bool) : Bool := prefixAnd x (firstFalseFlag x)

/-- **Run invariant.**  While every flag so far is `true`, after `2j` steps the machine is in the read-flag phase
at position `2j` with the accumulator equal to the AND of the first `j` values. -/
theorem run_two_j (x : List Bool) (j : ℕ) (hj : ∀ i < j, x.getD (2 * i) false = true) :
    run evalMachine (2 * j) (init evalMachine x) = ⟨(0, prefixAnd x j), 2 * j, x⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, x.getD (2 * i) false = true := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hflag : x.getD (2 * j) false = true := hj j (Nat.lt_succ_self j)
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e1, run_succ, run_succ, ih hj', step_flag_true hflag, step_val]
    simp only [prefixAnd]

/-- **Halt.**  After `2J+1` steps (`J` = first false flag) the machine is halted in phase `2` carrying `satAnd x`. -/
theorem run_halt (x : List Bool) :
    run evalMachine (2 * firstFalseFlag x + 1) (init evalMachine x)
      = ⟨(2, prefixAnd x (firstFalseFlag x)), 2 * firstFalseFlag x, x⟩ := by
  have hff : x.getD (2 * firstFalseFlag x) false = false := Nat.find_spec (flagFalse_exists x)
  have hmin : ∀ i < firstFalseFlag x, x.getD (2 * i) false = true := by
    intro i hi
    have := Nat.find_min (flagFalse_exists x) hi
    simpa using this
  rw [run_succ, run_two_j x (firstFalseFlag x) hmin, step_flag_false hff]

/-! ## The decision procedure and `InP` membership -/

/-- **The evaluator decides `satAnd` in poly time.**  Clock `2n+1` dominates the halt time `2·firstFalseFlag+1`
(as `firstFalseFlag ≤ |x|`), and `run_stable` freezes the answer. -/
theorem satAnd_decides : Decides evalMachine satAnd (fun n => 2 * n + 1) := by
  intro x
  have hJle : firstFalseFlag x ≤ x.length :=
    Nat.find_le (getD_pad x (by omega))
  have hhalt : run evalMachine (2 * firstFalseFlag x + 1) (init evalMachine x)
      = ⟨(2, prefixAnd x (firstFalseFlag x)), 2 * firstFalseFlag x, x⟩ := run_halt x
  have hst : evalMachine.halt (run evalMachine (2 * firstFalseFlag x + 1) (init evalMachine x)).st = true := by
    rw [hhalt]; rfl
  have hle : 2 * firstFalseFlag x + 1 ≤ 2 * x.length + 1 := by omega
  have hstable : run evalMachine (2 * x.length + 1) (init evalMachine x)
      = run evalMachine (2 * firstFalseFlag x + 1) (init evalMachine x) :=
    run_stable evalMachine x hle hst
  refine ⟨?_, ?_⟩
  · show evalMachine.halt (run evalMachine (2 * x.length + 1) (init evalMachine x)).st = true
    rw [hstable]; exact hst
  · show evalMachine.accept (run evalMachine (2 * x.length + 1) (init evalMachine x)).st = satAnd x
    rw [hstable, hhalt]; rfl

/-- **A genuine non-constant language in the faithful `ComposableMachine.InP`.** -/
theorem satAnd_inP : InP satAnd :=
  ⟨evalMachine, fun n => 2 * n + 1, ⟨2, 1, fun n => by simp only [pow_one]; omega⟩, satAnd_decides⟩

/-! ## Meaningfulness: on encoded input, `satAnd` computes the conjunction -/

/-- Encode a bit-list as self-delimiting `(true, bᵢ)` pairs; the padding supplies the terminating `false` flag. -/
def encode : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: encode bs

theorem encode_length (bs : List Bool) : (encode bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (true :: b :: encode bs).length = 2 * (bs.length + 1)
    rw [List.length_cons, List.length_cons, ih]; ring

/-- Even positions of an encoding carry `true` flags. -/
theorem encode_flag (bs : List Bool) (i : ℕ) (h : i < bs.length) :
    (encode bs).getD (2 * i) false = true := by
  induction bs generalizing i with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      show (true :: b :: encode bs).getD (2 * (i + 1)) false = true
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i h'

/-- Odd positions of an encoding carry the values. -/
theorem encode_val (bs : List Bool) (i : ℕ) (h : i < bs.length) :
    (encode bs).getD (2 * i + 1) false = bs.getD i false := by
  induction bs generalizing i with
  | nil => exact absurd h (by simp)
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < bs.length := by simpa using h
      show (true :: b :: encode bs).getD (2 * (i + 1) + 1) false = (b :: bs).getD (i + 1) false
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 from by ring]
      simp only [List.getD_cons_succ]
      exact ih i h'

/-- The machine's halt index on an encoding is exactly the number of pairs. -/
theorem firstFalseFlag_encode (bs : List Bool) : firstFalseFlag (encode bs) = bs.length := by
  rw [firstFalseFlag, Nat.find_eq_iff]
  refine ⟨getD_pad (encode bs) (le_of_eq (encode_length bs)), ?_⟩
  intro n hn
  rw [encode_flag bs n hn]; simp

/-- On an encoding, the accumulator is the AND of the taken values. -/
theorem prefixAnd_encode (bs : List Bool) (k : ℕ) (hk : k ≤ bs.length) :
    prefixAnd (encode bs) k = (bs.take k).all id := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk1 : k ≤ bs.length := Nat.le_of_succ_le hk
    have hklt : k < bs.length := hk
    rw [prefixAnd, ih hk1, encode_val bs k hklt, List.take_succ, List.all_append]
    congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt]

/-- **Meaningfulness.**  On a well-formed encoding, the evaluator's language is the conjunction of the bits. -/
theorem satAnd_encode (bs : List Bool) : satAnd (encode bs) = bs.all id := by
  rw [satAnd, firstFalseFlag_encode, prefixAnd_encode bs bs.length (le_refl _), List.take_length]

end PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine
