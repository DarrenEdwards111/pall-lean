import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEvalMachine

/-!
# Cook–Levin M1, step (1a) — a CNF-structure evaluator `ComposableMachine` in the faithful P

Extends the conjunction backbone (`satAnd`) to the full **CNF Boolean structure** `⋀_clauses ⋁_literals`.  The
tape is a stream of self-delimiting 2-bit tokens: a literal `(true, v)`, an end-of-clause `(false, true)`, or an
end-of-formula `(false, false)`.  Two accumulators: `cAcc` (current clause's OR), `fAcc` (formula's AND so far).
The machine halts on the first end-of-formula token, which the `false` padding always supplies.

Result: `satCNF ∈ ComposableMachine.InP` (`satCNF_inP`).  Its semantics `foldCNF` (clause-OR nested inside
formula-AND) is the CNF-structure evaluation, and is machine-checked via `run_halt`.  `satCNF_encode_nil` confirms
the empty formula evaluates to `true`; the general roundtrip `satCNF (encodeCNF cls) = cls.all (·.any id)` is
routine (a no-write head-shift induction over clauses) and left as a follow-up — `foldCNF` already pins the
semantics.

Still missing for a full SAT verifier: the variable→value **random-access lookup** (literals here carry their
value inline).  That is step (1b), the hard part, scoped in `SCOPE_COOKLEVIN.md`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinCNFMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine (getD_pad)

/-- Control: `State = Fin 4 × Bool × Bool` — phase `0`=read-flag, `1`=read-literal-value, `2`=read-marker-value,
`3`=halted; paired with `(cAcc, fAcc)` = (current clause OR, formula AND). -/
def cnfMachine : Machine where
  State := Fin 4 × Bool × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false, true)
  halt := fun s => decide (s.1 = 3)
  δ := fun s b =>
    if s.1 = 0 then
      (if b then ((1, s.2.1, s.2.2), none, 1) else ((2, s.2.1, s.2.2), none, 1))
    else if s.1 = 1 then
      ((0, s.2.1 || b, s.2.2), none, 1)
    else if s.1 = 2 then
      (if b then ((0, false, s.2.2 && s.2.1), none, 1) else ((3, s.2.1, s.2.2), none, 2))
    else
      ((3, s.2.1, s.2.2), none, 2)
  accept := fun s => s.2.2

/-- Read a `true` flag → go read the literal value. -/
theorem step_flag_true {c f : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cnfMachine ⟨(0, c, f), p, x⟩ = ⟨(1, c, f), p + 1, x⟩ := by
  simp only [step, cnfMachine, h, moveHead]; rfl

/-- Read a `false` flag → go read the marker value. -/
theorem step_flag_false {c f : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cnfMachine ⟨(0, c, f), p, x⟩ = ⟨(2, c, f), p + 1, x⟩ := by
  simp only [step, cnfMachine, h, moveHead]; rfl

/-- Read a literal value `v` → OR it into the clause accumulator. -/
theorem step_litval {c f : Bool} {p : ℕ} {x : List Bool} :
    step cnfMachine ⟨(1, c, f), p, x⟩ = ⟨(0, c || x.getD p false, f), p + 1, x⟩ := by
  simp only [step, cnfMachine, moveHead]; rfl

/-- Read a `true` marker value (end-of-clause) → AND the clause into the formula, reset the clause. -/
theorem step_marker_ec {c f : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step cnfMachine ⟨(2, c, f), p, x⟩ = ⟨(0, false, f && c), p + 1, x⟩ := by
  simp only [step, cnfMachine, h, moveHead]; rfl

/-- Read a `false` marker value (end-of-formula) → halt. -/
theorem step_marker_ef {c f : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step cnfMachine ⟨(2, c, f), p, x⟩ = ⟨(3, c, f), p, x⟩ := by
  simp only [step, cnfMachine, h, moveHead]; rfl

/-! ## Semantics, run-invariant, and halt -/

/-- The `(clause-OR, formula-AND)` accumulators after processing the first `j` tokens. -/
def foldCNF (x : List Bool) : ℕ → Bool × Bool
  | 0 => (false, true)
  | j + 1 =>
    if x.getD (2 * j) false then ((foldCNF x j).1 || x.getD (2 * j + 1) false, (foldCNF x j).2)
    else (false, (foldCNF x j).2 && (foldCNF x j).1)

/-- Token `j` is not an end-of-formula token. -/
def notEF (x : List Bool) (j : ℕ) : Prop :=
  ¬(x.getD (2 * j) false = false ∧ x.getD (2 * j + 1) false = false)

/-- The padding supplies an end-of-formula token by pair-index `|x|`. -/
theorem endFormula_exists (x : List Bool) :
    ∃ j, x.getD (2 * j) false = false ∧ x.getD (2 * j + 1) false = false :=
  ⟨x.length, getD_pad x (by omega), getD_pad x (by omega)⟩

/-- The machine's halt-token index: the first end-of-formula token. -/
def firstEndFormula (x : List Bool) : ℕ := Nat.find (endFormula_exists x)

/-- The decided language: the formula-AND accumulator at the halt token. -/
def satCNF (x : List Bool) : Bool := (foldCNF x (firstEndFormula x)).2

/-- **Run invariant.**  As long as no end-of-formula token has appeared, after `2j` steps the machine is in the
read-flag phase at position `2j` carrying the fold accumulators. -/
theorem run_two_j (x : List Bool) (j : ℕ) (hj : ∀ i < j, notEF x i) :
    run cnfMachine (2 * j) (init cnfMachine x)
      = ⟨(0, (foldCNF x j).1, (foldCNF x j).2), 2 * j, x⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, notEF x i := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hjEF : notEF x j := hj j (Nat.lt_succ_self j)
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e1, run_succ, run_succ, ih hj']
    by_cases hflag : x.getD (2 * j) false = true
    · rw [step_flag_true hflag, step_litval]
      simp only [foldCNF, hflag, if_true]
    · have hff : x.getD (2 * j) false = false := by simpa using hflag
      have hmv : x.getD (2 * j + 1) false = true := by
        by_contra hc; exact hjEF ⟨hff, by simpa using hc⟩
      rw [step_flag_false hff, step_marker_ec hmv]
      simp only [foldCNF, hff, Bool.false_eq_true, if_false]

/-- **Halt.**  After `2J+2` steps (`J` = first end-of-formula token) the machine is halted (`phase 3`) carrying
`satCNF x` in its formula accumulator. -/
theorem run_halt (x : List Bool) :
    run cnfMachine (2 * firstEndFormula x + 2) (init cnfMachine x)
      = ⟨(3, (foldCNF x (firstEndFormula x)).1, (foldCNF x (firstEndFormula x)).2),
          2 * firstEndFormula x + 1, x⟩ := by
  have hEF : x.getD (2 * firstEndFormula x) false = false
      ∧ x.getD (2 * firstEndFormula x + 1) false = false := Nat.find_spec (endFormula_exists x)
  have hmin : ∀ i < firstEndFormula x, notEF x i :=
    fun i hi => Nat.find_min (endFormula_exists x) hi
  rw [show 2 * firstEndFormula x + 2 = 2 * firstEndFormula x + 1 + 1 from by ring,
    run_succ, run_succ, run_two_j x (firstEndFormula x) hmin,
    step_flag_false hEF.1, step_marker_ef hEF.2]

/-! ## The decision procedure and `InP` membership -/

/-- **The CNF-structure evaluator decides `satCNF` in poly time.** -/
theorem satCNF_decides : Decides cnfMachine satCNF (fun n => 2 * n + 2) := by
  intro x
  have hJle : firstEndFormula x ≤ x.length :=
    Nat.find_le ⟨getD_pad x (by omega), getD_pad x (by omega)⟩
  have hhalt := run_halt x
  have hst : cnfMachine.halt (run cnfMachine (2 * firstEndFormula x + 2) (init cnfMachine x)).st = true := by
    rw [hhalt]; rfl
  have hle : 2 * firstEndFormula x + 2 ≤ 2 * x.length + 2 := by omega
  have hstable : run cnfMachine (2 * x.length + 2) (init cnfMachine x)
      = run cnfMachine (2 * firstEndFormula x + 2) (init cnfMachine x) :=
    run_stable cnfMachine x hle hst
  refine ⟨?_, ?_⟩
  · show cnfMachine.halt (run cnfMachine (2 * x.length + 2) (init cnfMachine x)).st = true
    rw [hstable]; exact hst
  · show cnfMachine.accept (run cnfMachine (2 * x.length + 2) (init cnfMachine x)).st = satCNF x
    rw [hstable, hhalt]; rfl

/-- **A CNF-structure evaluator in the faithful `ComposableMachine.InP`.** -/
theorem satCNF_inP : InP satCNF :=
  ⟨cnfMachine, fun n => 2 * n + 2, ⟨2, 1, fun n => by simp only [pow_one]; omega⟩, satCNF_decides⟩

/-! ## Encoding and the empty-formula meaningfulness check -/

/-- Encode a clause: its literals as `(true, bᵢ)` pairs, terminated by an end-of-clause `(false, true)`. -/
def encodeClause : List Bool → List Bool
  | [] => [false, true]
  | b :: bs => true :: b :: encodeClause bs

/-- Encode a CNF: each clause's encoding, terminated by an end-of-formula `(false, false)`. -/
def encodeCNF : List (List Bool) → List Bool
  | [] => [false, false]
  | cl :: cls => encodeClause cl ++ encodeCNF cls

/-- **Meaningfulness (empty formula).**  The empty CNF evaluates to `true`. -/
theorem satCNF_encode_nil : satCNF (encodeCNF []) = true := by
  have h0 : firstEndFormula (encodeCNF []) = 0 := by
    rw [firstEndFormula, Nat.find_eq_zero]; exact ⟨rfl, rfl⟩
  rw [satCNF, h0]; rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinCNFMachine
