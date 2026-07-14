import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEvalMachine

/-!
# Cook–Levin M1, step (1b) — data-dependent addressing (`ComposableMachine`)

The genuinely hard part of M1 is **random access**: a literal names a variable index `v`, and the machine must
read the assignment bit at position `v` — i.e. move its head to a position *computed from the input*.  Steps
(1a)/`satAnd` only ever moved the head forward by a fixed amount per token; nothing there addressed a
data-dependent position.

This file builds the **addressing core**: `readAtUnary` seeks past a unary counter `1ᵏ` and a separator, then
reads the bit at the resulting data-dependent position `k+1`.  So the head lands where the *input* says, and the
output is the bit at that computed address.  `readOut ∈ ComposableMachine.InP` (`readAtUnary_inP`), and on a
well-formed address `1ᵏ 0 b …` it returns `b` (`readOut_encode`).

Honest scope: this addresses a position `k+1` where `k` is the unary count — a data-dependent *seek-and-read*.  A
full variable→value lookup (read assignment[`v`] for an arbitrary literal, `v` re-usable) needs the classic
**two-pointer marking** construction (mark the counter, advance the data pointer in tandem, bounce) — which writes
to the tape and runs `O(k²)` — and is the remaining mountain, scoped in `SCOPE_COOKLEVIN.md`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinLookupMachine

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEvalMachine (getD_pad)

/-- Control: `State = Fin 3 × Bool` — phase `0`=seek, `1`=read, `2`=halted; paired with the stored output bit. -/
def readAtUnary : Machine where
  State := Fin 3 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 2)
  δ := fun s b =>
    if s.1 = 0 then
      (if b then ((0, s.2), none, 1) else ((1, s.2), none, 1))
    else if s.1 = 1 then
      ((2, b), none, 2)
    else
      ((2, s.2), none, 2)
  accept := fun s => s.2

/-- Seeking over a `true` (a counter cell): advance. -/
theorem step_seek_true {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step readAtUnary ⟨(0, s), p, x⟩ = ⟨(0, s), p + 1, x⟩ := by
  simp only [step, readAtUnary, h, moveHead]; rfl

/-- Seeking hits the `false` separator: advance into the data region, switch to read. -/
theorem step_seek_false {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step readAtUnary ⟨(0, s), p, x⟩ = ⟨(1, s), p + 1, x⟩ := by
  simp only [step, readAtUnary, h, moveHead]; rfl

/-- Read the addressed bit and halt (storing it as the output). -/
theorem step_read {s : Bool} {p : ℕ} {x : List Bool} :
    step readAtUnary ⟨(1, s), p, x⟩ = ⟨(2, x.getD p false), p, x⟩ := by
  simp only [step, readAtUnary, moveHead]; rfl

/-! ## Semantics, seek-invariant, halt, and `InP` -/

/-- The padding supplies a `false` by position `|x|`. -/
theorem false_exists (x : List Bool) : ∃ j, x.getD j false = false :=
  ⟨x.length, getD_pad x (le_refl _)⟩

/-- The separator position: the first `false` (end of the unary counter). -/
def firstFalse (x : List Bool) : ℕ := Nat.find (false_exists x)

/-- The addressed output: the bit one past the separator. -/
def readOut (x : List Bool) : Bool := x.getD (firstFalse x + 1) false

/-- **Seek invariant.**  While the counter cells are `true`, after `j` steps the head is at position `j`, still
seeking. -/
theorem run_seek (x : List Bool) (j : ℕ) (hj : ∀ i < j, x.getD i false = true) :
    run readAtUnary j (init readAtUnary x) = ⟨(0, false), j, x⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : ∀ i < j, x.getD i false = true := fun i hi => hj i (Nat.lt_succ_of_lt hi)
    have hflag : x.getD j false = true := hj j (Nat.lt_succ_self j)
    rw [run_succ, ih hj', step_seek_true hflag]

/-- **Halt.**  The head lands at the data-dependent address `firstFalse+1`, reads that bit, and halts with it. -/
theorem run_halt (x : List Bool) :
    run readAtUnary (firstFalse x + 2) (init readAtUnary x)
      = ⟨(2, x.getD (firstFalse x + 1) false), firstFalse x + 1, x⟩ := by
  have hk : x.getD (firstFalse x) false = false := Nat.find_spec (false_exists x)
  have hmin : ∀ i < firstFalse x, x.getD i false = true :=
    fun i hi => by simpa using Nat.find_min (false_exists x) hi
  rw [show firstFalse x + 2 = firstFalse x + 1 + 1 from rfl, run_succ, run_succ,
    run_seek x (firstFalse x) hmin, step_seek_false hk, step_read]

/-- **The addressing machine decides `readOut` in poly time.** -/
theorem readAtUnary_decides : Decides readAtUnary readOut (fun n => n + 2) := by
  intro x
  have hkle : firstFalse x ≤ x.length := Nat.find_le (getD_pad x (le_refl _))
  have hhalt := run_halt x
  have hst : readAtUnary.halt (run readAtUnary (firstFalse x + 2) (init readAtUnary x)).st = true := by
    rw [hhalt]; rfl
  have hle : firstFalse x + 2 ≤ x.length + 2 := by omega
  have hstable : run readAtUnary (x.length + 2) (init readAtUnary x)
      = run readAtUnary (firstFalse x + 2) (init readAtUnary x) :=
    run_stable readAtUnary x hle hst
  refine ⟨?_, ?_⟩
  · show readAtUnary.halt (run readAtUnary (x.length + 2) (init readAtUnary x)).st = true
    rw [hstable]; exact hst
  · show readAtUnary.accept (run readAtUnary (x.length + 2) (init readAtUnary x)).st = readOut x
    rw [hstable, hhalt]; rfl

/-- **Data-dependent addressing in the faithful `ComposableMachine.InP`.** -/
theorem readAtUnary_inP : InP readOut :=
  ⟨readAtUnary, fun n => n + 2, ⟨2, 1, fun n => by simp only [pow_one]; omega⟩, readAtUnary_decides⟩

/-! ## Meaningfulness: on a well-formed address, the machine returns the addressed bit -/

/-- A well-formed address: unary count `k`, separator, then the addressed bit `b`, then anything. -/
def encodeAddr (k : ℕ) (b : Bool) (rest : List Bool) : List Bool :=
  List.replicate k true ++ false :: b :: rest

/-- **Meaningfulness.**  The machine reads exactly the bit at the unary-specified address. -/
theorem readOut_encode (k : ℕ) (b : Bool) (rest : List Bool) :
    readOut (encodeAddr k b rest) = b := by
  have hlen : (List.replicate k true).length = k := List.length_replicate ..
  have hlt : ∀ i < k, (encodeAddr k b rest).getD i false = true := by
    intro i hi
    rw [encodeAddr, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hlen]; exact hi), List.getElem?_replicate]
    simp [hi]
  have hk : (encodeAddr k b rest).getD k false = false := by
    rw [encodeAddr, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hlen]), hlen]
    simp
  have hff : firstFalse (encodeAddr k b rest) = k := by
    rw [firstFalse, Nat.find_eq_iff]
    exact ⟨hk, fun i hi => by rw [hlt i hi]; simp⟩
  rw [readOut, hff, encodeAddr, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [hlen]; omega), hlen]
  simp

end PallLean.Paper93.DeepMath.PathB.CookLevinLookupMachine
