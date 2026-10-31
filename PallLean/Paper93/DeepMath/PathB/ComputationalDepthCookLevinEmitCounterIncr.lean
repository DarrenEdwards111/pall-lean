import Mathlib.Data.List.GetD
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinDoubled
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinShiftLoop

/-!
# Cook–Levin M2 emitter, E1 (i) — the unary counter and its increment machine

Second brick of the emitter sub-project (`SCOPE_EMITTER.md` §3, E1).  The emitter's work region holds unary
counters (`t`, `p`, `q`, `b`) and bounds (`B`, `P`) in the M1 doubled discipline: a counter with value `n` is
`unaryD n := encodeD (replicate n true)` — `n` doubled `11` pairs closed by the detectable `01` boundary marker
(`CookLevinDoubled`).

This file builds the **increment** operation as an actual `ComposableMachine`: scan pairs to the detectable `01`
marker (the M1 `scanMachine` discipline), overwrite the marker pair to `11`, and write a fresh `01` marker after
it — i.e. "append a `1`" to the unary counter.  Proved:

* per-phase step lemmas and the scan run-invariant (`run_scan_incr`);
* the structural write lemmas turning the four tape writes into `unaryD (n+1)` exactly
  (`writes_produce_succ`);
* **the top theorem** (`incr_run`/`incr_halted`): on tape `unaryD n`, the machine **halts by itself** at the
  detectable boundary after exactly `2n + 6` steps with tape **exactly** `unaryD (n + 1)` — a genuine
  self-terminating counter increment with a linear clock.

Scope notes, per the standing rules: the machine's spec is proved on well-formed counter tapes (`unaryD n` alone
on the tape) — the same promise form as the M1 bricks; the tape grows by one pair, so the increment is the
**final**-region operation (`SCOPE_EMITTER.md` §2 tape discipline; region interleaving is E4's concern, not
E1's).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled

/-! ## The doubled unary counter -/

/-- A unary counter of value `n` on the doubled tape: `n` doubled `11` pairs closed by the `01` marker. -/
def unaryD (n : ℕ) : List Bool := encodeD (List.replicate n true)

/-- Closed form: `2n` `true` cells then the `01` marker cells. -/
theorem unaryD_eq (n : ℕ) : unaryD n = List.replicate (2 * n) true ++ [false, true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show true :: true :: unaryD n = List.replicate (2 * (n + 1)) true ++ [false, true]
    rw [ih, show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, List.replicate_succ,
      List.replicate_succ]
    rfl

theorem unaryD_length (n : ℕ) : (unaryD n).length = 2 * n + 2 := by
  rw [unaryD, encodeD_length, List.length_replicate]

/-- Data cells read `true`. -/
theorem unaryD_getD_data (n c : ℕ) (h : c < 2 * n) : (unaryD n).getD c false = true := by
  rw [unaryD_eq, List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

/-- The marker's low cell reads `false`. -/
theorem unaryD_getD_markLo (n : ℕ) : (unaryD n).getD (2 * n) false = false := by
  rw [unaryD_eq, List.getD_append_right (h := by rw [List.length_replicate]),
    List.length_replicate, Nat.sub_self]
  rfl

/-- The marker's high cell reads `true`. -/
theorem unaryD_getD_markHi (n : ℕ) : (unaryD n).getD (2 * n + 1) false = true := by
  rw [unaryD_eq, List.getD_append_right (h := by rw [List.length_replicate]; omega),
    List.length_replicate, show 2 * n + 1 - 2 * n = 1 from by omega]
  rfl

/-! ## Structural write lemmas

`writeAt` acts as `List.set` inside the tape and as append at the tape end; these facts plus set-past-a-prefix
turn the increment's four writes into an exact tape computation. -/

/-- Setting past a prefix. -/
theorem set_append_left_length {α : Type} (l₁ l₂ : List α) (i : ℕ) (w : α) :
    (l₁ ++ l₂).set (l₁.length + i) w = l₁ ++ l₂.set i w := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show l.length + 1 + i = (l.length + i) + 1 from by omega, List.set_cons_succ, ih]

/-- Setting past a `replicate` prefix (the index form the increment's writes produce). -/
theorem set_after_replicate (k : ℕ) (c : Bool) (l : List Bool) (i : ℕ) (w : Bool) :
    (List.replicate k c ++ l).set (k + i) w = List.replicate k c ++ l.set i w := by
  have h := set_append_left_length (List.replicate k c) l i w
  rwa [List.length_replicate] at h

/-- In range, `writeAt` is `List.set`. -/
theorem writeAt_of_lt {l : List Bool} {p : ℕ} (w : Bool) (h : p < l.length) :
    writeAt l p w = l.set p w := by
  unfold writeAt
  rw [show p + 1 - l.length = 0 from by omega, List.replicate_zero, List.append_nil]

/-- At the tape end, `writeAt` appends. -/
theorem writeAt_append_end (l : List Bool) (w : Bool) :
    writeAt l l.length w = l ++ [w] := by
  unfold writeAt
  rw [show l.length + 1 - l.length = 1 from by omega, List.replicate_one]
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.cons_append, List.length_cons, List.set_cons_succ, ih]

/-! ## The increment machine

Control: `State = Fin 7 × Bool` — phases `0`=read-low, `1`=read-high (the M1 scan discipline: equal pair ⇒
continue, differing pair ⇒ the marker), then a four-write tail `2,3,4,5` (marker `01 ↦ 11`, fresh `01` appended)
into the halt phase `6`. -/

def incrMachine : Machine where
  State := Fin 7 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 6)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then (if b = s.2 then ((0, s.2), none, 1) else ((2, s.2), none, 0))
    else if s.1 = 2 then ((3, s.2), some true, 1)
    else if s.1 = 3 then ((4, s.2), some true, 1)
    else if s.1 = 4 then ((5, s.2), some false, 1)
    else if s.1 = 5 then ((6, s.2), some true, 2)
    else ((6, s.2), none, 2)
  accept := fun _ => false

/-- Read the low cell of a pair, store it, advance. -/
theorem step_readLo {s : Bool} {p : ℕ} {tape : List Bool} :
    step incrMachine ⟨(0, s), p, tape⟩ = ⟨(1, tape.getD p false), p + 1, tape⟩ := by
  simp only [step, incrMachine, moveHead]; rfl

/-- Read the high cell; it equals the stored low cell (data pair) ⇒ continue scanning. -/
theorem step_readHi_eq {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD p false = s) :
    step incrMachine ⟨(1, s), p, tape⟩ = ⟨(0, s), p + 1, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, incrMachine, moveHead, h]

/-- Read the high cell; it differs from the stored low cell (the marker) ⇒ back up to the marker's low cell. -/
theorem step_readHi_ne {s : Bool} {p : ℕ} {tape : List Bool} (h : tape.getD p false ≠ s) :
    step incrMachine ⟨(1, s), p, tape⟩ = ⟨(2, s), p - 1, tape⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, incrMachine, moveHead, h]

/-- First write: `true` over the marker's low cell. -/
theorem step_w1 {s : Bool} {p : ℕ} {tape : List Bool} :
    step incrMachine ⟨(2, s), p, tape⟩ = ⟨(3, s), p + 1, writeAt tape p true⟩ := by
  simp only [step, incrMachine, moveHead]; rfl

/-- Second write: `true` over the marker's high cell — the old marker is now a `11` data pair. -/
theorem step_w2 {s : Bool} {p : ℕ} {tape : List Bool} :
    step incrMachine ⟨(3, s), p, tape⟩ = ⟨(4, s), p + 1, writeAt tape p true⟩ := by
  simp only [step, incrMachine, moveHead]; rfl

/-- Third write: `false` — the fresh marker's low cell, appended at the tape end. -/
theorem step_w3 {s : Bool} {p : ℕ} {tape : List Bool} :
    step incrMachine ⟨(4, s), p, tape⟩ = ⟨(5, s), p + 1, writeAt tape p false⟩ := by
  simp only [step, incrMachine, moveHead]; rfl

/-- Fourth write: `true` — the fresh marker's high cell; enter the halt phase. -/
theorem step_w4 {s : Bool} {p : ℕ} {tape : List Bool} :
    step incrMachine ⟨(5, s), p, tape⟩ = ⟨(6, s), p, writeAt tape p true⟩ := by
  simp only [step, incrMachine, moveHead]; rfl

/-! ## The scan run-invariant -/

/-- Two steps over a `11` data pair: advance one pair, staying in the read-low phase, storing `true`. -/
theorem run_two_data {s : Bool} {p : ℕ} {tape : List Bool}
    (h1 : tape.getD p false = true) (h2 : tape.getD (p + 1) false = true) :
    run incrMachine 2 ⟨(0, s), p, tape⟩ = ⟨(0, true), p + 2, tape⟩ := by
  rw [run_succ, run_succ, run_zero, step_readLo, h1, step_readHi_eq h2]

/-- **Scan invariant.**  Over the counter's `11` data pairs, after `2j` steps the machine is reading a low cell
at position `2j` (entry stored bit preserved at `j = 0`, else the last data bit `true`). -/
theorem run_scan_incr (n : ℕ) (s : Bool) (j : ℕ) (hj : j ≤ n) :
    run incrMachine (2 * j) ⟨(0, s), 0, unaryD n⟩
      = ⟨(0, if j = 0 then s else true), 2 * j, unaryD n⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ n := Nat.le_of_succ_le hj
    have h1 : (unaryD n).getD (2 * j) false = true := unaryD_getD_data n (2 * j) (by omega)
    have h2 : (unaryD n).getD (2 * j + 1) false = true := unaryD_getD_data n (2 * j + 1) (by omega)
    rw [show 2 * (j + 1) = 2 * j + 2 from by ring, run_add, ih hj', run_two_data h1 h2]
    simp

/-! ## The four writes produce exactly `unaryD (n + 1)` -/

/-- The exact tape transformation of the write tail. -/
theorem writes_produce_succ (n : ℕ) :
    writeAt (writeAt (writeAt (writeAt (unaryD n) (2 * n) true) (2 * n + 1) true)
        (2 * n + 2) false) (2 * n + 3) true
      = unaryD (n + 1) := by
  -- write 1: marker low cell `false ↦ true`
  have h0 := set_after_replicate (2 * n) true [false, true] 0 true
  rw [Nat.add_zero] at h0
  have e1 : writeAt (unaryD n) (2 * n) true
      = List.replicate (2 * n) true ++ [true, true] := by
    rw [writeAt_of_lt true (by rw [unaryD_length]; omega), unaryD_eq, h0]
    rfl
  -- write 2: marker high cell `true ↦ true` (unchanged in value, exact in form)
  have e2 : writeAt (List.replicate (2 * n) true ++ [true, true]) (2 * n + 1) true
      = List.replicate (2 * n) true ++ [true, true] := by
    rw [writeAt_of_lt true (by rw [List.length_append, List.length_replicate]; simp),
      set_after_replicate]
    rfl
  -- write 3: fresh marker low cell, appended
  have e3 : writeAt (List.replicate (2 * n) true ++ [true, true]) (2 * n + 2) false
      = List.replicate (2 * n) true ++ [true, true] ++ [false] := by
    have h : (List.replicate (2 * n) true ++ [true, true]).length = 2 * n + 2 := by
      rw [List.length_append, List.length_replicate]; rfl
    rw [← h, writeAt_append_end]
  -- write 4: fresh marker high cell, appended
  have e4 : writeAt (List.replicate (2 * n) true ++ [true, true] ++ [false]) (2 * n + 3) true
      = List.replicate (2 * n) true ++ [true, true] ++ [false] ++ [true] := by
    have h : (List.replicate (2 * n) true ++ [true, true] ++ [false]).length = 2 * n + 3 := by
      rw [List.length_append, List.length_append, List.length_replicate]; rfl
    rw [← h, writeAt_append_end]
  rw [e1, e2, e3, e4, unaryD_eq, show 2 * (n + 1) = 2 * n + 1 + 1 from by ring,
    List.replicate_succ', List.replicate_succ']
  simp [List.append_assoc]

/-! ## The top theorem: a self-terminating increment in `2n + 6` steps -/

/-- **The increment runs to completion.**  From the read-low phase at position `0` on tape `unaryD n` (any entry
stored bit), after exactly `2n + 6` steps the machine is in the halt phase with tape exactly `unaryD (n + 1)`,
head parked on the fresh marker's high cell. -/
theorem incr_run' (n : ℕ) (s : Bool) :
    run incrMachine (2 * n + 6) ⟨(0, s), 0, unaryD n⟩
      = ⟨(6, false), 2 * n + 3, unaryD (n + 1)⟩ := by
  have hlo : (unaryD n).getD (2 * n) false = false := unaryD_getD_markLo n
  have hhi : (unaryD n).getD (2 * n + 1) false = true := unaryD_getD_markHi n
  rw [show 2 * n + 6 = 2 * n + 1 + 1 + 1 + 1 + 1 + 1 from by omega,
    run_succ, run_succ, run_succ, run_succ, run_succ, run_succ,
    run_scan_incr n s n (le_refl n), step_readLo, hlo,
    step_readHi_ne (by rw [hhi]; simp), show 2 * n + 1 - 1 = 2 * n from by omega,
    step_w1, step_w2, step_w3, step_w4, writes_produce_succ n]

/-- The increment from the forced initializer. -/
theorem incr_run (n : ℕ) :
    run incrMachine (2 * n + 6) (init incrMachine (unaryD n))
      = ⟨(6, false), 2 * n + 3, unaryD (n + 1)⟩ :=
  incr_run' n false

/-- The increment machine **halts by itself** at its clock. -/
theorem incr_halted (n : ℕ) :
    incrMachine.halt (run incrMachine (2 * n + 6) (init incrMachine (unaryD n))).st = true := by
  rw [incr_run]; rfl

/-- The increment's tape output is exactly the successor counter. -/
theorem incr_output (n : ℕ) :
    (run incrMachine (2 * n + 6) (init incrMachine (unaryD n))).tp = unaryD (n + 1) := by
  rw [incr_run]

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
