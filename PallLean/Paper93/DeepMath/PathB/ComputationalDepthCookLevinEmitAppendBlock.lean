import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterCopy

/-!
# Cook–Levin M2 emitter, E3 (i) — the output-append machine (fixed blocks into the doubled output)

First brick of E3 (`SCOPE_EMITTER.md` §3): the **append discipline** of §2 made real.  The emitter's output
region is kept in the M1 doubled form during construction — the output bits `out` are stored as
`encodeD out` (each bit `b` as the equal pair `bb`, closed by the detectable `01` terminator) — so the end of
the grown output is always the first *differing* pair, exactly the `scanMachine` boundary test.  (A raw output
region would be un-navigable: raw encodings contain `00` pairs, indistinguishable from the blank end.)

`appendMachine bits` is a machine family, one machine per **fixed block** `bits` (a hard-wired ROM — its
finite control is `Fin 7 × Fin (|bits|+1) × Bool`, the block index living in the finite state).  It scans
pairs to the output terminator, then splices the block in `4` steps per bit: overwrite the `01` terminator
with the doubled bit, re-append a fresh `01`, and step back onto it for the next bit.  Proved:

* the structural snoc lemmas (`encodeD_snoc`, `writes_snoc`): the four writes at the terminator turn
  `PRE ++ encodeD out` into exactly `PRE ++ encodeD (out ++ [b])`;
* the scan and write run-invariants, **position-generic** (arbitrary prefix `PRE` with `|PRE| = q`) and
  **reset-free** — the form E4's master loop can lift anywhere on the work tape;
* **the top theorem** (`append_run`/`append_halted`): from the read phase at the output region's start, the
  machine halts by itself after exactly `2·|out| + 2 + 4·|bits|` steps with tape **exactly**
  `PRE ++ encodeD (out ++ bits)` — a linear-clock fixed-block append.

Every template's *fixed skeleton* (literal-count blocks, tag blocks, sign bits) is an instance of this brick;
the *spliced counter blocks* (`encodeNat t` for a live counter `t`) are the next E3 brick.  The five
clause-shape bit-layouts these blocks assemble into are in `...EmitTemplates` (pure).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy

/-! ## Structural lemmas: snoc on the doubled output -/

/-- `take` one further, in `getD` form. -/
theorem take_snoc_getD {α : Type} (l : List α) (d : α) (j : ℕ) (h : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

/-- Snoc under the doubled encoding: overwrite the `01` terminator with the doubled bit, then a fresh
terminator. -/
theorem encodeD_snoc (out : List Bool) (b : Bool) :
    encodeD (out ++ [b])
      = ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b ++ [false, true] := by
  induction out with
  | nil => rfl
  | cons c out ih =>
    show c :: c :: encodeD (out ++ [b])
      = ((c :: c :: encodeD out).set (2 * (c :: out).length) b).set
          (2 * (c :: out).length + 1) b ++ [false, true]
    rw [ih]
    simp only [List.length_cons, show 2 * (out.length + 1) = 2 * out.length + 1 + 1 from by ring,
      List.set_cons_succ, List.cons_append]

/-- The four terminator writes are exactly the doubled snoc (past an arbitrary prefix). -/
theorem writes_snoc (PRE out : List Bool) (q : ℕ) (hq : PRE.length = q) (b : Bool) :
    writeAt (writeAt (writeAt (writeAt (PRE ++ encodeD out) (q + 2 * out.length) b)
        (q + 2 * out.length + 1) b) (q + 2 * out.length + 2) false) (q + 2 * out.length + 3) true
      = PRE ++ encodeD (out ++ [b]) := by
  -- write 1: terminator low cell
  have e1 : writeAt (PRE ++ encodeD out) (q + 2 * out.length) b
      = PRE ++ (encodeD out).set (2 * out.length) b := by
    rw [writeAt_of_lt b (by rw [List.length_append, encodeD_length, hq]; omega)]
    exact set_append_left_length' PRE (encodeD out) hq (2 * out.length) b
  -- write 2: terminator high cell
  have e2 : writeAt (PRE ++ (encodeD out).set (2 * out.length) b) (q + 2 * out.length + 1) b
      = PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b := by
    rw [writeAt_of_lt b (by
        rw [List.length_append, List.length_set, encodeD_length, hq]; omega),
      show q + 2 * out.length + 1 = q + (2 * out.length + 1) from by omega]
    exact set_append_left_length' PRE _ hq (2 * out.length + 1) b
  -- write 3: fresh terminator low cell, appended
  have hlen2 : (PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b).length
      = q + 2 * out.length + 2 := by
    rw [List.length_append, List.length_set, List.length_set, encodeD_length, hq]; omega
  have e3 : writeAt (PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b)
        (q + 2 * out.length + 2) false
      = (PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b) ++ [false] := by
    rw [← hlen2, writeAt_append_end]
  -- write 4: fresh terminator high cell, appended
  have hlen3 : ((PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b)
      ++ [false]).length = q + 2 * out.length + 3 := by
    rw [List.length_append, hlen2]; rfl
  have e4 : writeAt ((PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b)
        ++ [false]) (q + 2 * out.length + 3) true
      = ((PRE ++ ((encodeD out).set (2 * out.length) b).set (2 * out.length + 1) b)
          ++ [false]) ++ [true] := by
    rw [← hlen3, writeAt_append_end]
  rw [e1, e2, e3, e4, encodeD_snoc]
  simp [List.append_assoc]

/-! ## Lifted `getD` facts (the output region past an arbitrary prefix) -/

theorem preD_data_eq (PRE out : List Bool) (q i : ℕ) (hq : PRE.length = q) (h : i < out.length) :
    (PRE ++ encodeD out).getD (q + 2 * i) false
      = (PRE ++ encodeD out).getD (q + 2 * i + 1) false := by
  rw [getD_append_left_length' _ _ hq,
    show q + 2 * i + 1 = q + (2 * i + 1) from by omega, getD_append_left_length' _ _ hq]
  exact encodeD_data_eq out i h

theorem preD_mark_lo (PRE out : List Bool) (q : ℕ) (hq : PRE.length = q) :
    (PRE ++ encodeD out).getD (q + 2 * out.length) false = false := by
  rw [getD_append_left_length' _ _ hq]
  exact encodeD_mark_lo out

theorem preD_mark_hi (PRE out : List Bool) (q : ℕ) (hq : PRE.length = q) :
    (PRE ++ encodeD out).getD (q + 2 * out.length + 1) false = true := by
  rw [show q + 2 * out.length + 1 = q + (2 * out.length + 1) from by omega,
    getD_append_left_length' _ _ hq]
  exact encodeD_mark_hi out

/-! ## The append machine

Control: `Fin 7 × Fin (|bits|+1) × Bool` — phase, block index (the hard-wired ROM address), stored low cell.
Phases: `0/1` scan pairs to the differing `01` terminator (equal ⇒ continue, differ ⇒ back up to its low
cell), `2/3` overwrite the terminator with the doubled current bit, `4/5` append a fresh `01` terminator —
phase `5` steps back onto it and advances the index if bits remain, else halts into `6`. -/

def appendMachine (bits : List Bool) : Machine where
  State := Fin 7 × Fin (bits.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 6)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if b = s.2.2 then ((0, s.2.1, s.2.2), none, 1) else ((2, s.2.1, s.2.2), none, 0))
    else if s.1 = 2 then ((3, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 3 then ((4, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 4 then ((5, s.2.1, s.2.2), some false, 1)
    else if s.1 = 5 then
      (if h : s.2.1.val + 1 < bits.length then
        ((2, ⟨s.2.1.val + 1, by omega⟩, s.2.2), some true, 0)
       else ((6, s.2.1, s.2.2), some true, 2))
    else ((6, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

/-! ### Step lemmas -/

/-- Scan, low cell: read, store, advance. -/
theorem step_a0 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (appendMachine bits) ⟨(0, idx, s), p, T⟩ = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, appendMachine, moveHead]; rfl

/-- Scan, high cell equal (a doubled data pair): continue. -/
theorem step_a1_eq {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = s) :
    step (appendMachine bits) ⟨(1, idx, s), p, T⟩ = ⟨(0, idx, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, appendMachine, moveHead, h]

/-- Scan, high cell differs (the `01` terminator): back up to its low cell, start writing. -/
theorem step_a1_ne {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false ≠ s) :
    step (appendMachine bits) ⟨(1, idx, s), p, T⟩ = ⟨(2, idx, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, appendMachine, moveHead, h]

/-- Write the doubled current bit's low cell over the terminator's low cell. -/
theorem step_a2 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (appendMachine bits) ⟨(2, idx, s), p, T⟩
      = ⟨(3, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, appendMachine, moveHead]; rfl

/-- Write the doubled current bit's high cell. -/
theorem step_a3 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (appendMachine bits) ⟨(3, idx, s), p, T⟩
      = ⟨(4, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, appendMachine, moveHead]; rfl

/-- Write the fresh terminator's low cell (appended at the tape end). -/
theorem step_a4 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (appendMachine bits) ⟨(4, idx, s), p, T⟩ = ⟨(5, idx, s), p + 1, writeAt T p false⟩ := by
  simp only [step, appendMachine, moveHead]; rfl

/-- Write the fresh terminator's high cell; more bits remain ⇒ step back onto the terminator's low cell with
the index advanced. -/
theorem step_a5_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    step (appendMachine bits) ⟨(5, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, s), p - 1, writeAt T p true⟩ := by
  simp [step, appendMachine, moveHead, h]

/-- Write the fresh terminator's high cell; the block is exhausted ⇒ halt. -/
theorem step_a5_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    step (appendMachine bits) ⟨(5, idx, s), p, T⟩ = ⟨(6, idx, s), p, writeAt T p true⟩ := by
  simp [step, appendMachine, moveHead, h]

/-! ### The scan run-invariant -/

/-- The stored low cell after `m` scanned pairs (tracked exactly, as in the M1 `scanMachine`). -/
def storedD (T : List Bool) (q : ℕ) (s : Bool) : ℕ → Bool
  | 0 => s
  | m + 1 => T.getD (q + 2 * m) false

/-- Two steps over an equal (doubled data) pair. -/
theorem run_two_scan {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = T.getD (p + 1) false) :
    run (appendMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_a0, step_a1_eq h.symm]

/-- **Scan invariant.**  Over `m` equal pairs from position `q`, the machine advances `2m` steps in the read
phase, index untouched. -/
theorem run_scan (bits : List Bool) (T : List Bool) (q : ℕ) (idx : Fin (bits.length + 1))
    (s : Bool) (m : ℕ)
    (h : ∀ i, i < m → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (appendMachine bits) (2 * m) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, storedD T q s m), q + 2 * m, T⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_scan (h m (by omega))]
    rfl

/-- Detect the `01` terminator: two steps land on its low cell in the write phase, storing its (`false`) low
cell. -/
theorem run_two_detect {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (appendMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(2, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_a0, h1, step_a1_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

/-! ### The per-bit write cycle -/

/-- One mid-block bit: four steps overwrite the terminator with the doubled bit, re-append a fresh terminator,
and land back on its low cell with the index advanced. -/
theorem run_four_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    run (appendMachine bits) 4 ⟨(2, idx, s), p, T⟩
      = ⟨(2, ⟨idx.val + 1, by omega⟩, s), p + 2,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_a2, step_a3, step_a4,
    step_a5_mid h, show p + 3 - 1 = p + 2 from by omega]

/-- The last bit: four steps as above, halting on the fresh terminator's high cell. -/
theorem run_four_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    run (appendMachine bits) 4 ⟨(2, idx, s), p, T⟩
      = ⟨(6, idx, s), p + 3,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_a2, step_a3, step_a4,
    step_a5_last h]

/-! ### The block induction -/

/-- **Write-cycle invariant.**  With `d` bits left to splice (block position `j`, `j + d = |bits|`), `4d`
steps append them all: the tape advances from `out ++ bits.take j` to `out ++ bits`, halting on the final
terminator's high cell. -/
theorem run_write_all (bits PRE out : List Bool) (q : ℕ) (hq : PRE.length = q) (s : Bool) :
    ∀ d j, (hjd : j + d = bits.length) → 0 < d →
      run (appendMachine bits) (4 * d)
        ⟨(2, ⟨j, by omega⟩, s), q + 2 * (out.length + j), PRE ++ encodeD (out ++ bits.take j)⟩
      = ⟨(6, ⟨bits.length - 1, by omega⟩, s), q + 2 * (out.length + bits.length) + 1,
          PRE ++ encodeD (out ++ bits)⟩ := by
  intro d
  induction d with
  | zero => intro j hjd hd; omega
  | succ d ih =>
    intro j hjd hd
    -- the snoc this bit performs
    have hsn := writes_snoc PRE (out ++ bits.take j) q hq (bits.getD j false)
    rw [show (out ++ bits.take j).length = out.length + j from by
        rw [List.length_append, List.length_take]; omega] at hsn
    have htake : (out ++ bits.take j) ++ [bits.getD j false] = out ++ bits.take (j + 1) := by
      rw [List.append_assoc, ← take_snoc_getD bits false j (by omega)]
    rw [htake] at hsn
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · -- last bit: `j + 1 = |bits|`, so `take (j+1) = bits`
      subst hd0
      have hj : j = bits.length - 1 := by omega
      subst hj
      have hlast : ¬(bits.length - 1 + 1 < bits.length) := by omega
      rw [show 4 * (0 + 1) = 4 from rfl,
        run_four_last (s := s) hlast, hsn,
        show bits.take (bits.length - 1 + 1) = bits from by
          rw [show bits.length - 1 + 1 = bits.length from by omega, List.take_length],
        show q + 2 * (out.length + (bits.length - 1)) + 3
            = q + 2 * (out.length + bits.length) + 1 from by omega]
    · -- mid bit: recurse at `j + 1`
      have hmid : j + 1 < bits.length := by omega
      rw [show 4 * (d + 1) = 4 + 4 * d from by ring, run_add,
        run_four_mid (idx := ⟨j, by omega⟩) (s := s) hmid, hsn,
        show q + 2 * (out.length + j) + 2 = q + 2 * (out.length + (j + 1)) from by omega]
      exact ih (j + 1) (by omega) hd0

/-! ## The top theorem: a self-terminating fixed-block append -/

/-- **The append runs to completion.**  From the read phase at the output region's start (arbitrary prefix
`PRE` of length `q`, any entry stored bit), after exactly `2·|out| + 2 + 4·|bits|` steps the machine halts
with tape **exactly** `PRE ++ encodeD (out ++ bits)` — the fixed block spliced into the doubled output, all
other regions untouched. -/
theorem append_run (bits PRE out : List Bool) (q : ℕ) (hq : PRE.length = q)
    (hbits : bits ≠ []) (s : Bool) :
    run (appendMachine bits) (2 * out.length + 2 + 4 * bits.length)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), q, PRE ++ encodeD out⟩
      = ⟨(6, ⟨bits.length - 1, by omega⟩, false),
          q + 2 * (out.length + bits.length) + 1, PRE ++ encodeD (out ++ bits)⟩ := by
  have hk : 0 < bits.length := List.length_pos_iff.mpr hbits
  have hall := run_write_all bits PRE out q hq false bits.length 0 (by omega) hk
  simp only [List.take_zero, List.append_nil, Nat.add_zero] at hall
  rw [show 2 * out.length + 2 + 4 * bits.length
      = 2 * out.length + (2 + 4 * bits.length) from by omega, run_add,
    run_scan bits _ q _ s out.length
      (fun i hi => preD_data_eq PRE out q i hq hi),
    run_add,
    run_two_detect (preD_mark_lo PRE out q hq) (preD_mark_hi PRE out q hq), hall]

/-- The machine **halts by itself** at its clock. -/
theorem append_halted (bits PRE out : List Bool) (q : ℕ) (hq : PRE.length = q)
    (hbits : bits ≠ []) (s : Bool) :
    (appendMachine bits).halt
      (run (appendMachine bits) (2 * out.length + 2 + 4 * bits.length)
        ⟨(0, ⟨0, Nat.succ_pos _⟩, s), q, PRE ++ encodeD out⟩).st = true := by
  rw [append_run bits PRE out q hq hbits s]; rfl

/-- The standalone form: from the forced initializer on a bare doubled output. -/
theorem append_run_init (bits out : List Bool) (hbits : bits ≠ []) :
    run (appendMachine bits) (2 * out.length + 2 + 4 * bits.length)
      (init (appendMachine bits) (encodeD out))
      = ⟨(6, ⟨bits.length - 1, by omega⟩, false),
          2 * (out.length + bits.length) + 1, encodeD (out ++ bits)⟩ := by
  have h := append_run bits [] out 0 rfl hbits false
  simpa using h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
