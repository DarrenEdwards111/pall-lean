import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitSplice

/-!
# Cook–Levin M2 emitter, E4 (i) — the counted-loop harness (the master pattern)

First brick of E4, the nested-loop master (`SCOPE_EMITTER.md` §3, the component flagged as master-machine
scale).  Two decisions are made and locked here.

**Composition style.**  M1's master welded *already-proven* sub-machines via embeddings and per-group
simulation lemmas (`...CookLevinMasterSim`) — necessary there because the sub-machines' run-lemmas were
stated against their own `Cfg` types.  The E1/E3 bricks were built differently: their expensive content is
**machine-independent tape structure** (`cntT`/`hlT` descriptors with `getD` suites, the structural
mark/heal writes, `writes_snoc`, the `preD` output-region facts), all stated over plain lists, while the
per-machine layer (step lemmas, pair-steps, scan invariants) is hypothesis-based and mechanical.  So the E4
masters are built **fresh**, reusing every tape-level lemma verbatim and re-instantiating only the cheap
step layer — no embedding apparatus.

**Loop control.**  The loop `for k in range N` is controlled by **countdown-marking the bound counter**: the
bound `unaryD N` is consumed mark-by-mark (`10`) exactly as the splice machine consumes its source, and the
exit test is hitting the bound's `01` boundary — *no comparison machine, no copies*.  A restore pass heals
the bound afterwards, so the harness is bound-preserving and re-runnable.

`loopMachine bits` (control `Fin 13 × Fin (|bits|+1) × Bool`) runs `for k in range N: append bits`: find the
bound's next unprocessed pair and mark it; seek right across the bound's rest, its boundary, and the output's
doubled data to the output terminator; splice the fixed block there (the E3 ROM discipline, index in the
finite control); reset; when the bound is exhausted, restore it and halt.  Proved: all step/pair-step
lemmas, five scan invariants, the ROM block induction, the **round invariant** (round `k` costs exactly
`2N + 2L + 2(k·|bits|) + 4|bits| + 4` steps), the rounds induction, and **the top theorem**
(`loop_run`/`loop_halted`): on `unaryD N ++ encodeD out` the machine halts by itself at the explicit clock
`lpClock` (closed form proved, cubic bound `lpClock_le`) with tape **exactly**
`unaryD N ++ encodeD (out ++ blkRep bits N)` — `N` copies of the block emitted, the bound preserved.

The remaining E4 work instantiates this pattern: swap the ROM body for the splice/increment body (a loop
variable in a **capacity-bounded** in-place counter), nest two harnesses (`t ≤ B`, `p ≤ P`), and sequence
the seven families.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice

/-! ## The repeated block -/

/-- `k` copies of the block, in emission order. -/
def blkRep (bits : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => blkRep bits k ++ bits

theorem blkRep_length (bits : List Bool) (k : ℕ) :
    (blkRep bits k).length = k * bits.length := by
  induction k with
  | zero => simp [blkRep]
  | succ k ih => simp only [blkRep, List.length_append, ih]; ring

/-! ## The counted-loop machine

Control: `Fin 13 × Fin (|bits|+1) × Bool` — phase, ROM index, stored low cell.  Phases: `0/1` find the
bound's next unprocessed pair (skip `10`, mark `11` ⇒ emit, boundary `01` ⇒ restore-and-halt), `2/3` seek
across the bound's rest to its boundary, `4/5` seek across the output's doubled data to its terminator,
`6–9` the ROM block splice (four steps per bit, index advancing in the control; after the last bit, reset
into the next round), `10/11` the restore pass, `12` = halt. -/

def loopMachine (bits : List Bool) : Machine where
  State := Fin 13 × Fin (bits.length + 1) × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, ⟨0, Nat.succ_pos _⟩, false)
  halt := fun s => decide (s.1 = 12)
  δ := fun s b =>
    if s.1 = 0 then ((1, s.2.1, b), none, 1)
    else if s.1 = 1 then
      (if s.2.2 then
        (if b then ((2, ⟨0, Nat.succ_pos _⟩, s.2.2), some false, 1)
         else ((0, s.2.1, s.2.2), none, 1))
       else (if b then ((10, s.2.1, s.2.2), none, 3) else ((12, s.2.1, s.2.2), none, 2)))
    else if s.1 = 2 then ((3, s.2.1, b), none, 1)
    else if s.1 = 3 then
      (if s.2.2 then (if b then ((2, s.2.1, s.2.2), none, 1) else ((12, s.2.1, s.2.2), none, 2))
       else (if b then ((4, s.2.1, s.2.2), none, 1) else ((12, s.2.1, s.2.2), none, 2)))
    else if s.1 = 4 then ((5, s.2.1, b), none, 1)
    else if s.1 = 5 then
      (if b = s.2.2 then ((4, s.2.1, s.2.2), none, 1) else ((6, s.2.1, s.2.2), none, 0))
    else if s.1 = 6 then ((7, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 7 then ((8, s.2.1, s.2.2), some (bits.getD s.2.1.val false), 1)
    else if s.1 = 8 then ((9, s.2.1, s.2.2), some false, 1)
    else if s.1 = 9 then
      (if h : s.2.1.val + 1 < bits.length then
        ((6, ⟨s.2.1.val + 1, by omega⟩, s.2.2), some true, 0)
       else ((0, ⟨0, Nat.succ_pos _⟩, s.2.2), some true, 3))
    else if s.1 = 10 then ((11, s.2.1, b), none, 1)
    else if s.1 = 11 then
      (if s.2.2 then
        (if b then ((12, s.2.1, s.2.2), none, 2) else ((10, s.2.1, true), some true, 1))
       else ((12, s.2.1, s.2.2), none, 2))
    else ((s.1, s.2.1, s.2.2), none, 2)
  accept := fun _ => false

theorem init_loop (bits : List Bool) (x : List Bool) :
    init (loopMachine bits) x = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_l0 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(0, idx, s), p, T⟩ = ⟨(1, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l1_mark {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (loopMachine bits) ⟨(1, idx, true), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l1_skip {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (loopMachine bits) ⟨(1, idx, true), p, T⟩ = ⟨(0, idx, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l1_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (loopMachine bits) ⟨(1, idx, false), p, T⟩ = ⟨(10, idx, false), 0, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l2 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(2, idx, s), p, T⟩ = ⟨(3, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l3_data {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (loopMachine bits) ⟨(3, idx, true), p, T⟩ = ⟨(2, idx, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l3_cross {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = true) :
    step (loopMachine bits) ⟨(3, idx, false), p, T⟩ = ⟨(4, idx, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l4 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(4, idx, s), p, T⟩ = ⟨(5, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l5_eq {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = s) :
    step (loopMachine bits) ⟨(5, idx, s), p, T⟩ = ⟨(4, idx, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l5_ne {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false ≠ s) :
    step (loopMachine bits) ⟨(5, idx, s), p, T⟩ = ⟨(6, idx, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l6 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(6, idx, s), p, T⟩
      = ⟨(7, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l7 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(7, idx, s), p, T⟩
      = ⟨(8, idx, s), p + 1, writeAt T p (bits.getD idx.val false)⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l8 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(8, idx, s), p, T⟩ = ⟨(9, idx, s), p + 1, writeAt T p false⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l9_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    step (loopMachine bits) ⟨(9, idx, s), p, T⟩
      = ⟨(6, ⟨idx.val + 1, by omega⟩, s), p - 1, writeAt T p true⟩ := by
  simp [step, loopMachine, moveHead, h]

theorem step_l9_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    step (loopMachine bits) ⟨(9, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, writeAt T p true⟩ := by
  simp [step, loopMachine, moveHead, h]

theorem step_l10 {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(10, idx, s), p, T⟩ = ⟨(11, idx, T.getD p false), p + 1, T⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

theorem step_l11_heal {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} (h : T.getD p false = false) :
    step (loopMachine bits) ⟨(11, idx, true), p, T⟩
      = ⟨(10, idx, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, loopMachine, moveHead, h]

theorem step_l11_done {bits : List Bool} {idx : Fin (bits.length + 1)} {p : ℕ}
    {T : List Bool} :
    step (loopMachine bits) ⟨(11, idx, false), p, T⟩ = ⟨(12, idx, false), p, T⟩ := by
  simp only [step, loopMachine, moveHead]; rfl

/-! ### Pair-step lemmas -/

theorem run_two_skipF {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(0, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l0, h1, step_l1_skip h2]

theorem run_two_markF {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopMachine bits) 2 ⟨(0, idx, s), p, T⟩
      = ⟨(2, ⟨0, Nat.succ_pos _⟩, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_l0, h1, step_l1_mark h2]

theorem run_two_toRst {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopMachine bits) 2 ⟨(0, idx, s), p, T⟩ = ⟨(10, idx, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l0, h1, step_l1_done h2]

theorem run_two_seekD {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run (loopMachine bits) 2 ⟨(2, idx, s), p, T⟩ = ⟨(2, idx, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l2, h1, step_l3_data h2]

theorem run_two_crossD {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopMachine bits) 2 ⟨(2, idx, s), p, T⟩ = ⟨(4, idx, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l2, h1, step_l3_cross h2]

theorem run_two_seekO {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : T.getD p false = T.getD (p + 1) false) :
    run (loopMachine bits) 2 ⟨(4, idx, s), p, T⟩ = ⟨(4, idx, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l4, step_l5_eq h.symm]

theorem run_two_detectO {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run (loopMachine bits) 2 ⟨(4, idx, s), p, T⟩ = ⟨(6, idx, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l4, h1, step_l5_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_rom4_mid {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : idx.val + 1 < bits.length) :
    run (loopMachine bits) 4 ⟨(6, idx, s), p, T⟩
      = ⟨(6, ⟨idx.val + 1, by omega⟩, s), p + 2,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_l6, step_l7, step_l8,
    step_l9_mid h, show p + 3 - 1 = p + 2 from by omega]

theorem run_rom4_last {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h : ¬(idx.val + 1 < bits.length)) :
    run (loopMachine bits) 4 ⟨(6, idx, s), p, T⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0,
          writeAt (writeAt (writeAt (writeAt T p (bits.getD idx.val false)) (p + 1)
            (bits.getD idx.val false)) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_l6, step_l7, step_l8,
    step_l9_last h]

theorem run_two_heal {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run (loopMachine bits) 2 ⟨(10, idx, s), p, T⟩
      = ⟨(10, idx, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_l10, h1, step_l11_heal h2]

theorem run_two_done {bits : List Bool} {idx : Fin (bits.length + 1)} {s : Bool} {p : ℕ}
    {T : List Bool} (h1 : T.getD p false = false) :
    run (loopMachine bits) 2 ⟨(10, idx, s), p, T⟩ = ⟨(12, idx, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_l10, h1, step_l11_done]

/-! ### Scan run-invariants -/

theorem run_skipFs (bits : List Bool) (T : List Bool) (q k : ℕ)
    (idx : Fin (bits.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run (loopMachine bits) (2 * k) ⟨(0, idx, s), q, T⟩
      = ⟨(0, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipF hk.1 hk.2]
    rfl

theorem run_seekDs (bits : List Bool) (T : List Bool) (q k : ℕ)
    (idx : Fin (bits.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run (loopMachine bits) (2 * k) ⟨(2, idx, s), q, T⟩
      = ⟨(2, idx, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekD hk.1 hk.2]
    rfl

theorem run_seekOs (bits : List Bool) (T : List Bool) (q k : ℕ)
    (idx : Fin (bits.length + 1)) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run (loopMachine bits) (2 * k) ⟨(4, idx, s), q, T⟩
      = ⟨(4, idx, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekO (h k (by omega))]
    rfl

/-- The restore invariant (evolving tape), on the healing descriptor. -/
theorem run_rstL (bits : List Bool) (v : ℕ) (E : List Bool) (idx : Fin (bits.length + 1))
    (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run (loopMachine bits) (2 * i) ⟨(10, idx, s), 0, hlT v 0 ++ E⟩
      = ⟨(10, idx, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_heal (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ### The ROM block induction -/

/-- **ROM invariant.**  With `d` bits of the block left (`j + d = |bits|`), `4d` steps splice them all and
reset for the next round. -/
theorem run_rom (bits PRE out : List Bool) (q : ℕ) (hq : PRE.length = q) (s : Bool) :
    ∀ d j, (hjd : j + d = bits.length) → 0 < d →
      run (loopMachine bits) (4 * d)
        ⟨(6, ⟨j, by omega⟩, s), q + 2 * (out.length + j), PRE ++ encodeD (out ++ bits.take j)⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, PRE ++ encodeD (out ++ bits)⟩ := by
  intro d
  induction d with
  | zero => intro j hjd hd; omega
  | succ d ih =>
    intro j hjd hd
    have hsn := writes_snoc PRE (out ++ bits.take j) q hq (bits.getD j false)
    rw [show (out ++ bits.take j).length = out.length + j from by
        rw [List.length_append, List.length_take]; omega] at hsn
    have htake : (out ++ bits.take j) ++ [bits.getD j false] = out ++ bits.take (j + 1) := by
      rw [List.append_assoc, ← take_snoc_getD bits false j (by omega)]
    rw [htake] at hsn
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      have hj : j = bits.length - 1 := by omega
      subst hj
      have hlast : ¬(bits.length - 1 + 1 < bits.length) := by omega
      rw [show 4 * (0 + 1) = 4 from rfl, run_rom4_last (s := s) hlast, hsn,
        show bits.take (bits.length - 1 + 1) = bits from by
          rw [show bits.length - 1 + 1 = bits.length from by omega, List.take_length]]
    · have hmid : j + 1 < bits.length := by omega
      rw [show 4 * (d + 1) = 4 + 4 * d from by ring, run_add,
        run_rom4_mid (s := s) hmid, hsn,
        show q + 2 * (out.length + j) + 2 = q + 2 * (out.length + (j + 1)) from by omega]
      exact ih (j + 1) (by omega) hd0

/-! ## The round invariant -/

/-- **One loop round.**  From the origin on `cntT N k ++ encodeD (out ++ blkRep k)`, exactly
`2N + 2L + 2(k·|bits|) + 4|bits| + 4` steps mark the bound's pair `k`, splice one copy of the block at the
output terminator, and reset. -/
theorem run_loop_round (bits : List Bool) (N k : ℕ) (out : List Bool) (hk : k < N)
    (hbits : bits ≠ []) (idx : Fin (bits.length + 1)) (s : Bool) :
    run (loopMachine bits)
      (2 * N + 2 * out.length + 2 * (k * bits.length) + 4 * bits.length + 4)
      ⟨(0, idx, s), 0, cntT N k ++ encodeD (out ++ blkRep bits k)⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, false), 0,
          cntT N (k + 1) ++ encodeD (out ++ blkRep bits (k + 1))⟩ := by
  have hB : 0 < bits.length := List.length_pos_iff.mpr hbits
  -- Stage 1: skip the `k` processed pairs of the bound.
  have st1 := run_skipFs bits (cntT N k ++ encodeD (out ++ blkRep bits k)) 0 k idx s
    (fun i hi =>
      ⟨by simpa using cntE_mark_lo N k (encodeD (out ++ blkRep bits k)) i hi,
       by simpa using cntE_mark_hi N k (encodeD (out ++ blkRep bits k)) i hi⟩)
  simp only [Nat.zero_add] at st1
  -- Stage 2: mark the bound's pair `k`.
  have st2 := run_two_markF (idx := idx) (s := if k = 0 then s else true) (p := 2 * k)
    (cntE_data N k (encodeD (out ++ blkRep bits k)) (2 * k) (by omega) (by omega) (by omega))
    (cntE_data N k (encodeD (out ++ blkRep bits k)) (2 * k + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark N k (encodeD (out ++ blkRep bits k)) hk] at st2
  -- Stage 3: seek across the bound's remaining pairs.
  have st3 := run_seekDs bits (cntT N (k + 1) ++ encodeD (out ++ blkRep bits k)) (2 * k + 2)
    (N - k - 1) ⟨0, Nat.succ_pos _⟩ true (fun i hi =>
      ⟨cntE_data N (k + 1) (encodeD (out ++ blkRep bits k)) (2 * k + 2 + 2 * i)
         (by omega) (by omega) (by omega),
       cntE_data N (k + 1) (encodeD (out ++ blkRep bits k)) (2 * k + 2 + 2 * i + 1)
         (by omega) (by omega) (by omega)⟩)
  rw [show 2 * k + 2 + 2 * (N - k - 1) = 2 * N from by omega] at st3
  simp only [ite_self] at st3
  -- Stage 4: cross the bound's boundary.
  have st4 := run_two_crossD (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := true) (p := 2 * N)
    (cntE_cm_lo N (k + 1) (encodeD (out ++ blkRep bits k)) (by omega))
    (cntE_cm_hi N (k + 1) (encodeD (out ++ blkRep bits k)) (by omega))
  -- Stage 5: seek across the output's doubled data.
  have st5 := run_seekOs bits (cntT N (k + 1) ++ encodeD (out ++ blkRep bits k)) (2 * N + 2)
    (out.length + k * bits.length) ⟨0, Nat.succ_pos _⟩ false (fun i hi =>
      preD_data_eq (cntT N (k + 1)) (out ++ blkRep bits k) (2 * N + 2) i
        (cntT_length N (k + 1) (by omega))
        (by rw [List.length_append, blkRep_length]; omega))
  -- Stage 6: detect the output terminator.
  have hm_lo := preD_mark_lo (cntT N (k + 1)) (out ++ blkRep bits k) (2 * N + 2)
    (cntT_length N (k + 1) (by omega))
  have hm_hi := preD_mark_hi (cntT N (k + 1)) (out ++ blkRep bits k) (2 * N + 2)
    (cntT_length N (k + 1) (by omega))
  rw [show (out ++ blkRep bits k).length = out.length + k * bits.length from by
    rw [List.length_append, blkRep_length]] at hm_lo hm_hi
  have st6 := run_two_detectO (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := storedD (cntT N (k + 1) ++ encodeD (out ++ blkRep bits k)) (2 * N + 2) false
      (out.length + k * bits.length))
    (p := 2 * N + 2 + 2 * (out.length + k * bits.length)) hm_lo hm_hi
  -- Stage 7: splice the block (ROM) and reset.
  have st7 := run_rom bits (cntT N (k + 1)) (out ++ blkRep bits k) (2 * N + 2)
    (cntT_length N (k + 1) (by omega)) false bits.length 0 (by omega) hB
  simp only [List.take_zero, List.append_nil, Nat.add_zero] at st7
  rw [show (out ++ blkRep bits k).length = out.length + k * bits.length from by
      rw [List.length_append, blkRep_length]] at st7
  rw [List.append_assoc, show blkRep bits k ++ bits = blkRep bits (k + 1) from rfl] at st7
  -- Assemble the round.
  rw [show 2 * N + 2 * out.length + 2 * (k * bits.length) + 4 * bits.length + 4
      = 2 * k + (2 + (2 * (N - k - 1) + (2 + (2 * (out.length + k * bits.length)
          + (2 + 4 * bits.length))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6, st7]

/-! ## The rounds and their clocks -/

/-- The cumulative clock of the first `k` rounds (`L` the initial output bit-length, `B` the block
bit-length). -/
def lpRounds (N L B : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lpRounds N L B k + (2 * N + 2 * L + 2 * (k * B) + 4 * B + 4)

theorem lpRounds_eq (N L B k : ℕ) :
    lpRounds N L B k = 2 * N * k + 2 * L * k + B * k * k + 3 * B * k + 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [lpRounds]; rw [ih]; ring

/-- **Rounds invariant.**  `k` rounds consume `k` bound pairs and emit `k` copies of the block. -/
theorem run_loop_rounds (bits : List Bool) (N : ℕ) (out : List Bool) (hbits : bits ≠ [])
    (k : ℕ) (hk : k ≤ N) (s : Bool) :
    run (loopMachine bits) (lpRounds N out.length bits.length k)
      ⟨(0, ⟨0, Nat.succ_pos _⟩, s), 0, cntT N 0 ++ encodeD out⟩
      = ⟨(0, ⟨0, Nat.succ_pos _⟩, if k = 0 then s else false), 0,
          cntT N k ++ encodeD (out ++ blkRep bits k)⟩ := by
  induction k with
  | zero =>
    simp [blkRep]
    rfl
  | succ k ih =>
    rw [show lpRounds N out.length bits.length (k + 1)
        = lpRounds N out.length bits.length k
            + (2 * N + 2 * out.length + 2 * (k * bits.length) + 4 * bits.length + 4) from rfl,
      run_add, ih (by omega), run_loop_round bits N k out (by omega) hbits, if_neg (by omega)]

/-- The endgame clock: the exhausted find (with its reset) and the restore pass. -/
def lpTail (N : ℕ) : ℕ := 2 * N + (2 + (2 * N + 2))

/-- The loop's explicit clock. -/
def lpClock (N L B : ℕ) : ℕ := lpRounds N L B N + lpTail N

/-! ## The top theorem: a self-terminating, bound-preserving counted loop -/

/-- **The counted loop runs to completion.**  On tape `unaryD N ++ encodeD out`, after exactly
`lpClock N |out| |bits|` steps the machine halts with tape **exactly**
`unaryD N ++ encodeD (out ++ blkRep bits N)` — `N` copies of the fixed block emitted, the bound counter
restored. -/
theorem loop_run (bits : List Bool) (hbits : bits ≠ []) (N : ℕ) (out : List Bool) :
    run (loopMachine bits) (lpClock N out.length bits.length)
      (init (loopMachine bits) (unaryD N ++ encodeD out))
      = ⟨(12, ⟨0, Nat.succ_pos _⟩, false), 2 * N + 1,
          unaryD N ++ encodeD (out ++ blkRep bits N)⟩ := by
  rw [init_loop, ← cntT_zero, lpClock, run_add,
    run_loop_rounds bits N out hbits N (le_refl N) false, ite_self]
  -- Stage 1: the find phase exhausts the bound and resets into the restore pass.
  have st1 := run_skipFs bits (cntT N N ++ encodeD (out ++ blkRep bits N)) 0 N
    ⟨0, Nat.succ_pos _⟩ false (fun i hi =>
      ⟨by simpa using cntE_mark_lo N N (encodeD (out ++ blkRep bits N)) i hi,
       by simpa using cntE_mark_hi N N (encodeD (out ++ blkRep bits N)) i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toRst (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if N = 0 then false else true) (p := 2 * N)
    (cntE_cm_lo N N (encodeD (out ++ blkRep bits N)) (le_refl N))
    (cntE_cm_hi N N (encodeD (out ++ blkRep bits N)) (le_refl N))
  -- Stage 2: the restore pass and halt.
  have st3 := run_rstL bits N (encodeD (out ++ blkRep bits N)) ⟨0, Nat.succ_pos _⟩ false N
    (le_refl N)
  have st4 := run_two_done (idx := (⟨0, Nat.succ_pos _⟩ : Fin (bits.length + 1)))
    (s := if N = 0 then false else true) (p := 2 * N)
    (hlE_cm_lo N (encodeD (out ++ blkRep bits N)))
  -- Assemble the endgame.
  rw [lpTail, run_add, st1, run_add, st2, ← hlT_zero, run_add, st3, st4, hlT_last, cntT_zero]

/-- The machine **halts by itself** at its clock. -/
theorem loop_halted (bits : List Bool) (hbits : bits ≠ []) (N : ℕ) (out : List Bool) :
    (loopMachine bits).halt
      (run (loopMachine bits) (lpClock N out.length bits.length)
        (init (loopMachine bits) (unaryD N ++ encodeD out))).st = true := by
  rw [loop_run bits hbits N out]; rfl

/-- **The loop's output**: the bound preserved, `N` block copies appended. -/
theorem loop_output (bits : List Bool) (hbits : bits ≠ []) (N : ℕ) (out : List Bool) :
    (run (loopMachine bits) (lpClock N out.length bits.length)
      (init (loopMachine bits) (unaryD N ++ encodeD out))).tp
      = unaryD N ++ encodeD (out ++ blkRep bits N) := by
  rw [loop_run bits hbits N out]

/-- Closed form of the clock. -/
theorem lpClock_eq (N L B : ℕ) :
    lpClock N L B = B * N * N + 2 * N * N + 2 * L * N + 3 * B * N + 8 * N + 4 := by
  rw [lpClock, lpRounds_eq, lpTail]; ring

/-- **The clock is polynomial**: `lpClock N L B ≤ (B + 3)(N + L + 3)²`. -/
theorem lpClock_le (N L B : ℕ) : lpClock N L B ≤ (B + 3) * (N + L + 3) * (N + L + 3) := by
  rw [lpClock_eq]
  have h0 : N * N + 3 * N ≤ (N + L + 3) * (N + L + 3) := by nlinarith
  have h2 : 2 * N * N + 2 * L * N + 8 * N + 4 ≤ 3 * ((N + L + 3) * (N + L + 3)) := by nlinarith
  calc B * N * N + 2 * N * N + 2 * L * N + 3 * B * N + 8 * N + 4
      = B * (N * N + 3 * N) + (2 * N * N + 2 * L * N + 8 * N + 4) := by ring
    _ ≤ B * ((N + L + 3) * (N + L + 3)) + 3 * ((N + L + 3) * (N + L + 3)) :=
        Nat.add_le_add (Nat.mul_le_mul_left B h0) h2
    _ = (B + 3) * (N + L + 3) * (N + L + 3) := by ring

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoop
