import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitAppendBlock

/-!
# Cook–Levin M2 emitter, E3 (iii) — the counter-splice machine (`encodeNat` of a live counter)

Third and final brick of E3's inventory (`SCOPE_EMITTER.md` §3): appending `encodeNat v` — the unary block
of a **live counter's value** — to the doubled output, preserving the counter.  This is the E1 copy
machine's marking rounds crossed with the E3 append discipline:

* **Splice rounds**: find the counter's next unprocessed `11` pair (skipping `10` marks), mark it, seek right
  — across the counter's rest, its `01` boundary (finite control tracks the region crossing), and the output's
  doubled data — to the output's `01` terminator, splice one doubled `true` there (the four-write snoc of
  `...EmitAppendBlock`), reset.  Round `j` costs exactly `2v + 2L + 2j + 8` steps (`L = |out|`).
* **The terminator bit**: when the find phase hits the counter's boundary (all pairs marked), the same seek
  splices the block's closing `false` — `encodeNat v = replicate v true ++ [false]`, and the machine has
  emitted exactly its `v` trues and one false.
* **Restore pass**: heal the counter's `10` marks back to `11` — the splice is **counter-preserving** —
  and halt on the counter's boundary.

Proved: the counter-region and healing descriptors with `getD` suites and structural mark/heal write lemmas
(the output-region facts and the four-write snoc are **reused** from `...EmitAppendBlock` — `preD_data_eq`,
`preD_mark_lo/hi`, `writes_snoc`); all step/pair-step lemmas and five scan run-invariants; the round and
rounds invariants with explicit clocks (`splRounds`, closed form proved); and **the top theorem**
(`splice_run`/`splice_halted`): on `unaryD v ++ encodeD out` the machine halts by itself at the explicit
clock `splClock v L = 3v² + 2Lv + 13v + 2L + 10`, bounded by `3(v+L+3)²` (`splClock_le`), with tape
**exactly** `unaryD v ++ encodeD (out ++ encodeNat v)` — splice and preservation in one equation.

Scope note: the brick is stated for the counter-at-origin layout (`unaryD v` first, output last), the same
standalone promise form as E1; E4's master lifts it per work-region position by phase re-implementation, as
the M1 master did.  With this brick, E3's machine inventory is complete: fixed skeletons
(`...EmitAppendBlock`) + spliced counter blocks (here) cover every block stream of the five clause-shape
layouts (`...EmitTemplates`).  Next: E4, the nested-loop master.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock

/-! ## The counter-region descriptors -/

/-- The source counter with `j` pairs processed: `10^j 11^(v-j) 01`. -/
def cntT (v j : ℕ) : List Bool :=
  markedD j ++ (List.replicate (2 * (v - j)) true ++ [false, true])

theorem cntT_zero (v : ℕ) : cntT v 0 = unaryD v := by
  simp [cntT, markedD, unaryD_eq]

theorem cntT_length (v j : ℕ) (hj : j ≤ v) : (cntT v j).length = 2 * v + 2 := by
  simp only [cntT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-- The healing counter with `i` pairs restored: `11^i 10^(v-i) 01`. -/
def hlT (v i : ℕ) : List Bool :=
  List.replicate (2 * i) true ++ (markedD (v - i) ++ [false, true])

theorem hlT_zero (v : ℕ) : hlT v 0 = cntT v v := by
  simp [hlT, cntT]

theorem hlT_last (v : ℕ) : hlT v v = unaryD v := by
  simp [hlT, markedD, unaryD_eq]

theorem hlT_length (v i : ℕ) (hi : i ≤ v) : (hlT v i).length = 2 * v + 2 := by
  simp only [hlT, List.length_append, markedD_length, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-! ### `getD` suites (under an arbitrary output suffix `E`) -/

theorem cntE_mark_lo (v j : ℕ) (E : List Bool) (i : ℕ) (h : i < j) :
    (cntT v j ++ E).getD (2 * i) false = true := by
  rw [cntT, List.append_assoc, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_lo j i h

theorem cntE_mark_hi (v j : ℕ) (E : List Bool) (i : ℕ) (h : i < j) :
    (cntT v j ++ E).getD (2 * i + 1) false = false := by
  rw [cntT, List.append_assoc, List.getD_append (h := by rw [markedD_length]; omega)]
  exact markedD_getD_hi j i h

theorem cntE_data (v j : ℕ) (E : List Bool) (c : ℕ) (hj : j ≤ v) (h1 : 2 * j ≤ c)
    (h2 : c < 2 * v) :
    (cntT v j ++ E).getD c false = true := by
  rw [cntT]
  simp only [List.append_assoc]
  rw [show c = 2 * j + (c - 2 * j) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    List.getD_append (h := by rw [List.length_replicate]; omega)]
  exact List.getD_replicate _ (h := by omega)

theorem cntE_cm_lo (v j : ℕ) (E : List Bool) (hj : j ≤ v) :
    (cntT v j ++ E).getD (2 * v) false = false := by
  rw [cntT]
  simp only [List.append_assoc]
  rw [show 2 * v = 2 * j + (2 * (v - j) + 0) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem cntE_cm_hi (v j : ℕ) (E : List Bool) (hj : j ≤ v) :
    (cntT v j ++ E).getD (2 * v + 1) false = true := by
  rw [cntT]
  simp only [List.append_assoc]
  rw [show 2 * v + 1 = 2 * j + (2 * (v - j) + 1) from by omega,
    getD_append_left_length' _ _ (markedD_length j),
    getD_append_left_length' _ _ List.length_replicate]
  rfl

theorem hlE_pair_lo (v i : ℕ) (E : List Bool) (h : i < v) :
    (hlT v i ++ E).getD (2 * i) false = true := by
  rw [hlT, List.append_assoc, getD_append_length' _ _ List.length_replicate,
    show v - i = (v - i - 1) + 1 from by omega]
  rfl

theorem hlE_pair_hi (v i : ℕ) (E : List Bool) (h : i < v) :
    (hlT v i ++ E).getD (2 * i + 1) false = false := by
  rw [hlT, List.append_assoc, getD_append_left_length' _ _ List.length_replicate,
    show v - i = (v - i - 1) + 1 from by omega]
  rfl

theorem hlE_cm_lo (v : ℕ) (E : List Bool) :
    (hlT v v ++ E).getD (2 * v) false = false := by
  rw [hlT, Nat.sub_self, List.append_assoc, getD_append_length' _ _ List.length_replicate]
  rfl

theorem hlE_cm_hi (v : ℕ) (E : List Bool) :
    (hlT v v ++ E).getD (2 * v + 1) false = true := by
  rw [hlT, Nat.sub_self, List.append_assoc, getD_append_left_length' _ _ List.length_replicate]
  rfl

/-! ### The structural mark and heal writes (inside the counter region, suffix untouched) -/

/-- Marking the counter's next data pair. -/
theorem cntT_mark (v j : ℕ) (E : List Bool) (hj : j < v) :
    writeAt (cntT v j ++ E) (2 * j + 1) false = cntT v (j + 1) ++ E := by
  rw [writeAt_of_lt false (by
      rw [List.length_append, cntT_length v j (by omega)]; omega),
    List.set_append_left _ _ (by rw [cntT_length v j (by omega)]; omega), cntT,
    set_append_left_length' _ _ (markedD_length j),
    show 2 * (v - j) = 2 * (v - j - 1) + 1 + 1 from by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show v - j - 1 = v - (j + 1) from by omega]
  rfl

/-- Healing the counter's next processed pair. -/
theorem hlT_heal (v i : ℕ) (E : List Bool) (hi : i < v) :
    writeAt (hlT v i ++ E) (2 * i + 1) true = hlT v (i + 1) ++ E := by
  rw [writeAt_of_lt true (by
      rw [List.length_append, hlT_length v i (by omega)]; omega),
    List.set_append_left _ _ (by rw [hlT_length v i (by omega)]; omega), hlT,
    set_append_left_length' _ _ List.length_replicate,
    show v - i = (v - i - 1) + 1 from by omega]
  simp only [markedD, List.cons_append, List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc,
    show ([true, true] : List Bool) = List.replicate 2 true from rfl, ← List.replicate_add,
    show 2 * i + 2 = 2 * (i + 1) from by ring,
    show v - i - 1 = v - (i + 1) from by omega]
  rfl

/-! ## The splice machine

Control: `Fin 19 × Bool` (stored low cell).  Phases: `0/1` find in the counter (skip `10`, mark `11` ⇒
splice a `true`, boundary `01` ⇒ splice the closing `false`), `2/3` seek across the counter's rest to its
boundary, `4/5` seek across the output's doubled data to its `01` terminator, `6–9` the four-write `true`
snoc and reset (next round), `10/11` the final seek, `12–15` the four-write `false` snoc and reset into
`16/17` the restore pass (heal `10` ⇒ continue, boundary `01` ⇒ halt), `18` = halt. -/

def spliceMachine : Machine where
  State := Fin 19 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 18)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then (if b then ((2, s.2), some false, 1) else ((0, s.2), none, 1))
       else (if b then ((10, s.2), none, 1) else ((18, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then (if b then ((2, s.2), none, 1) else ((18, s.2), none, 2))
       else (if b then ((4, s.2), none, 1) else ((18, s.2), none, 2)))
    else if s.1 = 4 then ((5, b), none, 1)
    else if s.1 = 5 then
      (if b = s.2 then ((4, s.2), none, 1) else ((6, s.2), none, 0))
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some true, 1)
    else if s.1 = 8 then ((9, s.2), some false, 1)
    else if s.1 = 9 then ((0, s.2), some true, 3)
    else if s.1 = 10 then ((11, b), none, 1)
    else if s.1 = 11 then
      (if b = s.2 then ((10, s.2), none, 1) else ((12, s.2), none, 0))
    else if s.1 = 12 then ((13, s.2), some false, 1)
    else if s.1 = 13 then ((14, s.2), some false, 1)
    else if s.1 = 14 then ((15, s.2), some false, 1)
    else if s.1 = 15 then ((16, s.2), some true, 3)
    else if s.1 = 16 then ((17, b), none, 1)
    else if s.1 = 17 then
      (if s.2 then (if b then ((18, s.2), none, 2) else ((16, true), some true, 1))
       else ((18, s.2), none, 2))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_spl (x : List Bool) : init spliceMachine x = ⟨(0, false), 0, x⟩ := rfl

/-! ### Step lemmas -/

theorem step_s0 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s1_mark {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step spliceMachine ⟨(1, true), p, T⟩ = ⟨(2, true), p + 1, writeAt T p false⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s1_skip {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step spliceMachine ⟨(1, true), p, T⟩ = ⟨(0, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s1_final {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step spliceMachine ⟨(1, false), p, T⟩ = ⟨(10, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s2 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s3_data {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step spliceMachine ⟨(3, true), p, T⟩ = ⟨(2, true), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s3_cross {p : ℕ} {T : List Bool} (h : T.getD p false = true) :
    step spliceMachine ⟨(3, false), p, T⟩ = ⟨(4, false), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s4 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(4, s), p, T⟩ = ⟨(5, T.getD p false), p + 1, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s5_eq {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = s) :
    step spliceMachine ⟨(5, s), p, T⟩ = ⟨(4, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s5_ne {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false ≠ s) :
    step spliceMachine ⟨(5, s), p, T⟩ = ⟨(6, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s6 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(6, s), p, T⟩ = ⟨(7, s), p + 1, writeAt T p true⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s7 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(7, s), p, T⟩ = ⟨(8, s), p + 1, writeAt T p true⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s8 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(8, s), p, T⟩ = ⟨(9, s), p + 1, writeAt T p false⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s9 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(9, s), p, T⟩ = ⟨(0, s), 0, writeAt T p true⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s10 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(10, s), p, T⟩ = ⟨(11, T.getD p false), p + 1, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s11_eq {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false = s) :
    step spliceMachine ⟨(11, s), p, T⟩ = ⟨(10, s), p + 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s11_ne {s : Bool} {p : ℕ} {T : List Bool} (h : T.getD p false ≠ s) :
    step spliceMachine ⟨(11, s), p, T⟩ = ⟨(12, s), p - 1, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s12 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(12, s), p, T⟩ = ⟨(13, s), p + 1, writeAt T p false⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s13 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(13, s), p, T⟩ = ⟨(14, s), p + 1, writeAt T p false⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s14 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(14, s), p, T⟩ = ⟨(15, s), p + 1, writeAt T p false⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s15 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(15, s), p, T⟩ = ⟨(16, s), 0, writeAt T p true⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s16 {s : Bool} {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(16, s), p, T⟩ = ⟨(17, T.getD p false), p + 1, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

theorem step_s17_heal {p : ℕ} {T : List Bool} (h : T.getD p false = false) :
    step spliceMachine ⟨(17, true), p, T⟩ = ⟨(16, true), p + 1, writeAt T p true⟩ := by
  rw [List.getD_eq_getElem?_getD] at h
  simp [step, spliceMachine, moveHead, h]

theorem step_s17_done {p : ℕ} {T : List Bool} :
    step spliceMachine ⟨(17, false), p, T⟩ = ⟨(18, false), p, T⟩ := by
  simp only [step, spliceMachine, moveHead]; rfl

/-! ### Pair-step lemmas -/

theorem run_two_skipS {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run spliceMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s0, h1, step_s1_skip h2]

theorem run_two_markS {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), p + 2, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero, step_s0, h1, step_s1_mark h2]

theorem run_two_toFinal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(0, s), p, T⟩ = ⟨(10, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s0, h1, step_s1_final h2]

theorem run_two_seekA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s2, h1, step_s3_data h2]

theorem run_two_crossA {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s2, h1, step_s3_cross h2]

theorem run_two_seekB {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = T.getD (p + 1) false) :
    run spliceMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s4, step_s5_eq h.symm]

theorem run_two_detectB {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(4, s), p, T⟩ = ⟨(6, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s4, h1, step_s5_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_four_trueSnoc {s : Bool} {p : ℕ} {T : List Bool} :
    run spliceMachine 4 ⟨(6, s), p, T⟩
      = ⟨(0, s), 0, writeAt (writeAt (writeAt (writeAt T p true) (p + 1) true)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_s6, step_s7, step_s8, step_s9]

theorem run_two_seekF {s : Bool} {p : ℕ} {T : List Bool}
    (h : T.getD p false = T.getD (p + 1) false) :
    run spliceMachine 2 ⟨(10, s), p, T⟩ = ⟨(10, T.getD p false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s10, step_s11_eq h.symm]

theorem run_two_detectF {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run spliceMachine 2 ⟨(10, s), p, T⟩ = ⟨(12, false), p, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s10, h1, step_s11_ne (by rw [h2]; simp),
    show p + 1 - 1 = p from by omega]

theorem run_four_falseSnoc {s : Bool} {p : ℕ} {T : List Bool} :
    run spliceMachine 4 ⟨(12, s), p, T⟩
      = ⟨(16, s), 0, writeAt (writeAt (writeAt (writeAt T p false) (p + 1) false)
          (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero, step_s12, step_s13, step_s14, step_s15]

theorem run_two_heal {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run spliceMachine 2 ⟨(16, s), p, T⟩ = ⟨(16, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero, step_s16, h1, step_s17_heal h2]

theorem run_two_rstDone {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) :
    run spliceMachine 2 ⟨(16, s), p, T⟩ = ⟨(18, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero, step_s16, h1, step_s17_done]

/-! ### Scan run-invariants -/

/-- Skip `k` processed counter pairs in the find phase. -/
theorem run_findS (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = false) :
    run spliceMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_skipS hk.1 hk.2]
    rfl

/-- Seek across `k` unprocessed counter pairs. -/
theorem run_seekAs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true ∧ T.getD (q + 2 * i + 1) false = true) :
    run spliceMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekA hk.1 hk.2]
    rfl

/-- Seek across `k` doubled output pairs (equal cells; the stored bit tracks the last pair, as in the M1
scan). -/
theorem run_seekBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run spliceMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekB (h k (by omega))]
    rfl

/-- The final seek, same discipline. -/
theorem run_seekFs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = T.getD (q + 2 * i + 1) false) :
    run spliceMachine (2 * k) ⟨(10, s), q, T⟩
      = ⟨(10, storedD T q s k), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), run_two_seekF (h k (by omega))]
    rfl

/-- **Restore invariant** (evolving tape): `2i` steps heal the first `i` processed pairs. -/
theorem run_rst (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run spliceMachine (2 * i) ⟨(16, s), 0, hlT v 0 ++ E⟩
      = ⟨(16, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      run_two_heal (hlE_pair_lo v i E (by omega)) (hlE_pair_hi v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The round invariant -/

/-- **One splice round.**  From the origin on `cntT v j ++ encodeD (out ++ 1^j)`, `2v + 2L + 2j + 8` steps
mark the counter's pair `j`, seek to the output terminator, splice one doubled `true`, and reset. -/
theorem run_splice_round (v j : ℕ) (out : List Bool) (hj : j < v) (s : Bool) :
    run spliceMachine (2 * v + 2 * out.length + 2 * j + 8)
      ⟨(0, s), 0, cntT v j ++ encodeD (out ++ List.replicate j true)⟩
      = ⟨(0, false), 0, cntT v (j + 1) ++ encodeD (out ++ List.replicate (j + 1) true)⟩ := by
  -- Stage 1: skip the `j` processed pairs.
  have st1 := run_findS (cntT v j ++ encodeD (out ++ List.replicate j true)) 0 j s (fun i hi =>
    ⟨by simpa using cntE_mark_lo v j (encodeD (out ++ List.replicate j true)) i hi,
     by simpa using cntE_mark_hi v j (encodeD (out ++ List.replicate j true)) i hi⟩)
  simp only [Nat.zero_add] at st1
  -- Stage 2: mark pair `j`.
  have st2 := run_two_markS (s := if j = 0 then s else true) (p := 2 * j)
    (cntE_data v j (encodeD (out ++ List.replicate j true)) (2 * j) (by omega) (by omega)
      (by omega))
    (cntE_data v j (encodeD (out ++ List.replicate j true)) (2 * j + 1) (by omega) (by omega)
      (by omega))
  rw [cntT_mark v j (encodeD (out ++ List.replicate j true)) hj] at st2
  -- Stage 3: seek across the counter's remaining pairs.
  have st3 := run_seekAs (cntT v (j + 1) ++ encodeD (out ++ List.replicate j true)) (2 * j + 2)
    (v - j - 1) true (fun i hi =>
      ⟨cntE_data v (j + 1) (encodeD (out ++ List.replicate j true)) (2 * j + 2 + 2 * i)
         (by omega) (by omega) (by omega),
       cntE_data v (j + 1) (encodeD (out ++ List.replicate j true)) (2 * j + 2 + 2 * i + 1)
         (by omega) (by omega) (by omega)⟩)
  rw [show 2 * j + 2 + 2 * (v - j - 1) = 2 * v from by omega] at st3
  simp only [ite_self] at st3
  -- Stage 4: cross the counter's boundary.
  have st4 := run_two_crossA (s := true) (p := 2 * v)
    (cntE_cm_lo v (j + 1) (encodeD (out ++ List.replicate j true)) (by omega))
    (cntE_cm_hi v (j + 1) (encodeD (out ++ List.replicate j true)) (by omega))
  -- Stage 5: seek across the output's doubled data.
  have st5 := run_seekBs (cntT v (j + 1) ++ encodeD (out ++ List.replicate j true)) (2 * v + 2)
    (out.length + j) false (fun i hi =>
      preD_data_eq (cntT v (j + 1)) (out ++ List.replicate j true) (2 * v + 2) i
        (cntT_length v (j + 1) (by omega))
        (by rw [List.length_append, List.length_replicate]; omega))
  -- Stage 6: detect the output terminator.
  have hm_lo := preD_mark_lo (cntT v (j + 1)) (out ++ List.replicate j true) (2 * v + 2)
    (cntT_length v (j + 1) (by omega))
  have hm_hi := preD_mark_hi (cntT v (j + 1)) (out ++ List.replicate j true) (2 * v + 2)
    (cntT_length v (j + 1) (by omega))
  rw [show (out ++ List.replicate j true).length = out.length + j from by
    rw [List.length_append, List.length_replicate]] at hm_lo hm_hi
  have st6 := run_two_detectB
    (s := storedD (cntT v (j + 1) ++ encodeD (out ++ List.replicate j true)) (2 * v + 2) false
      (out.length + j))
    (p := 2 * v + 2 + 2 * (out.length + j)) hm_lo hm_hi
  -- Stage 7: the four-write `true` snoc, and reset.
  have hsn := writes_snoc (cntT v (j + 1)) (out ++ List.replicate j true) (2 * v + 2)
    (cntT_length v (j + 1) (by omega)) true
  rw [show (out ++ List.replicate j true).length = out.length + j from by
      rw [List.length_append, List.length_replicate],
    List.append_assoc, ← List.replicate_succ'] at hsn
  have st7 := run_four_trueSnoc
    (s := false) (p := 2 * v + 2 + 2 * (out.length + j))
    (T := cntT v (j + 1) ++ encodeD (out ++ List.replicate j true))
  rw [hsn] at st7
  -- Assemble the round.
  rw [show 2 * v + 2 * out.length + 2 * j + 8
      = 2 * j + (2 + (2 * (v - j - 1) + (2 + (2 * (out.length + j) + (2 + 4))))) from by omega,
    run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5, run_add, st6, st7]

/-! ## The rounds and their clocks -/

/-- The cumulative clock of the first `k` splice rounds (`L` the initial output bit-length). -/
def splRounds (v L : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => splRounds v L k + (2 * v + 2 * L + 2 * k + 8)

theorem splRounds_eq (v L k : ℕ) : splRounds v L k = 2 * v * k + 2 * L * k + k * k + 7 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [splRounds]; rw [ih]; ring

/-- **Rounds invariant.**  `k` rounds mark `k` counter pairs and splice `k` doubled trues. -/
theorem run_splice_rounds (v : ℕ) (out : List Bool) (k : ℕ) (hk : k ≤ v) (s : Bool) :
    run spliceMachine (splRounds v out.length k) ⟨(0, s), 0, cntT v 0 ++ encodeD out⟩
      = ⟨(0, if k = 0 then s else false), 0,
          cntT v k ++ encodeD (out ++ List.replicate k true)⟩ := by
  induction k with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [show splRounds v out.length (k + 1)
        = splRounds v out.length k + (2 * v + 2 * out.length + 2 * k + 8) from rfl, run_add,
      ih (by omega), run_splice_round v k out (by omega), if_neg (by omega)]

/-- The endgame clock: the exhausted find, the final seek, the `false` snoc, and the restore pass. -/
def splTail (v L : ℕ) : ℕ := 2 * v + (2 + (2 * (L + v) + (2 + (4 + (2 * v + 2)))))

/-- The splice's explicit clock. -/
def splClock (v L : ℕ) : ℕ := splRounds v L v + splTail v L

/-! ## The top theorem: a self-terminating, counter-preserving `encodeNat` splice -/

/-- **The splice runs to completion.**  On tape `unaryD v ++ encodeD out`, after exactly
`splClock v |out|` steps the machine halts with tape **exactly**
`unaryD v ++ encodeD (out ++ encodeNat v)` — the counter's unary block spliced into the doubled output,
the counter itself restored. -/
theorem splice_run (v : ℕ) (out : List Bool) :
    run spliceMachine (splClock v out.length) (init spliceMachine (unaryD v ++ encodeD out))
      = ⟨(18, false), 2 * v + 1, unaryD v ++ encodeD (out ++ encodeNat v)⟩ := by
  rw [init_spl, ← cntT_zero, splClock, run_add,
    run_splice_rounds v out v (le_refl v) false, ite_self]
  -- Stage 1: the find phase exhausts the counter.
  have st1 := run_findS (cntT v v ++ encodeD (out ++ List.replicate v true)) 0 v false
    (fun i hi =>
      ⟨by simpa using cntE_mark_lo v v (encodeD (out ++ List.replicate v true)) i hi,
       by simpa using cntE_mark_hi v v (encodeD (out ++ List.replicate v true)) i hi⟩)
  simp only [Nat.zero_add] at st1
  have st2 := run_two_toFinal (s := if v = 0 then false else true) (p := 2 * v)
    (cntE_cm_lo v v (encodeD (out ++ List.replicate v true)) (le_refl v))
    (cntE_cm_hi v v (encodeD (out ++ List.replicate v true)) (le_refl v))
  -- Stage 2: the final seek across the grown output.
  have st3 := run_seekFs (cntT v v ++ encodeD (out ++ List.replicate v true)) (2 * v + 2)
    (out.length + v) false (fun i hi =>
      preD_data_eq (cntT v v) (out ++ List.replicate v true) (2 * v + 2) i
        (cntT_length v v (le_refl v))
        (by rw [List.length_append, List.length_replicate]; omega))
  -- Stage 3: detect the terminator and splice the closing `false`.
  have hm_lo := preD_mark_lo (cntT v v) (out ++ List.replicate v true) (2 * v + 2)
    (cntT_length v v (le_refl v))
  have hm_hi := preD_mark_hi (cntT v v) (out ++ List.replicate v true) (2 * v + 2)
    (cntT_length v v (le_refl v))
  rw [show (out ++ List.replicate v true).length = out.length + v from by
    rw [List.length_append, List.length_replicate]] at hm_lo hm_hi
  have st4 := run_two_detectF
    (s := storedD (cntT v v ++ encodeD (out ++ List.replicate v true)) (2 * v + 2) false
      (out.length + v))
    (p := 2 * v + 2 + 2 * (out.length + v)) hm_lo hm_hi
  have hsn := writes_snoc (cntT v v) (out ++ List.replicate v true) (2 * v + 2)
    (cntT_length v v (le_refl v)) false
  rw [show (out ++ List.replicate v true).length = out.length + v from by
    rw [List.length_append, List.length_replicate]] at hsn
  have st5 := run_four_falseSnoc
    (s := false) (p := 2 * v + 2 + 2 * (out.length + v))
    (T := cntT v v ++ encodeD (out ++ List.replicate v true))
  rw [hsn] at st5
  -- Stage 4: the restore pass and halt.
  have st6 := run_rst v (encodeD ((out ++ List.replicate v true) ++ [false])) false v (le_refl v)
  have st7 := run_two_rstDone
    (s := if v = 0 then false else true) (p := 2 * v)
    (hlE_cm_lo v (encodeD ((out ++ List.replicate v true) ++ [false])))
  -- Assemble the endgame.
  rw [splTail, run_add, st1, run_add, st2, run_add, st3, run_add, st4, run_add, st5,
    ← hlT_zero, run_add, st6, st7, hlT_last, cntT_zero,
    show (out ++ List.replicate v true) ++ [false] = out ++ encodeNat v from by
      rw [List.append_assoc]; rfl]

/-- The machine **halts by itself** at its clock. -/
theorem splice_halted (v : ℕ) (out : List Bool) :
    spliceMachine.halt
      (run spliceMachine (splClock v out.length)
        (init spliceMachine (unaryD v ++ encodeD out))).st = true := by
  rw [splice_run]; rfl

/-- **Splice with preservation**: the output tape is the counter followed by the output with the counter's
unary block appended. -/
theorem splice_output (v : ℕ) (out : List Bool) :
    (run spliceMachine (splClock v out.length)
      (init spliceMachine (unaryD v ++ encodeD out))).tp
      = unaryD v ++ encodeD (out ++ encodeNat v) := by
  rw [splice_run]

/-- Closed form of the clock. -/
theorem splClock_eq (v L : ℕ) :
    splClock v L = 3 * v * v + 2 * L * v + 13 * v + 2 * L + 10 := by
  rw [splClock, splRounds_eq, splTail]; ring

/-- **The clock is quadratic**: `splClock v L ≤ 3(v + L + 3)²`. -/
theorem splClock_le (v L : ℕ) : splClock v L ≤ 3 * (v + L + 3) * (v + L + 3) := by
  rw [splClock_eq]; nlinarith

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
