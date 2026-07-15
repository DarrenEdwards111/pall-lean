import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRepP

/-!
# Cook–Levin M2 emitter — E2's majorant: `c·(n+1)²` by nested grand loops

`addTPPMachine` is the adder under TWO prefixes (the `P`-lift twice: each of the three skip pairs
chains into a second-level pair), so it is `repP_run`'s per-round body; `repP (addTPP)` is the
prefixed multiplier, itself `rep_run`'s per-round body; and `rep (repP (addTPP))` computes the
canonical majorant `p(n) = c·(n+1)²` in the padded accumulator (`majorant2_run`) — the outer grand
loop drives `c` inner multipliers, whose healed counters re-enter as `cntT v 0 = unaryD v` for
free.  For any fixed exponent `k` the same two lifts iterate (`k`-nested loops over a `k+1`-fold
prefixed adder); `k = 2` lands the pattern with all quantities on the tape at explicit clocks.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMajorant

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg2 (W4_append_right2)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3 (liftJ3 writeAt_append_right3
  W4_append_right3)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep

def addTPPMachine : Machine where
  State := Fin 24 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (12, false)
  halt := fun s => decide (s.1 = 11)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then
        (if b then ((14, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((16, s.2), none, 3) else ((11, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), some true, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some false, 1)
    else if s.1 = 8 then ((12, false), some true, 3)
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if s.2 then ((9, true), some true, 1)
       else (if b then ((11, false), none, 2) else ((11, false), none, 2)))
    else if s.1 = 12 then ((13, b), none, 1)
    else if s.1 = 13 then
      (if s.2 then ((12, s.2), none, 1)
       else (if b then ((18, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 14 then ((15, b), none, 1)
    else if s.1 = 15 then
      (if s.2 then ((14, s.2), none, 1)
       else (if b then ((20, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 16 then ((17, b), none, 1)
    else if s.1 = 17 then
      (if s.2 then ((16, s.2), none, 1)
       else (if b then ((22, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 18 then ((19, b), none, 1)
    else if s.1 = 19 then
      (if s.2 then ((18, s.2), none, 1)
       else (if b then ((0, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 20 then ((21, b), none, 1)
    else if s.1 = 21 then
      (if s.2 then ((20, s.2), none, 1)
       else (if b then ((2, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 22 then ((23, b), none, 1)
    else if s.1 = 23 then
      (if s.2 then ((22, s.2), none, 1)
       else (if b then ((9, s.2), none, 1) else ((11, s.2), none, 2)))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_a2 (t : List Bool) : init addTPPMachine t = ⟨(12, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsAP
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem a2_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run addTPPMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(0, s), p, T⟩ = ⟨(14, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(0, s), p, T⟩ = ⟨(16, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipR1 (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_walk (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTPPMachine, moveHead, h1']
  rw [e0]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_four_incr (h1 : T.getD p false = false) :
    run addTPPMachine 4 ⟨(4, s), p, T⟩
      = ⟨(12, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTPPMachine, moveHead, h1']
  have e1 : ∀ p' T', step addTPPMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTPPMachine, moveHead]; rfl
  have e2 : ∀ p' T', step addTPPMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, addTPPMachine, moveHead]; rfl
  have e3 : ∀ p' T', step addTPPMachine ⟨(8, s), p', T'⟩
      = ⟨(12, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem a2_healB (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_doneFin (h1 : T.getD p false = false) :
    run addTPPMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]
  rcases T.getD (p + 1) false with _ | _ <;> rfl

theorem a2_skipWf (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(12, s), p, T⟩ = ⟨(12, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossWf (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(12, s), p, T⟩ = ⟨(18, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(12, s), p, T⟩ = ⟨(13, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipWr (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(14, s), p, T⟩ = ⟨(14, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossWr (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(14, s), p, T⟩ = ⟨(20, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(14, s), p, T⟩ = ⟨(15, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipWh (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(16, s), p, T⟩ = ⟨(16, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(16, s), p, T⟩ = ⟨(17, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossWh (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(16, s), p, T⟩ = ⟨(22, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(16, s), p, T⟩ = ⟨(17, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

end StepsAP

/-! ### Scan invariants -/

theorem a2_skipBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run addTPPMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipB hk.1 hk.2]
    rfl

theorem a2_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipR1 (h k (by omega))]
    rfl

theorem a2_walks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_walk (h k (by omega))]
    rfl

theorem a2_skipWfs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(12, s), q, T⟩
      = ⟨(12, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipWf (h k (by omega))]
    rfl

theorem a2_skipWrs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(14, s), q, T⟩
      = ⟨(14, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipWr (h k (by omega))]
    rfl

theorem a2_skipWhs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(16, s), q, T⟩
      = ⟨(16, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipWh (h k (by omega))]
    rfl

theorem a2_healBs (P : List Bool) (G v : ℕ) (E : List Bool) (hP : P.length = 2 * G + 2)
    (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run addTPPMachine (2 * i) ⟨(9, s), 2 * G + 2, P ++ (hlT v 0 ++ E)⟩
      = ⟨(9, if i = 0 then s else true), 2 * G + 2 + 2 * i, P ++ (hlT v i ++ E)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (hlT v i ++ E)).getD (2 * G + 2 + 2 * i) false = true := by
      rw [show 2 * G + 2 + 2 * i = 2 * G + 2 + (2 * i) from rfl]
      exact liftJ P _ hP (hlE_pair_lo v i E (by omega))
    have hw : writeAt (P ++ (hlT v i ++ E)) (2 * G + 2 + 2 * i + 1) true
        = P ++ (hlT v (i + 1) ++ E) := by
      rw [show 2 * G + 2 + 2 * i + 1 = 2 * G + 2 + (2 * i + 1) from by omega,
        writeAt_append_right P _ (2 * G + 2) (2 * i + 1) true hP
          (by rw [List.length_append, hlT_length v i (by omega)]; omega),
        hlT_heal v i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      a2_healB h1, hw]
    rfl


theorem a2_skipW2f {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(18, s), p, T⟩ = ⟨(18, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossW2f {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(18, s), p, T⟩ = ⟨(0, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(18, s), p, T⟩ = ⟨(19, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipW2fs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(18, s), q, T⟩
      = ⟨(18, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipW2f (h k (by omega))]
    rfl

theorem a2_skipW2r {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(20, s), p, T⟩ = ⟨(20, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossW2r {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(20, s), p, T⟩ = ⟨(2, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(20, s), p, T⟩ = ⟨(21, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipW2rs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(20, s), q, T⟩
      = ⟨(20, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipW2r (h k (by omega))]
    rfl

theorem a2_skipW2h {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = true) :
    run addTPPMachine 2 ⟨(22, s), p, T⟩ = ⟨(22, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(22, s), p, T⟩ = ⟨(23, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTPPMachine, moveHead]; rfl

theorem a2_crossW2h {s : Bool} {p : ℕ} {T : List Bool}
    (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTPPMachine 2 ⟨(22, s), p, T⟩ = ⟨(9, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTPPMachine ⟨(22, s), p, T⟩ = ⟨(23, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTPPMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTPPMachine, moveHead, h2]

theorem a2_skipW2hs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTPPMachine (2 * k) ⟨(22, s), q, T⟩
      = ⟨(22, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), a2_skipW2h (h k (by omega))]
    rfl
/-- The two-prefix heal walk. -/
theorem a2_healBs2 (P Q : List Bool) (G1 G2 v : ℕ) (E : List Bool)
    (hP : P.length = 2 * G1 + 2) (hQ : Q.length = 2 * G2 + 2) (s : Bool) (i : ℕ)
    (hi : i ≤ v) :
    run addTPPMachine (2 * i)
      ⟨(9, s), 2 * G1 + 2 + 2 * G2 + 2, P ++ (Q ++ (hlT v 0 ++ E))⟩
      = ⟨(9, if i = 0 then s else true), 2 * G1 + 2 + 2 * G2 + 2 + 2 * i,
          P ++ (Q ++ (hlT v i ++ E))⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (P ++ (Q ++ (hlT v i ++ E))).getD (2 * G1 + 2 + 2 * G2 + 2 + 2 * i) false
        = true := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      exact liftJ2 P Q _ hP hQ (hlE_pair_lo v i E (by omega))
    have hw : writeAt (P ++ (Q ++ (hlT v i ++ E)))
        (2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1) true = P ++ (Q ++ (hlT v (i + 1) ++ E)) := by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega,
        writeAt_append_right2 P Q _ (2 * G1 + 2) (2 * G2 + 2) (2 * i + 1) true hP hQ
          (by rw [List.length_append, hlT_length v i (by omega)]; omega),
        hlT_heal v i E (by omega)]
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      a2_healB h1, hw]
    rfl

/-! ## The round and the loop -/

/-- One doubly-prefixed addition round. -/
theorem a2_round (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ) (hg2 : g2 ≤ G2)
    (A CAP v i : ℕ) (hi : i < A) (hvA : v + A ≤ CAP) (E : List Bool) (s : Bool) :
    run addTPPMachine (4 * G1 + 4 * G2 + 2 * A + 2 * v + 4 * i + 16)
      ⟨(12, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E)))⟩
      = ⟨(12, false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i + 1) ++ E)))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  have hA1 : (cntT A (i + 1)).length = 2 * A + 2 := cntT_length A (i + 1) (by omega)
  have r0 := a2_skipWfs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
    0 G1 s (fun i' hi' => by simpa using cntE_lo G1 g1 _ i' hg1 hi')
  simp only [Nat.zero_add] at r0
  have r0' := a2_crossWf (s := if G1 = 0 then s else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have r0b := a2_skipW2fs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i
      ++ (jT CAP (v + i) ++ E)))) (2 * G1 + 2) G2 false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * i' = 2 * G1 + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i' hg2 hi'))
  have r0c := a2_crossW2f (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have r1 := a2_skipBs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
    (2 * G1 + 2 + 2 * G2 + 2) i false
    (fun i' hi' => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i')
          from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (cntE_mark_lo A i _ i' hi'), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i' + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (cntE_mark_hi A i _ i' hi')⟩)
  have r2 := a2_markB (s := if i = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * i)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2
          (cntE_data A i _ (2 * i) (by omega) (by omega) (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2
          (cntE_data A i _ (2 * i + 1) (by omega) (by omega) (by omega)))
  have hwm : writeAt (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E))))
      (2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1) false
      = cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))) := by
    rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
        = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega,
      writeAt_append_right2 _ _ _ (2 * G1 + 2) (2 * G2 + 2) (2 * i + 1) false hW1 hW2
        (by rw [List.length_append, cntT_length A i (by omega)]; omega),
      cntT_mark A i _ hi]
  rw [hwm] at r2
  have r3 := a2_skipWrs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1)
      ++ (jT CAP (v + i) ++ E)))) 0 G1 true
    (fun i' hi' => by simpa using cntE_lo G1 g1 _ i' hg1 hi')
  simp only [Nat.zero_add] at r3
  have r3' := a2_crossWr (s := if G1 = 0 then true else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have r3b := a2_skipW2rs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1)
      ++ (jT CAP (v + i) ++ E)))) (2 * G1 + 2) G2 false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * i' = 2 * G1 + 2 + (2 * i') from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i' hg2 hi'))
  have r3c := a2_crossW2r (s := if G2 = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have r4 := a2_skipR1s (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1)
      ++ (jT CAP (v + i) ++ E)))) (2 * G1 + 2 + 2 * G2 + 2) A false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i' = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i')
          from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (cntE_lo A (i + 1) _ i' (by omega) hi'))
  have r5 := a2_crossR1 (s := if A = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * A)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A = 2 * G1 + 2 + (2 * G2 + 2 + 2 * A)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (cntE_cm_lo A (i + 1) _ (by omega)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * A + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (cntE_cm_hi A (i + 1) _ (by omega)))
  have r6 := a2_walks (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1)
      ++ (jT CAP (v + i) ++ E)))) (2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 2) (v + i) false
    (fun i' hi' => by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 2 + 2 * i'
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * A + 2 + 2 * i')) from by omega,
        ← jsT_zero CAP (v + i)]
      exact liftJ3 _ _ _ _ hW1 hW2 hA1
        (jsE_data CAP (v + i) 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have r7 := a2_four_incr (s := if v + i = 0 then false else true)
    (p := 2 * G1 + 2 + (2 * G2 + 2 + (2 * A + 2 + 2 * (v + i))))
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A (i + 1) ++ (jT CAP (v + i) ++ E))))
    (by rw [← jsT_zero CAP (v + i)]
        exact liftJ3 _ _ _ _ hW1 hW2 hA1 (jsE_m_lo CAP (v + i) 0 _ (by omega)))
  rw [W4_append_right3 (cntT G1 g1) (cntT G2 g2) (cntT A (i + 1))
      (jT CAP (v + i) ++ E) (2 * G1 + 2) (2 * G2 + 2) (2 * A + 2) (2 * (v + i))
      true true false true hW1 hW2 hA1
      (by rw [List.length_append, jT_length CAP (v + i) (by omega)]; omega),
    jT_incr CAP (v + i) _ (by omega)] at r7
  rw [show 4 * G1 + 4 * G2 + 2 * A + 2 * v + 4 * i + 16
      = 2 * G1 + (2 + (2 * G2 + (2 + (2 * i + (2 + (2 * G1 + (2 + (2 * G2 + (2
          + (2 * A + (2 + (2 * (v + i) + 4)))))))))))) from by omega,
    run_add, r0, run_add, r0', run_add, r0b, run_add, r0c, run_add, r1, run_add, r2,
    run_add, r3, run_add, r3', run_add, r3b, run_add, r3c, run_add, r4, run_add, r5,
    run_add, r6,
    show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 2 + 2 * (v + i)
      = 2 * G1 + 2 + (2 * G2 + 2 + (2 * A + 2 + 2 * (v + i))) from by omega,
    r7]

def a2ClockN (G1 G2 A v : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => a2ClockN G1 G2 A v i + (4 * G1 + 4 * G2 + 2 * A + 2 * v + 4 * i + 16)

theorem a2_run_rounds (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ) (hg2 : g2 ≤ G2)
    (A CAP v : ℕ) (hvA : v + A ≤ CAP) (E : List Bool) (i : ℕ) (hi : i ≤ A) (s : Bool) :
    run addTPPMachine (a2ClockN G1 G2 A v i)
      ⟨(12, s), 0, cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A 0 ++ (jT CAP v ++ E)))⟩
      = ⟨(12, if i = 0 then s else false), 0,
          cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A i ++ (jT CAP (v + i) ++ E)))⟩ := by
  induction i with
  | zero => simp only [a2ClockN]; rw [run_zero]; simp
  | succ i ih =>
    rw [show a2ClockN G1 G2 A v (i + 1)
        = a2ClockN G1 G2 A v i + (4 * G1 + 4 * G2 + 2 * A + 2 * v + 4 * i + 16) from rfl,
      run_add, ih (by omega), a2_round G1 g1 hg1 G2 g2 hg2 A CAP v i (by omega) hvA E _,
      if_neg (by omega), show v + (i + 1) = v + i + 1 from by omega]

def a2Clock (G1 G2 A v : ℕ) : ℕ :=
  a2ClockN G1 G2 A v A
    + (2 * G1 + (2 + (2 * G2 + (2 + (2 * A + (2 + (2 * G1 + (2 + (2 * G2 + (2
        + (2 * A + 2)))))))))))

/-- **The doubly-prefixed adder runs to completion** — `repP_run`'s hypothesis shape. -/
theorem addTPP_run (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (G2 g2 : ℕ) (hg2 : g2 ≤ G2)
    (A CAP v : ℕ) (hvA : v + A ≤ CAP) (E : List Bool) :
    run addTPPMachine (a2Clock G1 G2 A v)
      (init addTPPMachine (cntT G1 g1 ++ (cntT G2 g2 ++ (unaryD A ++ (jT CAP v ++ E)))))
      = ⟨(11, false), 2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 1,
          cntT G1 g1 ++ (cntT G2 g2 ++ (unaryD A ++ (jT CAP (v + A) ++ E)))⟩ := by
  have hW1 : (cntT G1 g1).length = 2 * G1 + 2 := cntT_length G1 g1 hg1
  have hW2 : (cntT G2 g2).length = 2 * G2 + 2 := cntT_length G2 g2 hg2
  rw [init_a2,
    show (cntT G1 g1 ++ (cntT G2 g2 ++ (unaryD A ++ (jT CAP v ++ E))) : List Bool)
      = cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A 0 ++ (jT CAP v ++ E))) from by rw [cntT_zero]]
  simp only [a2Clock]
  have f0 := a2_skipWfs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A
      ++ (jT CAP (v + A) ++ E)))) 0 G1 false
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f0
  have f0' := a2_crossWf (s := if G1 = 0 then false else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A ++ (jT CAP (v + A) ++ E))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f0b := a2_skipW2fs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A
      ++ (jT CAP (v + A) ++ E)))) (2 * G1 + 2) G2 false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f0c := a2_crossW2f (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A ++ (jT CAP (v + A) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f1 := a2_skipBs (cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A ++ (jT CAP (v + A) ++ E))))
    (2 * G1 + 2 + 2 * G2 + 2) A false
    (fun i hi => ⟨by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i = 2 * G1 + 2 + (2 * G2 + 2 + 2 * i)
          from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (cntE_mark_lo A A _ i hi), by
      rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * i + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * i + 1)) from by omega]
      exact liftJ2 _ _ _ hW1 hW2 (cntE_mark_hi A A _ i hi)⟩)
  have f2 := a2_doneB (s := if A = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * A)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (cntT A A ++ (jT CAP (v + A) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A = 2 * G1 + 2 + (2 * G2 + 2 + 2 * A)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (cntE_cm_lo A A _ (le_refl A)))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A + 1
          = 2 * G1 + 2 + (2 * G2 + 2 + (2 * A + 1)) from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (cntE_cm_hi A A _ (le_refl A)))
  have f3 := a2_skipWhs (cntT G1 g1 ++ (cntT G2 g2 ++ (hlT A 0
      ++ (jT CAP (v + A) ++ E)))) 0 G1 false
    (fun i hi => by simpa using cntE_lo G1 g1 _ i hg1 hi)
  simp only [Nat.zero_add] at f3
  have f3' := a2_crossWh (s := if G1 = 0 then false else true) (p := 2 * G1)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (hlT A 0 ++ (jT CAP (v + A) ++ E))))
    (cntE_cm_lo G1 g1 _ hg1) (cntE_cm_hi G1 g1 _ hg1)
  have f3b := a2_skipW2hs (cntT G1 g1 ++ (cntT G2 g2 ++ (hlT A 0
      ++ (jT CAP (v + A) ++ E)))) (2 * G1 + 2) G2 false
    (fun i hi => by
      rw [show 2 * G1 + 2 + 2 * i = 2 * G1 + 2 + (2 * i) from rfl]
      exact liftJ _ _ hW1 (cntE_lo G2 g2 _ i hg2 hi))
  have f3c := a2_crossW2h (s := if G2 = 0 then false else true) (p := 2 * G1 + 2 + 2 * G2)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (hlT A 0 ++ (jT CAP (v + A) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 = 2 * G1 + 2 + (2 * G2) from rfl]
        exact liftJ _ _ hW1 (cntE_cm_lo G2 g2 _ hg2))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 1 = 2 * G1 + 2 + (2 * G2 + 1) from by omega]
        exact liftJ _ _ hW1 (cntE_cm_hi G2 g2 _ hg2))
  have f4 := a2_healBs2 (cntT G1 g1) (cntT G2 g2) G1 G2 A (jT CAP (v + A) ++ E) hW1 hW2
    false A (le_refl A)
  have f5 := a2_doneFin (s := if A = 0 then false else true)
    (p := 2 * G1 + 2 + 2 * G2 + 2 + 2 * A)
    (T := cntT G1 g1 ++ (cntT G2 g2 ++ (hlT A A ++ (jT CAP (v + A) ++ E))))
    (by rw [show 2 * G1 + 2 + 2 * G2 + 2 + 2 * A = 2 * G1 + 2 + (2 * G2 + 2 + 2 * A)
          from by omega]
        exact liftJ2 _ _ _ hW1 hW2 (hlE_cm_lo A _))
  rw [run_add, a2_run_rounds G1 g1 hg1 G2 g2 hg2 A CAP v hvA E A (le_refl A) false,
    ite_self, run_add, f0, run_add, f0', run_add, f0b, run_add, f0c, run_add, f1,
    run_add, f2, ← hlT_zero, run_add, f3, run_add, f3', run_add, f3b, run_add, f3c,
    run_add, f4, f5, hlT_last]

theorem addTPP_halt : addTPPMachine.halt ((11 : Fin 24), false) = true := rfl

/-! ## THE k = 2 MAJORANT: `c·(n+1)²` BY NESTED GRAND LOOPS -/

open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP

/-- **The inner multiplier as a per-round body**: `repP` over the doubly-prefixed adder adds
`(n+1)·A` per outer round — `repP_run`'s own conclusion is `rep_run`'s hypothesis shape. -/
theorem repP_mul_run (G1 g1 : ℕ) (hg1 : g1 ≤ G1) (B A CAP v : ℕ)
    (hcap : v + B * A ≤ CAP) (E : List Bool) :
    run (repPMachine addTPPMachine)
      (repPRounds G1 (fun t => a2Clock G1 B A (v + t * A)) B + (4 * G1 + 4 * B + 8))
      (init (repPMachine addTPPMachine)
        (cntT G1 g1 ++ (cntT B 0 ++ (unaryD A ++ (jT CAP v ++ E)))))
      = ⟨Sum.inl (4, false), 2 * G1 + 2 + 2 * B + 1,
          cntT G1 g1 ++ (unaryD B ++ (unaryD A ++ (jT CAP (v + B * A) ++ E)))⟩ := by
  have h := repP_run addTPPMachine G1 g1 hg1 B
    (fun t => unaryD A ++ (jT CAP (v + t * A) ++ E))
    (fun t => a2Clock G1 B A (v + t * A))
    (fun _ => (11, false)) (fun _ => 2 * G1 + 2 + 2 * B + 2 + 2 * A + 1)
    (fun t ht => by
      constructor
      · have hr := addTPP_run G1 g1 hg1 B (t + 1) (by omega) A CAP (v + t * A)
          (by have h1 : (t + 1) * A ≤ B * A := Nat.mul_le_mul_right _ (by omega)
              have h0 : (t + 1) * A = t * A + A := by ring
              omega) E
        rw [show v + t * A + A = v + (t + 1) * A from by ring] at hr
        exact hr
      · rfl)
  simpa using h

/-- **THE k = 2 MAJORANT MACHINE**: `rep (repP (addTPP))` computes `c·(n+1)²` in the padded
accumulator — the outer grand loop drives `c` rounds of the inner `repP`-multiplier, whose healed
counter re-enters as `cntT (n+1) 0 = unaryD (n+1)` for free.  With `n := |x|` this is the concrete
canonical majorant `p(n) = c·(n+1)²` of any quadratically-bounded clock, on the tape, at the
explicit clock — the `k`-fold pattern iterates the same two lifts per fixed exponent. -/
theorem majorant2_run (c n CAP : ℕ) (hcap : c * ((n + 1) * (n + 1)) ≤ CAP)
    (E : List Bool) :
    run (repMachine (repPMachine addTPPMachine))
      (repRounds (fun j =>
          repPRounds c (fun t => a2Clock c (n + 1) (n + 1)
            (j * ((n + 1) * (n + 1)) + t * (n + 1))) (n + 1)
          + (4 * c + 4 * (n + 1) + 8)) c + (4 * c + 4))
      (init (repMachine (repPMachine addTPPMachine))
        (cntT c 0 ++ (unaryD (n + 1) ++ (unaryD (n + 1) ++ (jT CAP 0 ++ E)))))
      = ⟨Sum.inl (4, false), 2 * c + 1,
          unaryD c ++ (unaryD (n + 1) ++ (unaryD (n + 1)
            ++ (jT CAP (c * ((n + 1) * (n + 1))) ++ E)))⟩ := by
  have h := rep_run (repPMachine addTPPMachine) c
    (fun j => unaryD (n + 1) ++ (unaryD (n + 1)
      ++ (jT CAP (j * ((n + 1) * (n + 1))) ++ E)))
    (fun j => repPRounds c (fun t => a2Clock c (n + 1) (n + 1)
        (j * ((n + 1) * (n + 1)) + t * (n + 1))) (n + 1)
      + (4 * c + 4 * (n + 1) + 8))
    (fun _ => Sum.inl (4, false)) (fun _ => 2 * c + 2 + 2 * (n + 1) + 1)
    (fun j hj => by
      constructor
      · have hr := repP_mul_run c (j + 1) (by omega) (n + 1) (n + 1) CAP
          (j * ((n + 1) * (n + 1)))
          (by have h1 : (j + 1) * ((n + 1) * (n + 1)) ≤ c * ((n + 1) * (n + 1)) :=
                Nat.mul_le_mul_right _ (by omega)
              calc j * ((n + 1) * (n + 1)) + (n + 1) * (n + 1)
                  = (j + 1) * ((n + 1) * (n + 1)) := by ring
                _ ≤ c * ((n + 1) * (n + 1)) := h1
                _ ≤ CAP := hcap) E
        rw [show j * ((n + 1) * (n + 1)) + (n + 1) * (n + 1)
            = (j + 1) * ((n + 1) * (n + 1)) from by ring,
          show (cntT c (j + 1) ++ (cntT (n + 1) 0 ++ (unaryD (n + 1)
              ++ (jT CAP (j * ((n + 1) * (n + 1))) ++ E))) : List Bool)
            = cntT c (j + 1) ++ (unaryD (n + 1) ++ (unaryD (n + 1)
              ++ (jT CAP (j * ((n + 1) * (n + 1))) ++ E))) from by rw [cntT_zero]] at hr
        exact hr
      · rfl)
  simpa using h
end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMajorant
