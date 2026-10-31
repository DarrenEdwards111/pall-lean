import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInterT

/-!
# Cook–Levin M2 emitter — E2's primitive: unary addition into a padded accumulator

`addTMachine` computes `v + A` in place: on the layout `unaryD A ++ (jT CAP v ++ E)` it loops over
the addend counter — mark a pair, walk to the accumulator's value marker, apply the in-place
four-write increment (`jT_incr`), reset — then heals the addend and halts:
`unaryD A ++ (jT CAP (v + A) ++ E)`, the addend restored verbatim, the suffix untouched.

This is the arithmetic primitive of **E2**: the accumulator is capacity-padded (`jT CAP v`, fixed
length `2·CAP+2`), so repeated addition — and hence multiplication, and hence the canonical
polynomial majorant `p(n) = c·(n+1)^k` — evaluates with **fixed region addresses**, the same design
that carried the `t`-mirror.  Multiplication is this machine iterated (an outer marked counter and
a grand prefix — the established `P`-lift); the majorant is `k` chained multiplications.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitAddT

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar

/-! ## The machine

`Fin 12 × Bool`: `0/1` the loop find over the addend (mark an unmarked pair, or done at the end
marker), `2/3` re-skip the addend, `4/5` walk the accumulator's filled pairs,
`4(else),6,7,8` the four-write increment at the marker, `9/10` the addend heal, `11` halt. -/

def addTMachine : Machine where
  State := Fin 12 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 11)
  δ := fun s b =>
    if s.1 = 0 then ((1, b), none, 1)
    else if s.1 = 1 then
      (if s.2 then
        (if b then ((2, s.2), some false, 3) else ((0, s.2), none, 1))
       else (if b then ((9, s.2), none, 3) else ((11, s.2), none, 2)))
    else if s.1 = 2 then ((3, b), none, 1)
    else if s.1 = 3 then
      (if s.2 then ((2, s.2), none, 1)
       else (if b then ((4, s.2), none, 1) else ((11, s.2), none, 2)))
    else if s.1 = 4 then
      (if b then ((5, b), none, 1) else ((6, s.2), some true, 1))
    else if s.1 = 5 then ((4, s.2), none, 1)
    else if s.1 = 6 then ((7, s.2), some true, 1)
    else if s.1 = 7 then ((8, s.2), some false, 1)
    else if s.1 = 8 then ((0, false), some true, 3)
    else if s.1 = 9 then ((10, b), none, 1)
    else if s.1 = 10 then
      (if s.2 then ((9, true), some true, 1)
       else (if b then ((11, false), none, 2) else ((11, false), none, 2)))
    else ((s.1, s.2), none, 2)
  accept := fun _ => false

theorem init_at (t : List Bool) : init addTMachine t = ⟨(0, false), 0, t⟩ := rfl

/-! ## The step layer -/

section StepsAT
variable {s : Bool} {p : ℕ} {T : List Bool}

theorem at_skipB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = false) :
    run addTMachine 2 ⟨(0, s), p, T⟩ = ⟨(0, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTMachine, moveHead, h2]

theorem at_markB (h1 : T.getD p false = true) (h2 : T.getD (p + 1) false = true) :
    run addTMachine 2 ⟨(0, s), p, T⟩ = ⟨(2, true), 0, writeAt T (p + 1) false⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTMachine, moveHead, h2]

theorem at_doneB (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTMachine 2 ⟨(0, s), p, T⟩ = ⟨(9, false), 0, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(0, s), p, T⟩ = ⟨(1, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTMachine, moveHead, h2]

theorem at_skipR1 (h1 : T.getD p false = true) :
    run addTMachine 2 ⟨(2, s), p, T⟩ = ⟨(2, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTMachine, moveHead]; rfl

theorem at_crossR1 (h1 : T.getD p false = false) (h2 : T.getD (p + 1) false = true) :
    run addTMachine 2 ⟨(2, s), p, T⟩ = ⟨(4, false), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(2, s), p, T⟩ = ⟨(3, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  rw [List.getD_eq_getElem?_getD] at h2
  simp [step, addTMachine, moveHead, h2]

theorem at_walk (h1 : T.getD p false = true) :
    run addTMachine 2 ⟨(4, s), p, T⟩ = ⟨(4, true), p + 2, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(4, s), p, T⟩ = ⟨(5, true), p + 1, T⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTMachine, moveHead, h1']
  rw [e0]
  simp only [step, addTMachine, moveHead]; rfl

/-- The four-write increment at the accumulator's marker, then reset. -/
theorem at_four_incr (h1 : T.getD p false = false) :
    run addTMachine 4 ⟨(4, s), p, T⟩
      = ⟨(0, false), 0, writeAt (writeAt (writeAt (writeAt T p true)
          (p + 1) true) (p + 2) false) (p + 3) true⟩ := by
  rw [run_succ, run_succ, run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(4, s), p, T⟩ = ⟨(6, s), p + 1, writeAt T p true⟩ := by
    have h1' := h1
    rw [List.getD_eq_getElem?_getD] at h1'
    simp [step, addTMachine, moveHead, h1']
  have e1 : ∀ p' T', step addTMachine ⟨(6, s), p', T'⟩
      = ⟨(7, s), p' + 1, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTMachine, moveHead]; rfl
  have e2 : ∀ p' T', step addTMachine ⟨(7, s), p', T'⟩
      = ⟨(8, s), p' + 1, writeAt T' p' false⟩ := by
    intro p' T'; simp only [step, addTMachine, moveHead]; rfl
  have e3 : ∀ p' T', step addTMachine ⟨(8, s), p', T'⟩
      = ⟨(0, false), 0, writeAt T' p' true⟩ := by
    intro p' T'; simp only [step, addTMachine, moveHead]; rfl
  rw [e0, e1, e2, e3]

theorem at_healB (h1 : T.getD p false = true) :
    run addTMachine 2 ⟨(9, s), p, T⟩ = ⟨(9, true), p + 2, writeAt T (p + 1) true⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTMachine, moveHead]; rfl

theorem at_doneFin (h1 : T.getD p false = false) :
    run addTMachine 2 ⟨(9, s), p, T⟩ = ⟨(11, false), p + 1, T⟩ := by
  rw [run_succ, run_succ, run_zero]
  have e0 : step addTMachine ⟨(9, s), p, T⟩ = ⟨(10, T.getD p false), p + 1, T⟩ := by
    simp only [step, addTMachine, moveHead]; rfl
  rw [e0, h1]
  simp only [step, addTMachine, moveHead]
  rcases T.getD (p + 1) false with _ | _ <;> rfl

end StepsAT

/-! ### Scan invariants -/

theorem at_skipBs (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true
      ∧ T.getD (q + 2 * i + 1) false = false) :
    run addTMachine (2 * k) ⟨(0, s), q, T⟩
      = ⟨(0, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), at_skipB hk.1 hk.2]
    rfl

theorem at_skipR1s (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTMachine (2 * k) ⟨(2, s), q, T⟩
      = ⟨(2, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), at_skipR1 (h k (by omega))]
    rfl

theorem at_walks (T : List Bool) (q k : ℕ) (s : Bool)
    (h : ∀ i, i < k → T.getD (q + 2 * i) false = true) :
    run addTMachine (2 * k) ⟨(4, s), q, T⟩
      = ⟨(4, if k = 0 then s else true), q + 2 * k, T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, run_add,
      ih (fun i hi => h i (by omega)), at_walk (h k (by omega))]
    rfl

theorem at_healBs (v : ℕ) (E : List Bool) (s : Bool) (i : ℕ) (hi : i ≤ v) :
    run addTMachine (2 * i) ⟨(9, s), 0, hlT v 0 ++ E⟩
      = ⟨(9, if i = 0 then s else true), 2 * i, hlT v i ++ E⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 from by ring, run_add, ih (by omega),
      at_healB (hlE_pair_lo v i E (by omega)),
      hlT_heal v i E (by omega)]
    rfl

/-! ## The round and the loop -/

/-- One addition round: scan `i` marks, mark pair `i`, re-skip the addend, walk `v+i` filled
pairs, increment, reset. -/
theorem at_round (A CAP v i : ℕ) (hi : i < A) (hvA : v + A ≤ CAP) (E : List Bool)
    (s : Bool) :
    run addTMachine (2 * A + 2 * v + 4 * i + 8)
      ⟨(0, s), 0, cntT A i ++ (jT CAP (v + i) ++ E)⟩
      = ⟨(0, false), 0, cntT A (i + 1) ++ (jT CAP (v + i + 1) ++ E)⟩ := by
  have hA1 : (cntT A (i + 1)).length = 2 * A + 2 := cntT_length A (i + 1) (by omega)
  have r1 := at_skipBs (cntT A i ++ (jT CAP (v + i) ++ E)) 0 i s
    (fun i' hi' => ⟨by simpa using cntE_mark_lo A i _ i' hi',
                    by simpa using cntE_mark_hi A i _ i' hi'⟩)
  simp only [Nat.zero_add] at r1
  have r2 := at_markB (s := if i = 0 then s else true) (p := 2 * i)
    (T := cntT A i ++ (jT CAP (v + i) ++ E))
    (cntE_data A i _ (2 * i) (by omega) (by omega) (by omega))
    (cntE_data A i _ (2 * i + 1) (by omega) (by omega) (by omega))
  rw [cntT_mark A i _ hi] at r2
  have r3 := at_skipR1s (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)) 0 A true
    (fun i' hi' => by simpa using cntE_lo A (i + 1) _ i' (by omega) hi')
  simp only [Nat.zero_add] at r3
  have r4 := at_crossR1 (s := if A = 0 then true else true) (p := 2 * A)
    (T := cntT A (i + 1) ++ (jT CAP (v + i) ++ E))
    (cntE_cm_lo A (i + 1) _ (by omega)) (cntE_cm_hi A (i + 1) _ (by omega))
  have r5 := at_walks (cntT A (i + 1) ++ (jT CAP (v + i) ++ E)) (2 * A + 2) (v + i) false
    (fun i' hi' => by
      rw [show 2 * A + 2 + 2 * i' = 2 * A + 2 + (2 * i') from rfl, ← jsT_zero CAP (v + i)]
      exact liftJ _ _ hA1
        (jsE_data CAP (v + i) 0 _ (2 * i') (by omega) (by omega) (by omega)))
  have r6 := at_four_incr (s := if v + i = 0 then false else true)
    (p := 2 * A + 2 + 2 * (v + i)) (T := cntT A (i + 1) ++ (jT CAP (v + i) ++ E))
    (by rw [show 2 * A + 2 + 2 * (v + i) = 2 * A + 2 + (2 * (v + i)) from rfl,
        ← jsT_zero CAP (v + i)]
        exact liftJ _ _ hA1 (jsE_m_lo CAP (v + i) 0 _ (by omega)))
  rw [show 2 * A + 2 + 2 * (v + i) = 2 * A + 2 + (2 * (v + i)) from rfl,
    W4_append_right (cntT A (i + 1)) (jT CAP (v + i) ++ E) (2 * A + 2) (2 * (v + i))
      true true false true hA1
      (by rw [List.length_append, jT_length CAP (v + i) (by omega)]; omega),
    jT_incr CAP (v + i) _ (by omega)] at r6
  rw [show 2 * A + 2 * v + 4 * i + 8
      = 2 * i + (2 + (2 * A + (2 + (2 * (v + i) + 4)))) from by omega,
    run_add, r1, run_add, r2, run_add, r3, run_add, r4, run_add, r5,
    show 2 * A + 2 + 2 * (v + i) = 2 * A + 2 + (2 * (v + i)) from rfl, r6,
    show v + i + 1 = v + (i + 1) from by omega]

def atClockN (A v : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => atClockN A v i + (2 * A + 2 * v + 4 * i + 8)

/-- The rounds invariant. -/
theorem at_run_rounds (A CAP v : ℕ) (hvA : v + A ≤ CAP) (E : List Bool) (i : ℕ)
    (hi : i ≤ A) (s : Bool) :
    run addTMachine (atClockN A v i) ⟨(0, s), 0, cntT A 0 ++ (jT CAP v ++ E)⟩
      = ⟨(0, if i = 0 then s else false), 0, cntT A i ++ (jT CAP (v + i) ++ E)⟩ := by
  induction i with
  | zero => simp only [atClockN]; rw [run_zero]; simp
  | succ i ih =>
    rw [show atClockN A v (i + 1) = atClockN A v i + (2 * A + 2 * v + 4 * i + 8) from rfl,
      run_add, ih (by omega), at_round A CAP v i (by omega) hvA E _, if_neg (by omega),
      show v + (i + 1) = v + i + 1 from by omega]

def atClock (A v : ℕ) : ℕ := atClockN A v A + (2 * A + (2 + (2 * A + 2)))

/-- **E2'S ADDITION PRIMITIVE**: from `unaryD A ++ (jT CAP v ++ E)` the machine halts by itself at
the explicit clock with the accumulator at `v + A` — the addend healed verbatim, the padding
discipline keeping every address fixed. -/
theorem addT_run (A CAP v : ℕ) (hvA : v + A ≤ CAP) (E : List Bool) :
    run addTMachine (atClock A v)
      (init addTMachine (unaryD A ++ (jT CAP v ++ E)))
      = ⟨(11, false), 2 * A + 1, unaryD A ++ (jT CAP (v + A) ++ E)⟩ := by
  rw [init_at,
    show (unaryD A ++ (jT CAP v ++ E) : List Bool)
      = cntT A 0 ++ (jT CAP v ++ E) from by rw [cntT_zero]]
  simp only [atClock]
  have f1 := at_skipBs (cntT A A ++ (jT CAP (v + A) ++ E)) 0 A false
    (fun i hi => ⟨by simpa using cntE_mark_lo A A _ i hi,
                  by simpa using cntE_mark_hi A A _ i hi⟩)
  simp only [Nat.zero_add] at f1
  have f2 := at_doneB (s := if A = 0 then false else true) (p := 2 * A)
    (T := cntT A A ++ (jT CAP (v + A) ++ E))
    (cntE_cm_lo A A _ (le_refl A)) (cntE_cm_hi A A _ (le_refl A))
  have f3 := at_healBs A (jT CAP (v + A) ++ E) false A (le_refl A)
  have f4 := at_doneFin (s := if A = 0 then false else true) (p := 2 * A)
    (T := hlT A A ++ (jT CAP (v + A) ++ E)) (hlE_cm_lo A _)
  rw [run_add, at_run_rounds A CAP v hvA E A (le_refl A) false, ite_self,
    run_add, f1, run_add, f2, ← hlT_zero, run_add, f3, f4, hlT_last]

theorem addT_halt : addTMachine.halt ((11 : Fin 12), false) = true := rfl

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitAddT