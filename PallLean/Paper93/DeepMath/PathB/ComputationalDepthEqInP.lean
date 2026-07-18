import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDIndexMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoWayCommFooling

/-!
# EQUALITY is in P: completing the two-way separation

`TwoWayCommFooling` proved the equality function `EQ` needs `≥ n` bits of *two-way* communication.
This file supplies the other half: the equality predicate is decided by a polynomial-time
machine (`eqLang_inP`), so it is a genuine `P`-vs-two-way-communication separation
(`EQ_in_P_but_linear_twoWay`) — a poly-time language whose communication problem requires linear
interactive communication.

The machine `eqMachine` scans a self-delimiting encoding `encPairs` (each bit as a `[T, bit]`
unit, pairs interleaved, an `F` terminator).  It writes nothing, so its tape is fixed
(`tape_unchanged`); the head advances one cell per non-halting step (`hd_eq`, via `step_hd`); and
the padding supplies the terminator, so it halts on *every* input within `|w|+2` steps
(`halts_all`).  On a well-formed encoding it halts with accept bit `allEq` (all pairs equal,
`eq_run`), which on an encoded `(x, y)` is exactly `decide (x = y)` (`eqLang_encFn`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EqInP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (getD_at getD_beyond run_one run_two)
open PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling (EQ eq_leaves_ge RectPartition)

/-! ## The encoding and the machine -/

/-- The self-delimiting pair encoding: each pair `(a, b)` as `[T, a, T, b]`, terminated by `F`. -/
def encPairs : List (Bool × Bool) → List Bool
  | [] => [false]
  | (a, b) :: rest => true :: a :: true :: b :: encPairs rest

/-- Whether all pairs are equal. -/
def allEq (pairs : List (Bool × Bool)) : Bool := pairs.all fun p => p.1 == p.2

theorem allEq_cons (a b : Bool) (rest : List (Bool × Bool)) :
    allEq ((a, b) :: rest) = ((a == b) && allEq rest) := by simp [allEq]

/-- The equality scan machine.  States `0`–`3` scan a `[T,x_i,T,y_i]` block comparing `x_i,y_i`;
`4` halts (accept bit stored). -/
def eqMachine : Machine where
  State := Fin 5 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 4)
  δ := fun s b =>
    if s.1 = 0 then (if b then ((1, s.2), none, 1) else ((4, true), none, 2))
    else if s.1 = 1 then ((2, b), none, 1)
    else if s.1 = 2 then (if b then ((3, s.2), none, 1) else ((4, false), none, 2))
    else if s.1 = 3 then (if b = s.2 then ((0, false), none, 1) else ((4, false), none, 2))
    else ((4, s.2), none, 2)
  accept := fun s => s.2

theorem step_0_T {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step eqMachine ⟨(0, s), p, x⟩ = ⟨(1, s), p + 1, x⟩ := by
  simp only [step, eqMachine, h, moveHead]; rfl

theorem step_0_F {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step eqMachine ⟨(0, s), p, x⟩ = ⟨(4, true), p, x⟩ := by
  simp only [step, eqMachine, h, moveHead]; rfl

theorem step_1 {s : Bool} {p : ℕ} {x : List Bool} :
    step eqMachine ⟨(1, s), p, x⟩ = ⟨(2, x.getD p false), p + 1, x⟩ := by
  simp only [step, eqMachine, moveHead]; rfl

theorem step_2_T {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step eqMachine ⟨(2, s), p, x⟩ = ⟨(3, s), p + 1, x⟩ := by
  simp only [step, eqMachine, h, moveHead]; rfl

theorem step_2_F {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step eqMachine ⟨(2, s), p, x⟩ = ⟨(4, false), p, x⟩ := by
  simp only [step, eqMachine, h, moveHead]; rfl

theorem step_3_eq {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = s) :
    step eqMachine ⟨(3, s), p, x⟩ = ⟨(0, false), p + 1, x⟩ := by
  simp only [step, eqMachine, h, moveHead, if_pos]; rfl

theorem step_3_ne {s : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false ≠ s) :
    step eqMachine ⟨(3, s), p, x⟩ = ⟨(4, false), p, x⟩ := by
  simp only [step, eqMachine, moveHead]
  rw [if_neg h]; rfl

theorem step_4 {s : Bool} {p : ℕ} {x : List Bool} :
    step eqMachine ⟨(4, s), p, x⟩ = ⟨(4, s), p, x⟩ :=
  step_of_halted eqMachine (by rfl)

/-! ## Halting predicate helpers -/

theorem halt_st4 {s : Fin 5 × Bool} (h : eqMachine.halt s = true) : s.1 = 4 := by
  simp only [eqMachine, decide_eq_true_eq] at h; exact h

theorem halt_of_st4 {s : Fin 5 × Bool} (h : s.1 = 4) : eqMachine.halt s = true := by
  simp only [eqMachine, decide_eq_true_eq]; exact h

/-- Every non-halting move of `eqMachine` advances the head (move `1`). -/
theorem delta_move (s : Fin 5 × Bool) (b : Bool) :
    (eqMachine.δ s b).1.1 ≠ 4 → (eqMachine.δ s b).2.2 = 1 := by
  simp only [eqMachine]
  split_ifs <;> first | (intro _; rfl) | (intro h; exact absurd rfl h)

/-! ## The machine never writes -/

theorem eqMachine_no_write (s : Fin 5 × Bool) (b : Bool) : (eqMachine.δ s b).2.1 = none := by
  simp only [eqMachine]
  split_ifs <;> rfl

theorem tape_preserved (c : Cfg eqMachine) : (step eqMachine c).tp = c.tp := by
  unfold step
  by_cases h : eqMachine.halt c.st = true
  · rw [if_pos h]
  · rw [if_neg h]
    show (match (eqMachine.δ c.st (c.tp.getD c.hd false)).2.1 with
      | none => c.tp | some w => writeAt c.tp c.hd w) = c.tp
    rw [eqMachine_no_write]

theorem tape_unchanged (w : List Bool) (t : ℕ) :
    (run eqMachine t (init eqMachine w)).tp = w := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, tape_preserved, ih]

/-! ## One block of the scan -/

/-- **One `[T,a,T,b]` block.**  From state `0` at the block start, four steps compare `a,b`:
match ⟶ back to state `0` past the block; mismatch ⟶ reject.  The tape is untouched. -/
theorem block_step (P rest_tail : List Bool) (a b s : Bool) :
    run eqMachine 4 ⟨(0, s), P.length, P ++ true :: a :: true :: b :: rest_tail⟩
      = if b = a
          then ⟨(0, false), P.length + 4, P ++ true :: a :: true :: b :: rest_tail⟩
          else ⟨(4, false), P.length + 3, P ++ true :: a :: true :: b :: rest_tail⟩ := by
  have g0 : (P ++ true :: a :: true :: b :: rest_tail).getD P.length false = true :=
    getD_at P true _
  have g1 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1) false = a := by
    rw [show P.length + 1 = (P ++ [true]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true]) ++ a :: true :: b :: rest_tail from by simp]
    exact getD_at _ a _
  have g2 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1 + 1) false = true := by
    rw [show P.length + 1 + 1 = (P ++ [true, a]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true, a]) ++ true :: b :: rest_tail from by simp]
    exact getD_at _ true _
  have g3 : (P ++ true :: a :: true :: b :: rest_tail).getD (P.length + 1 + 1 + 1) false = b := by
    rw [show P.length + 1 + 1 + 1 = (P ++ [true, a, true]).length from by simp,
      show P ++ true :: a :: true :: b :: rest_tail
        = (P ++ [true, a, true]) ++ b :: rest_tail from by simp]
    exact getD_at _ b _
  rw [show run eqMachine 4 ⟨(0, s), P.length, P ++ true :: a :: true :: b :: rest_tail⟩
        = step eqMachine (step eqMachine (step eqMachine (step eqMachine
            ⟨(0, s), P.length, P ++ true :: a :: true :: b :: rest_tail⟩))) from rfl,
    step_0_T g0, step_1, g1, step_2_T g2]
  by_cases hba : b = a
  · rw [step_3_eq (by rw [g3]; exact hba), if_pos hba]
  · rw [step_3_ne (by rw [g3]; exact hba), if_neg hba]

/-! ## Semantics on well-formed input -/

/-- **The scan.**  From state `0` at the start of `encPairs pairs`, the machine halts with accept
bit `allEq pairs`. -/
theorem eq_run (pairs : List (Bool × Bool)) : ∀ (P : List Bool),
    ∃ t p, run eqMachine t ⟨(0, false), P.length, P ++ encPairs pairs⟩
      = ⟨(4, allEq pairs), p, P ++ encPairs pairs⟩ := by
  induction pairs with
  | nil =>
    intro P
    refine ⟨1, P.length, ?_⟩
    rw [run_one, show P ++ encPairs [] = P ++ false :: [] from rfl, step_0_F (getD_at P false [])]
    rfl
  | cons ab rest ih =>
    intro P
    obtain ⟨a, b⟩ := ab
    have htape : P ++ encPairs ((a, b) :: rest)
        = P ++ true :: a :: true :: b :: encPairs rest := rfl
    by_cases hba : b = a
    · obtain ⟨t', p', hrec⟩ := ih (P ++ [true, a, true, b])
      refine ⟨4 + t', p', ?_⟩
      rw [run_add, htape, block_step P (encPairs rest) a b false, if_pos hba,
        show P.length + 4 = (P ++ [true, a, true, b]).length from by simp,
        show P ++ true :: a :: true :: b :: encPairs rest
          = (P ++ [true, a, true, b]) ++ encPairs rest from by simp, hrec,
        show allEq ((a, b) :: rest) = allEq rest from by
          rw [allEq_cons, show (a == b) = true from by cases a <;> cases b <;> simp_all,
            Bool.true_and]]
    · refine ⟨4, P.length + 3, ?_⟩
      rw [htape, block_step P (encPairs rest) a b false, if_neg hba,
        show allEq ((a, b) :: rest) = false from by
          rw [allEq_cons, show (a == b) = false from by cases a <;> cases b <;> simp_all,
            Bool.false_and]]

/-! ## Totality -/

/-- A non-halting step advances the head by one. -/
theorem step_hd (c : Cfg eqMachine) (h : (step eqMachine c).st.1 ≠ 4) :
    (step eqMachine c).hd = c.hd + 1 := by
  by_cases hnh : eqMachine.halt c.st = true
  · rw [step_of_halted eqMachine hnh] at h
    exact absurd (halt_st4 hnh) h
  · have st_h : (step eqMachine c).st = (eqMachine.δ c.st (c.tp.getD c.hd false)).1 := by
      unfold step; rw [if_neg hnh]
    have hd_h : (step eqMachine c).hd
        = moveHead c.hd (eqMachine.δ c.st (c.tp.getD c.hd false)).2.2 := by
      unfold step; rw [if_neg hnh]
    rw [st_h] at h
    rw [hd_h, delta_move c.st (c.tp.getD c.hd false) h]
    simp [moveHead]

/-- Below the first halt, the head equals the step count. -/
theorem hd_eq (w : List Bool) : ∀ t, (run eqMachine t (init eqMachine w)).st.1 ≠ 4 →
    (run eqMachine t (init eqMachine w)).hd = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hne
    have hnt : (run eqMachine t (init eqMachine w)).st.1 ≠ 4 := by
      intro h4
      apply hne
      rw [run_succ, step_of_halted eqMachine (halt_of_st4 h4)]
      exact h4
    rw [run_succ] at hne ⊢
    rw [step_hd (run eqMachine t (init eqMachine w)) hne, ih hnt]

/-- From any padding configuration the machine is halted within two steps. -/
theorem pad_halt (s : Fin 5 × Bool) (p : ℕ) (w : List Bool)
    (h0 : w.getD p false = false) (h1 : w.getD (p + 1) false = false) :
    eqMachine.halt (run eqMachine 2 ⟨s, p, w⟩).st = true := by
  obtain ⟨q, sb⟩ := s
  match q with
  | 0 => rw [run_two, step_0_F h0, step_4]; rfl
  | 1 => rw [run_two, step_1, step_2_F h1]; rfl
  | 2 => rw [run_two, step_2_F h0, step_4]; rfl
  | 3 =>
    rw [run_two]
    by_cases hb : w.getD p false = sb
    · rw [step_3_eq hb, step_0_F h1]; rfl
    · rw [step_3_ne hb, step_4]; rfl
  | 4 => rw [run_two, step_4, step_4]; rfl

/-- **Totality.**  The machine halts on every input within `|w| + 2` steps. -/
theorem halts_all (w : List Bool) : HaltsBy eqMachine w (w.length + 2) := by
  by_cases hh : eqMachine.halt (run eqMachine w.length (init eqMachine w)).st = true
  · show eqMachine.halt (run eqMachine (w.length + 2) (init eqMachine w)).st = true
    rw [run_stable eqMachine w (by omega) hh]; exact hh
  · have hne : (run eqMachine w.length (init eqMachine w)).st.1 ≠ 4 := fun h4 =>
      hh (halt_of_st4 h4)
    have hhd := hd_eq w w.length hne
    have htp := tape_unchanged w w.length
    have key := pad_halt (run eqMachine w.length (init eqMachine w)).st
      (run eqMachine w.length (init eqMachine w)).hd
      (run eqMachine w.length (init eqMachine w)).tp
      (by rw [htp, hhd]; exact getD_beyond w w.length (le_refl _))
      (by rw [htp, hhd]; exact getD_beyond w (w.length + 1) (by omega))
    show eqMachine.halt (run eqMachine (w.length + 2) (init eqMachine w)).st = true
    rw [run_add]
    exact key

/-! ## The language is in P -/

/-- The language decided by `eqMachine`. -/
noncomputable def eqLang (w : List Bool) : Bool := decideOut eqMachine w (w.length + 2)

/-- **EQUALITY is in P.** -/
theorem eqLang_inP : InP eqLang :=
  ⟨eqMachine, fun m => m + 2, ⟨3, 1, fun n => by
    show n + 2 ≤ 3 * (n + 1) ^ 1
    have : (n + 1) ^ 1 = n + 1 := pow_one _
    omega⟩, fun w => ⟨halts_all w, rfl⟩⟩

/-- On a well-formed encoding, the language is `allEq`: all interleaved pairs are equal. -/
theorem eqLang_enc (pairs : List (Bool × Bool)) : eqLang (encPairs pairs) = allEq pairs := by
  obtain ⟨t, p, hrun⟩ := eq_run pairs []
  simp only [List.length_nil, List.nil_append] at hrun
  show decideOut eqMachine (encPairs pairs) ((encPairs pairs).length + 2) = allEq pairs
  unfold decideOut
  rcases le_total t ((encPairs pairs).length + 2) with hle | hle
  · rw [run_stable eqMachine (encPairs pairs) hle
      (by show eqMachine.halt (run eqMachine t ⟨(0, false), 0, encPairs pairs⟩).st = true
          rw [hrun]; rfl)]
    show eqMachine.accept (run eqMachine t ⟨(0, false), 0, encPairs pairs⟩).st = allEq pairs
    rw [hrun]; rfl
  · rw [← run_stable eqMachine (encPairs pairs) hle (halts_all (encPairs pairs))]
    show eqMachine.accept (run eqMachine t ⟨(0, false), 0, encPairs pairs⟩).st = allEq pairs
    rw [hrun]; rfl

/-! ## The bridge to EQUALITY and the separation -/

/-- `allEq` of a zipped pair of equal-length lists decides list equality. -/
theorem allEq_zip : ∀ a b : List Bool, a.length = b.length → allEq (a.zip b) = decide (a = b)
  | [], [], _ => rfl
  | x :: a, y :: b, hlen => by
    have hlen' : a.length = b.length := by simpa using hlen
    show allEq ((x, y) :: a.zip b) = decide (x :: a = y :: b)
    rw [allEq_cons, allEq_zip a b hlen']
    cases x <;> cases y <;> simp [List.cons.injEq]

/-- The encoded-input bridge: on the interleaved encoding of `(x, y)`, the language is exactly
`x = y`. -/
theorem eqLang_encFn {n : ℕ} (x y : Fin n → Bool) :
    eqLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = EQ n x y := by
  rw [eqLang_enc, allEq_zip _ _ (by simp)]
  show decide (List.ofFn x = List.ofFn y) = decide (x = y)
  rw [decide_eq_decide.mpr List.ofFn_inj]

/-- **EQUALITY: in P, but linear two-way communication.**  The equality predicate is decided in
polynomial time (`eqLang_inP`), yet its communication function `EQ` needs `≥ 2^n` protocol leaves
(`eq_leaves_ge`) — `≥ n` bits of two-way interactive communication.  Polynomial time does not
imply sublinear two-way communication. -/
theorem EQ_in_P_but_linear_twoWay :
    InP eqLang
      ∧ (∀ (n : ℕ) (x y : Fin n → Bool),
          eqLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = EQ n x y)
      ∧ ∀ (n k : ℕ), RectPartition (EQ n) k → 2 ^ n ≤ k :=
  ⟨eqLang_inP, fun _ x y => eqLang_encFn x y, fun n k R => eq_leaves_ge n k R⟩

end PallLean.Paper93.DeepMath.PathB.EqInP
