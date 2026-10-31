import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqInP
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The log-rank two-way lower bound (a fifth technique)

A *fifth* communication-complexity technique for the two-way regime: the **rank method**.  The
communication matrix `M_f` (entry `f x y` over `ℝ`) factors through the `k` leaves of any
deterministic protocol as `M_f = A · D` with `A : α × Fin k`, so its rank is at most the number of
leaves (`rank_le_leaves`).  Hence any protocol needs `≥ rank(M_f)` leaves — the **log-rank lower
bound** `D(f) ≥ log₂ rank(M_f)`.

The witness is again EQUALITY, but caught by a genuinely different invariant: its communication
matrix is the **identity** (`commMatrix_EQ`), whose rank is `2^n` (`rank_one`).  So EQUALITY needs
`≥ 2^n` leaves — recovering the two-way bound of `TwoWayCommFooling` via linear algebra instead of
fooling sets.  Combined with `eqLang ∈ P`, this is a `P`-vs-two-way separation by the rank method
(`P_not_sublinear_twoWay_rank`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RankTwoWay

open Finset
open PallLean.Paper93.DeepMath.PathB.ComposableMachine (InP)
open PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling (EQ RectPartition)
open PallLean.Paper93.DeepMath.PathB.EqInP (eqLang eqLang_inP eqLang_encFn encPairs)

variable {α β : Type} [Fintype α] [Fintype β]

/-- The communication matrix of `f` over `ℝ`. -/
noncomputable def commMatrix (f : α → β → Bool) : Matrix α β ℝ := fun x y => if f x y then 1 else 0

/-- **The rank lower bound.**  The communication matrix factors through the `k` leaves of any
protocol, so its rank is at most `k`: on leaf `i` (a rectangle `a_i × b_i` with constant value
`v_i`), `M_f = ∑_i v_i · a_i b_iᵀ`, i.e. `M_f = A · D` with `A` of width `k`. -/
theorem rank_le_leaves (f : α → β → Bool) (k : ℕ) (R : RectPartition f k) :
    (commMatrix f).rank ≤ k := by
  classical
  by_cases hαβ : Nonempty (α × β)
  · -- representative of each nonempty leaf
    set rep : Fin k → α × β :=
      fun i => if h : ∃ p : α × β, R.leaf p.1 p.2 = i then h.choose else hαβ.some with hrep_def
    have hrep : ∀ i, (∃ p : α × β, R.leaf p.1 p.2 = i) → R.leaf (rep i).1 (rep i).2 = i := by
      intro i hi
      rw [hrep_def]
      simp only [dif_pos hi]
      exact hi.choose_spec
    set A : Matrix α (Fin k) ℝ :=
      fun x i => if R.leaf x (rep i).2 = i then 1 else 0 with hA_def
    set D : Matrix (Fin k) β ℝ :=
      fun i y => (if f (rep i).1 (rep i).2 then (1 : ℝ) else 0)
                  * (if R.leaf (rep i).1 y = i then 1 else 0) with hD_def
    have hAD : commMatrix f = A * D := by
      ext x y
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (R.leaf x y)]
      · -- the diagonal term
        have hne : R.leaf (rep (R.leaf x y)).1 (rep (R.leaf x y)).2 = R.leaf x y :=
          hrep _ ⟨(x, y), rfl⟩
        have hax : R.leaf x (rep (R.leaf x y)).2 = R.leaf x y :=
          (R.rect x y (rep (R.leaf x y)).1 (rep (R.leaf x y)).2 (by rw [hne])).1
        have hdy : R.leaf (rep (R.leaf x y)).1 y = R.leaf x y :=
          (R.rect x y (rep (R.leaf x y)).1 (rep (R.leaf x y)).2 (by rw [hne])).2
        have hfv : f (rep (R.leaf x y)).1 (rep (R.leaf x y)).2 = f x y :=
          R.mono (rep (R.leaf x y)).1 (rep (R.leaf x y)).2 x y (by rw [hne])
        simp only [hA_def, hD_def, hax, hdy, hfv]
        simp [commMatrix]
      · -- off-diagonal terms vanish
        intro i _ hi
        simp only [hA_def, hD_def]
        by_cases hxi : R.leaf x (rep i).2 = i
        · by_cases hyi : R.leaf (rep i).1 y = i
          · exfalso
            exact hi (((R.rect x (rep i).2 (rep i).1 y (by rw [hxi, hyi])).1).trans hxi).symm
          · simp [hyi]
        · simp [hxi]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hAD]
    calc (A * D).rank ≤ A.rank := Matrix.rank_mul_le_left A D
      _ ≤ Fintype.card (Fin k) := Matrix.rank_le_card_width A
      _ = k := Fintype.card_fin k
  · rw [not_nonempty_iff] at hαβ
    rcases isEmpty_prod.mp hαβ with h | h
    · calc (commMatrix f).rank ≤ Fintype.card α := Matrix.rank_le_card_height _
        _ = 0 := Fintype.card_eq_zero
        _ ≤ k := Nat.zero_le k
    · calc (commMatrix f).rank ≤ Fintype.card β := Matrix.rank_le_card_width _
        _ = 0 := Fintype.card_eq_zero
        _ ≤ k := Nat.zero_le k

/-! ## EQUALITY -/

/-- EQUALITY's communication matrix is the identity. -/
theorem commMatrix_EQ (n : ℕ) : commMatrix (EQ n) = (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  ext x y
  by_cases h : x = y <;> simp [commMatrix, EQ, Matrix.one_apply, h]

/-- EQUALITY's communication matrix has rank `2^n`. -/
theorem rank_commMatrix_EQ (n : ℕ) : (commMatrix (EQ n)).rank = 2 ^ n := by
  rw [commMatrix_EQ, Matrix.rank_one, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **EQUALITY needs `≥ 2^n` leaves, by rank.**  A second, linear-algebraic proof of the two-way
bound: any protocol has `≥ rank = 2^n` leaves. -/
theorem eq_rank_ge (n k : ℕ) (R : RectPartition (EQ n) k) : 2 ^ n ≤ k := by
  have := rank_le_leaves (EQ n) k R
  rwa [rank_commMatrix_EQ] at this

/-- **EQUALITY has two-way communication complexity `≥ n`, by log-rank.** -/
theorem eq_logrank_ge (n k : ℕ) (R : RectPartition (EQ n) k) : n ≤ Nat.log 2 k := by
  have hk : 2 ^ n ≤ k := eq_rank_ge n k R
  calc n = Nat.log 2 (2 ^ n) := (Nat.log_pow Nat.one_lt_two n).symm
    _ ≤ Nat.log 2 k := Nat.log_mono_right hk

/-- **P ⊄ sublinear two-way communication, by the rank method.**  `eqLang ∈ P`, and by the
log-rank bound every deterministic two-way protocol for the length-`n` equality problem uses `≥ n`
bits — a fifth technique (rank), independent of fooling sets, giving the same separation. -/
theorem P_not_sublinear_twoWay_rank :
    InP eqLang
      ∧ (∀ (n : ℕ) (x y : Fin n → Bool),
          eqLang (encPairs ((List.ofFn x).zip (List.ofFn y))) = EQ n x y)
      ∧ ∀ (n k : ℕ), RectPartition (EQ n) k → n ≤ Nat.log 2 k :=
  ⟨eqLang_inP, fun _ x y => eqLang_encFn x y, fun n k R => eq_logrank_ge n k R⟩

end PallLean.Paper93.DeepMath.PathB.RankTwoWay
