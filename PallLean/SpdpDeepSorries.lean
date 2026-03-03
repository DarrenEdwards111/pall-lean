/-
  SpdpDeepSorries.lean — Statement objects + proved LA lemmas for Pall §3-12
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open scoped BigOperators

namespace SpdpDeepSorries

/-! ## Abstract SPDP interface -/

class PolyLike (P : Type*) extends CommSemiring P where
  GammaB : ℕ → ℕ → P → ℕ

abbrev Statement := Prop

/-! ## 5 statement objects -/

def kappa_padding_rank_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (Y V : P) : Statement :=
  (PolyLike.GammaB κ ℓ (Y * V)) ≤
    (Finset.range (κ + 1)).sum (fun r => (Nat.choose κ r) * PolyLike.GammaB r ℓ V)

def width_to_rank_bound_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (p : P) (G w : ℕ) : Statement :=
  PolyLike.GammaB κ ℓ p ≤ (G * w) ^ 3

def identity_minor_lower_bound_stmt {P : Type*} [PolyLike P]
    (κ ℓ L : ℕ) (Qx : P) : Statement :=
  Nat.choose L κ ≤ PolyLike.GammaB κ ℓ Qx

def extraction_rank_monotone_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (Qx pMN : P) : Statement :=
  PolyLike.GammaB κ ℓ Qx ≤ PolyLike.GammaB κ ℓ pMN

def binomial_lower_bound_stmt (n : ℕ) : Statement :=
  Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4)

structure FiveDeepSorriesBundle : Type where
  Lemma3_1 : Statement
  Thm5_16 : Statement
  Thm9_3 : Statement
  Thm12_2 : Statement
  BinomLB : Statement

/-! ## Proved: Matrix rank lemmas for Thm 9.3 and Thm 12.2 -/

section MatrixRank

variable {R : Type*} [Field R]

/-- rank(1) = card n — identity matrix has full rank -/
theorem identity_rank {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.rank (1 : Matrix n n R) = Fintype.card n :=
  Matrix.rank_one

/-- Reindexing preserves rank exactly -/
theorem rank_reindex_eq {m n m₀ n₀ : Type*}
    [Fintype m] [Fintype n] [Fintype m₀] [Fintype n₀]
    [DecidableEq m₀] [DecidableEq n₀]
    (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    Matrix.rank (A.submatrix em en) = Matrix.rank A :=
  Matrix.rank_submatrix A em en

/-- Submatrix rank ≤ original rank (when row map is equiv).
    This is the backbone of extraction rank monotonicity. -/
theorem rank_submatrix_le' {m n m₀ n₀ : Type*}
    [Fintype m] [Fintype n] [Fintype m₀] [Fintype n₀]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix n m R) (f : n₀ → n) (e : m₀ ≃ m) :
    Matrix.rank (A.submatrix f e) ≤ Matrix.rank A :=
  Matrix.rank_submatrix_le f e A

/-- Identity minor → rank ≥ k.
    If A has a k×k submatrix equal to the identity (via equiv on rows),
    then rank(A) ≥ k. -/
theorem rank_ge_of_identity_minor {F : Type*} [Field F]
    {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix m n F) (er : k ≃ m) (g : k → n)
    (hid : A.submatrix er g = 1) :
    Fintype.card k ≤ Matrix.rank A := by
  calc Fintype.card k
      = Matrix.rank (1 : Matrix k k F) := (Matrix.rank_one).symm
    _ = Matrix.rank (A.submatrix er g) := by rw [hid]
    _ = Matrix.rank (A.submatrix er g).transpose := (Matrix.rank_transpose _).symm
    _ = Matrix.rank (A.transpose.submatrix g er) := by rw [Matrix.transpose_submatrix]
    _ ≤ Matrix.rank A.transpose := Matrix.rank_submatrix_le g er A.transpose
    _ = Matrix.rank A := Matrix.rank_transpose A

set_option maxHeartbeats 800000 in
/-- Simpler version: identity minor with Fin k embedding -/
theorem rank_ge_card_of_identity_submatrix {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (k : ℕ) (A : Matrix m n R)
    (f : Fin k → m) (g : Fin k → n)
    (hf : Function.Injective f)
    (hid : ∀ i j : Fin k, A (f i) (g j) = if i = j then 1 else 0) :
    k ≤ Matrix.rank A := by
  -- Embed Fin k into m via f, extend to an equiv on the range
  -- Then use the proved rank_ge_of_identity_minor
  -- Strategy: construct a larger matrix B : Matrix (Fin k) n R with B i j = A (f i) j
  -- Show B = A.submatrix f id, rank(B) ≤ rank(A), and B has identity minor
  let B := A.submatrix f id
  have hB : ∀ i j : Fin k, B i (g j) = if i = j then 1 else 0 := by
    intro i j; exact hid i j
  -- B.submatrix id g = 1
  have hBsub : B.submatrix (Equiv.refl _) g = 1 := by
    funext i j
    show A (f i) (g j) = (1 : Matrix (Fin k) (Fin k) _) i j
    rw [Matrix.one_apply]
    exact hid i j
  have hrank_B : Fintype.card (Fin k) ≤ Matrix.rank B := by
    exact rank_ge_of_identity_minor B (Equiv.refl _) g hBsub
  simp [Fintype.card_fin] at hrank_B
  -- rank(B) = rank(A.submatrix f id) ≤ rank(A)
  have hle : Matrix.rank B ≤ Matrix.rank A :=
    Matrix.rank_submatrix_le f (Equiv.refl _) A
  exact le_trans hrank_B hle

end MatrixRank

end SpdpDeepSorries
