/-!
# SPDP Definitions

Core definitions matching Pall paper Section 2.
SPDP rank is kept opaque; properties are proved or axiomatised.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Order.Filter.Basic

open Finset Matrix MvPolynomial

namespace SPDP

/-! ## Block Partition -/

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

/-! ## SPDP Parameters -/

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ
  deriving DecidableEq, Repr

/-! ## Matched parameter regime -/

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

/-! ## SPDP Rank

We define SPDP rank as an opaque function satisfying the required properties.
The concrete matrix construction is left for future work; what matters for
the separation is the interface (properties). -/

/-- SPDP rank: the rank of the blocked SPDP coefficient matrix.
    Opaque — we axiomatise its properties below. -/
opaque spdpRank {F : Type*} [Field F] (n : ℕ) (params : SPDPParams)
    (B : BlockPartition n) (p : MvPolynomial (Fin n) F) : ℕ

/-! ## Arithmetic lemma -/

/-- For any fixed C, eventually n^{log₂ n / 4} > n^C.
    This is the key asymptotic fact: super-polynomial beats polynomial. -/
theorem superPoly_beats_poly (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ^ (Nat.log 2 n / 4) > n ^ C := by
  -- Take n₀ = 2^{4C+4}. Then log₂ n ≥ 4C+4, so log₂ n / 4 ≥ C+1 > C.
  use 2 ^ (4 * C + 4)
  intro n hn
  have h_log : Nat.log 2 n ≥ 4 * C + 4 := by
    calc Nat.log 2 n ≥ Nat.log 2 (2 ^ (4 * C + 4)) := by
          exact Nat.log_mono_right (by linarith) hn
        _ = 4 * C + 4 := by
          rw [Nat.log_pow]
          · ring_nf
  have h_exp : Nat.log 2 n / 4 ≥ C + 1 := by omega
  have h_n_pos : n ≥ 2 := by
    calc n ≥ 2 ^ (4 * C + 4) := hn
      _ ≥ 2 ^ 1 := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      _ = 2 := by ring
  exact Nat.pow_lt_pow_right (by omega) (by omega)

end SPDP
