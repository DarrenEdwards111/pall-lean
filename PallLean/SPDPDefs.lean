import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# SPDP Definitions — Concrete

SPDP rank defined concretely as the dimension of the SPDP subspace.
No opaque definitions — everything is transparent for proving properties.
-/

namespace SPDP

open MvPolynomial

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

/-! ## Concrete SPDP rank -/

/-- Iterated partial derivative along a list of variable indices -/
noncomputable def iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-- The SPDP subspace V_{κ}(p) = span{ m · ∂_S p : |S| = κ } -/
noncomputable def spdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (indices : List (Fin n)) (m : MvPolynomial (Fin n) F),
        indices.length = κ ∧ q = m * iterDerivList indices p }

/-- SPDP rank = dimension of V_{κ}(p) -/
noncomputable def spdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (spdpSubspace κ p)

/-! ## foldl_pderiv_zero -/

theorem foldl_pderiv_zero {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) :
    List.foldl (fun (q : MvPolynomial (Fin n) F) i => pderiv i q) 0 indices = 0 := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [List.foldl_cons, map_zero]; exact ih

/-! ## Arithmetic -/

theorem superPoly_beats_poly (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ^ (Nat.log 2 n / 4) > n ^ C := by
  use 2 ^ (4 * C + 4)
  intro n hn
  apply Nat.pow_lt_pow_right
  · have : (2 : ℕ) ^ 1 ≤ 2 ^ (4 * C + 4) := by
      apply Nat.pow_le_pow_right (by norm_num); omega
    omega
  · have h_log : Nat.log 2 n ≥ 4 * C + 4 := by
      have : 2 ^ (4 * C + 4) ≤ n := hn
      calc 4 * C + 4
          = Nat.log 2 (2 ^ (4 * C + 4)) := by
            rw [Nat.log_pow (by norm_num : 1 < 2)]
        _ ≤ Nat.log 2 n := Nat.log_mono_right this
    omega

end SPDP
