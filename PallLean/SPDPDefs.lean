import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# SPDP Definitions — Paper-Faithful (Pall §2)

SPDP rank defined faithfully following Definition 2.1–2.3 of the paper.

**Definition 2.1 (SPDP matrix).** A row of M_{κ,ℓ}(f) is indexed by (S, m)
where S ⊆ [N] with |S| = κ and m is a monomial with deg(m) ≤ ℓ.
The row vector is the coefficient vector of m · ∂_S f.

**Definition 2.2 (SPDP rank).** Γ_{κ,ℓ}(f) := rank(M_{κ,ℓ}(f)).

The rank of this matrix equals the dimension of the F-span of
{ m · ∂_S f : |S| = κ, deg(m) ≤ ℓ } in the polynomial ring,
so we define it as Module.finrank of that span.

**Definition 2.3 (Blocked SPDP rank).** ΓB_{κ,ℓ}(f) restricts rows to
block-admissible (S, m) pairs. We model this with a `BlockPartition`
predicate and a separate `blockedSpdpRank`.
-/

namespace SPDP

open MvPolynomial

/-! ## Block Partitions (Definition 2.3) -/

/-- A block partition of [n] into r blocks -/
structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

/-- S is block-admissible: |S ∩ B_i| ≤ 1 for each block (i.e. S is a transversal) -/
def isBlockAdmissible {n : ℕ} (B : BlockPartition n) (S : List (Fin n)) : Prop :=
  S.Nodup ∧ ∀ b : Fin B.numBlocks, (S.filter (fun i => B.assign i = b)).length ≤ 1

/-! ## SPDP Parameters -/

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

/-! ## Iterated Partial Derivatives -/

/-- Iterated partial derivative along a list of variable indices -/
noncomputable def iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-! ## SPDP Subspace and Rank (Definitions 2.1–2.2) -/

/-- The (unblocked) SPDP subspace at parameters (κ, ℓ):
    V_{κ,ℓ}(f) = span_F { m · ∂_S f : |S| = κ, deg(m) ≤ ℓ }

    When ℓ = 0, only the identity monomial m=1 is allowed,
    recovering the pure shifted-partial-derivative space V_κ(f).

    The paper's SPDP rank Γ_{κ,ℓ}(f) is the dimension of this space,
    which equals the matrix rank of the coefficient matrix M_{κ,ℓ}(f). -/
noncomputable def spdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        q = m * iterDerivList S p }

/-- (Unblocked) SPDP rank Γ_{κ,ℓ}(f) = dim V_{κ,ℓ}(f) (Definition 2.2) -/
noncomputable def spdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (spdpSubspace κ ℓ p)

/-- The blocked SPDP subspace VB_{κ,ℓ}(f) restricts to block-admissible rows:
    VB_{κ,ℓ}(f) = span_F { m · ∂_S f : |S| = κ, deg(m) ≤ ℓ, (S,m) block-admissible }

    By Proposition 2.4: ΓB ≤ Γ (submatrix ⇒ rank monotonicity). -/
noncomputable def blockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S p }

/-- Blocked SPDP rank ΓB_{κ,ℓ}(f) (Definition 2.3) -/
noncomputable def blockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (blockedSpdpSubspace B κ ℓ p)

/-! ## Basic Properties -/

/-- Proposition 2.4: VB ≤ V (blocked subspace ≤ unblocked) -/
theorem blockedSubspace_le {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpSubspace B κ ℓ p ≤ spdpSubspace κ ℓ p := by
  apply Submodule.span_mono
  intro q ⟨S, m, hlen, hdeg, _, hq⟩
  exact ⟨S, m, hlen, hdeg, hq⟩

theorem foldl_pderiv_zero {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) :
    List.foldl (fun (q : MvPolynomial (Fin n) F) i => pderiv i q) 0 indices = 0 := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [List.foldl_cons, map_zero]; exact ih

/-! ## Arithmetic (Theorem 19.1 step) -/

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
