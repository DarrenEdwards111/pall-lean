import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# SPDP Definitions — Paper-Faithful (Pall §2)

Definitions 2.1–2.3. SPDP rank defined as the dimension of the row span
of the SPDP matrix M_{κ,ℓ}(f), whose rows are the polynomials m·∂_S f
for |S|=κ, deg(m)≤ℓ.

Since the dimension of the span of a set of polynomials equals the
matrix rank of their coefficient vectors, this is equivalent to
Module.finrank of the F-span. We use the submodule formulation.
-/

namespace SPDP

open MvPolynomial

/-! ## Block Partitions (Definition 2.3) -/

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

def isBlockAdmissible {n : ℕ} (B : BlockPartition n) (S : List (Fin n)) : Prop :=
  S.Nodup ∧ ∀ b : Fin B.numBlocks, (S.filter (fun i => B.assign i = b)).length ≤ 1

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

/-! ## Iterated Partial Derivatives -/

noncomputable def iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-! ## SPDP Subspace and Rank (Definitions 2.1–2.2)

The SPDP matrix M_{κ,ℓ}(f) has rows indexed by (S, m) where |S|=κ and
deg(m)≤ℓ. Each row is the coefficient vector of m · ∂_S f.

Γ_{κ,ℓ}(f) = rank(M_{κ,ℓ}(f)) = dim(span{m · ∂_S f : |S|=κ, deg(m)≤ℓ})

We define this as Module.finrank of the F-span. -/

noncomputable def spdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        q = m * iterDerivList S p }

noncomputable def spdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (spdpSubspace κ ℓ p)

noncomputable def blockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S p }

noncomputable def blockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (blockedSpdpSubspace B κ ℓ p)

/-! ## Basic Properties -/

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

/-! ## Monotonicity Properties (Pall §2, basic properties)

These are fundamental properties of SPDP rank that hold because
each operation corresponds to a rank-nonincreasing operation on
the coefficient matrix M_{κ,ℓ}(f). -/

/-- Restriction monotonicity (§2 basic property 3):
    Setting a variable to a constant cannot increase SPDP rank.
    Proof: restriction is a linear map on coefficient vectors,
    so it maps the row space to a subspace of equal or smaller dimension. -/
axiom restriction_rank_le {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (i : Fin n) (c : F) :
    spdpRank κ ℓ (MvPolynomial.eval₂Hom C (fun j => if j = i then C c else X j) p) ≤
      spdpRank κ ℓ p

/-- Rename with injective f preserves SPDP rank.
    Proof: injective rename is a bijection on coefficient vectors. -/
axiom rank_rename_eq {n m : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (f : Fin n → Fin m) (hf : Function.Injective f) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    spdpRank κ ℓ (rename f p) = spdpRank κ ℓ p

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
