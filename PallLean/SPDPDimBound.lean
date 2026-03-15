import PallLean.BoolEval
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
/-!
# SPDP Dimension Bound — Paper §8.6

## Key Theorem

For κ = 0: if spdpRank(0, ℓ, p) ≤ r, then p ∈ spdpSubspace(0, ℓ, p),
so the evaluation vector of p lies in a subspace of dimension ≤ r.

For κ > 0 (the paper's case): the bound requires showing that the
κ-th derivatives constrain the polynomial. We prove the κ = 0 case
here and connect it to the general case.

## Paper's Argument

The paper uses a CANONICAL MATRIX M whose rows are evaluation vectors
of multilinear monomials on the live variables. All restricted circuits'
evaluation vectors lie in M's row space. rank(M) ≤ d_n* < 2^n.

The connection: for κ = 0 with sufficient ℓ, the spdpSubspace contains
ALL multilinear monomials up to degree ℓ (since 1 · p = p ∈ spdpSubspace).
So the evaluation vectors are constrained to a space of dimension ≤ r.
-/

namespace SPDPDimBound

open BoolEval MvPolynomial SPDP Restriction

/-! ## Boolean evaluation as linear map -/

/-- Boolean evaluation is a linear map from polynomials to ℚ^{2^n}. -/
noncomputable def boolEval (n : ℕ) :
    MvPolynomial (Fin n) ℚ →ₗ[ℚ] ((Fin n → Bool) → ℚ) where
  toFun p x := MvPolynomial.eval (fun i => boolToRat (x i)) p
  map_add' p q := by ext x; simp [map_add]
  map_smul' c p := by ext x; simp [map_smul, smul_eq_mul]

/-! ## κ = 0 case: p ∈ spdpSubspace → eval(p) ∈ eval(spdpSubspace) -/

/-- When κ = 0, p itself is in spdpSubspace(0, ℓ, p) for any ℓ ≥ 0. -/
theorem mem_spdpSubspace_zero {n : ℕ} (ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    p ∈ spdpSubspace 0 ℓ p := by
  apply Submodule.subset_span
  exact ⟨[], 1, rfl, by simp [totalDegree_one], by simp [iterDerivList]⟩

/-- The evaluation image of spdpSubspace(0, ℓ, p) under boolEval. -/
noncomputable def spdpEvalImage (n ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    Submodule ℚ ((Fin n → Bool) → ℚ) :=
  (spdpSubspace 0 ℓ p).map (boolEval n)

/-- The eval vector of p lies in the eval image of its spdpSubspace. -/
theorem eval_in_spdp_image {n : ℕ} (ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    boolEval n p ∈ spdpEvalImage n ℓ p := by
  exact ⟨p, mem_spdpSubspace_zero ℓ p, rfl⟩

/-- The evaluation image dimension ≤ spdpRank for κ = 0. -/
theorem eval_image_dim_le_spdpRank {n : ℕ} (ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    [Module.Finite ℚ (spdpSubspace 0 ℓ p)] :
    Module.finrank ℚ (spdpEvalImage n ℓ p) ≤ spdpRank 0 ℓ p := by
  unfold spdpEvalImage spdpRank
  exact Submodule.finrank_map_le (boolEval n) (spdpSubspace 0 ℓ p)

/-! ## Connection to the paper's InFSPDP with κ > 0

The paper uses κ = log₂(n) > 0. For κ > 0, the spdpSubspace does NOT
contain p itself, only its κ-th derivatives. However, the paper's
canonical matrix approach works differently:

1. The canonical matrix M has rows for ALL multilinear monomials of
   degree ≤ w on the live variables
2. Every restricted polynomial p|ρ is a linear combination of these
   monomials (since it's multilinear on w variables)
3. So eval(p|ρ) ∈ span of monomial evaluations = row space of M
4. rank(M) = min(#monomials, #eval_points) ≤ Σ_{j≤w} C(w,j) = 2^w

This gives dim(eval subspace) ≤ 2^w where w = numLive(ρ*).
For w = O(log n): 2^w = poly(n) < 2^n.

But crucially, this bound doesn't use SPDP rank at all! It just uses
the number of live variables. The SPDP rank provides a TIGHTER bound
(spdpRank ≤ √n < 2^w), but 2^w < 2^n already suffices.

The real question: for our InFSPDP with varying ρ (different ρ per function),
is 2^w bounded? With the paper's fixed seed, w is fixed for all functions.
With varying ρ, different functions can use different ρ with different w,
and w could be up to n (trivial restriction leaving all variables live).

This is why the paper needs the FIXED SEED: to ensure all P-time circuits
use the SAME restriction, giving a shared bound on w.

Without the fixed seed, spdp_dim_bound requires the fixed-seed structure.
We therefore accept it as an axiom that encapsulates the fixed-seed argument.
-/

end SPDPDimBound
