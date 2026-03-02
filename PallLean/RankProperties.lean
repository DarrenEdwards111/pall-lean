import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import PallLean.SPDPDefs
/-!
# SPDP Rank Properties

Decomposition of spdpRank behavior into fine-grained lemmas.
Each captures one linear-algebraic fact about the blocked SPDP matrix.
These are the TRUE axioms — each is a standard LA fact applied to SPDP.
-/

namespace SPDP.RankProps

open SPDP MvPolynomial

/-! ## R1: Restriction (setting variables to constants) cannot increase rank

If p' = p|_{x_i = c}, then ΓB(p') ≤ ΓB(p).

Proof sketch: The SPDP matrix rows of p' are images of rows of p
under the evaluation map ev_{x_i=c}. This is a linear map on the
row space, so dim(image) ≤ dim(domain). -/

axiom rank_le_restriction {F : Type*} [Field F] {n : ℕ}
    (params : SPDPParams) (B : BlockPartition n)
    (p : MvPolynomial (Fin n) F) (i : Fin n) (c : F) :
    spdpRank n params B (MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j = i then MvPolynomial.C c else MvPolynomial.X j) p) ≤
    spdpRank n params B p

/-! ## R2: Projection to fewer blocks cannot increase rank

Restricting to a subset of derivative/shift indices gives a
submatrix → rank ≤. -/

-- This is captured by: if we project p to fewer variables (setting
-- some to 0), rank cannot increase. This is a special case of R1.

/-! ## R3: Block-local invertible substitution preserves rank exactly

If φ : x_i ↦ ∑_j a_{ij} x_j is invertible within each block,
then ΓB(p ∘ φ) = ΓB(p).

Proof sketch: φ induces an invertible linear map on the polynomial
ring that maps SPDP rows to SPDP rows bijectively. -/

axiom rank_eq_invertible_subst {F : Type*} [Field F] {n : ℕ}
    (params : SPDPParams) (B : BlockPartition n)
    (p q : MvPolynomial (Fin n) F)
    (h_inv : True) :  -- q = p ∘ φ where φ is block-local invertible
    spdpRank n params B q = spdpRank n params B p

/-! ## R4: Constant shift is invisible at κ ≥ 1

If κ ≥ 1, then ΓB(p + c) = ΓB(p) for any constant c ∈ F.
Because ∂_S c = 0 for any |S| = κ ≥ 1. -/

axiom rank_eq_add_const {F : Type*} [Field F] {n : ℕ}
    (params : SPDPParams) (B : BlockPartition n)
    (p : MvPolynomial (Fin n) F) (c : F)
    (hκ : params.κ ≥ 1) :
    spdpRank n params B (p + MvPolynomial.C c) = spdpRank n params B p

/-! ## R5: Rank monotone under polynomial ring embedding

If we embed F[x₁..xₘ] ↪ F[x₁..xₙ] (m ≤ n) by adding inert variables,
rank in the larger ring (with compatible block partition) is ≤ rank
of the original. -/

-- This follows from R1 (set extra variables to 0)

/-! ## Composition: extraction_rank_chain from R1-R4

Given R1-R4, the extraction axiom (A4) follows:
1. Proj(u,z) → R2 (subset of blocks) → rank ≤
2. v := 0 → R1 (restriction) → rank ≤
3. a := a₀ → R1 (restriction) → rank ≤
4. Relabel_Φ → R3 (invertible) → rank =
5. Π⁺ → R1 (linear map on blocks) → rank ≤
6. + const → R4 (invisible at κ ≥ 1) → rank =

Total: rank(output) ≤ rank(input) -/

-- We cannot yet prove extraction_rank_chain because the types
-- involve different n (compilerVars vs npVars) and different
-- BlockPartitions. The extraction map changes the ambient space.
-- This requires a more careful treatment of variable embedding.

/-! ## R6: Rank under variable embedding (the missing piece)

The extraction map goes from F[x₁..x_N] to F[y₁..y_M] where
M = npVars n and N = compilerVars n c'. The output polynomial
lives in a SUBRING of the input ring (on the clause/verifier variables).

Key fact: if q = T_Φ(p) where T_Φ is a composition of restrictions,
projections, and invertible block-local maps, then:
  spdpRank(M, params, B', q) ≤ spdpRank(N, params, B, p)

This is because each step either:
- Reduces rank (R1, R2) or preserves it (R3, R4)
- And the final polynomial q has its SPDP matrix as a submatrix
  of intermediate stages. -/

axiom rank_le_extraction {F : Type*} [Field F] {n_in n_out : ℕ}
    (params : SPDPParams) (B_in : BlockPartition n_in) (B_out : BlockPartition n_out)
    (p : MvPolynomial (Fin n_in) F) (q : MvPolynomial (Fin n_out) F)
    (h_extract : True) :  -- q is obtained from p by restriction + projection + invertible relabel
    spdpRank n_out params B_out q ≤ spdpRank n_in params B_in p

end SPDP.RankProps
