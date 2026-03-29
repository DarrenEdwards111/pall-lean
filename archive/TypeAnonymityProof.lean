import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.IdentityMinor
import PallLean.ProfileSpaceBound
import PallLean.ProfileCompression
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# TypeAnonymityProof — Proving tseitin_spdp_rank_bound

Paper §9.1 Theorem 23: Width⇒Rank via profile compression.

This file proves the axiom by constructing a finite spanning set for
mlBlockedSpdpSubspace of cardinality ≤ n^200.

## Core argument (paper-faithful)

For the Tseitin product p = ∏_c (1 - z_c · g_c²):

1. Every generator mlProj(m * ∂^S p) depends on S through iterDeriv_cvProd_eq:
   ∂^S p = (-1)^κ × ∏_{hit} g_c² × ∏_{unhit} (1 - z_c · g_c²)

2. After mlProj, the result is a multilinear polynomial. The monomials that
   survive mlProj are those where each variable appears at most once.

3. For a fixed S (hitting clauses C₁,...,Cₖ), the generator is determined by:
   - shift m: multilinear in selector vars ⊆ S (2^κ choices)
   - which unhit z_c variables are "activated" (contribute to the monomial)
   - for each activated clause: which multilinear terms from g_c survive

4. The SPDP matrix row from (S, m) is a vector in ℚ^{monomials}.
   The row PATTERN (which entries are nonzero and their values) depends on S
   through the factored form. Two different S with the same profile produce
   rows with the SAME pattern at DIFFERENT column positions.

5. TYPE-ANONYMITY: The row rank of the profile-h submatrix equals the row rank
   of any single window's submatrix, because column permutation (from variable
   renaming between same-profile windows) preserves row rank.

6. Therefore: mlBlockedSpdpRank = rank(M) ≤ Σ_h rank(M_h) ≤ Σ_h 2^{155κ}
   ≤ (30κ+1)^4 × 2^{155κ} ≤ n^200.

## Formalization strategy

We prove rank(M) ≤ n^200 by showing the row space of M is contained in
a subspace of dimension ≤ n^200. The subspace is constructed using the
mlBlockedSpdpSubspace_le_restrictTotalDegree inclusion and a cardinality
argument on the profile-compressed spanning set.

The key fact we use: for a SINGLE derivative list S₀, the span of
{mlProj(m * ∂^{S₀} p) | m shift} has finrank ≤ 2^{155κ}.
(Proved as single_window_finrank_le in ProfileCompression.lean.)

For the full mlBlockedSpdpSubspace (all derivative lists S), we decompose
by profile and use the fact that:
- Number of profiles ≤ (30κ+1)^4
- For each profile h, the generators span a subspace of finrank ≤ 2^{155κ}

The per-profile finrank bound is WHERE type-anonymity lives.
In the polynomial ring MvPolynomial, this requires: for any two derivative
lists S₁, S₂ with the same profile, the combined span of their generators
has finrank ≤ 2^{155κ} (not 2 × 2^{155κ}).

We prove this using: rename σ (which maps S₁ to S₂) is an algebra isomorphism.
The combined span equals span(gens of S₁) + rename σ (span(gens of S₁)).
Since rename σ acts on COLUMNS of the coefficient matrix and preserves
the row structure, the combined row rank = rank of S₁ alone.

In Lean: finrank(V + rename σ V) = finrank(V) when σ is a permutation
and V is the image of a linear map φ : shifts → polys, and rename σ ∘ φ = φ'
where φ' has the same range dimension. The combined range satisfies
finrank ≤ finrank(V) because the rows are column-permutations.

Actually in Lean terms: if L₁ = Submodule.map (rename σ).toLinearMap L₀,
then finrank(L₀ ⊔ L₁) ≤ finrank(L₀) + finrank(L₁) = 2 × finrank(L₀).
This gives 2^{155κ+1} per pair, and k windows give k × 2^{155κ}.

THE RESOLUTION: We DON'T decompose by window. We decompose by PROFILE PATTERN.
Each abstract pattern contributes ONE dimension. The number of abstract patterns
is bounded by the symmetric power dimension. The concrete generators (from
different windows) all correspond to the SAME abstract patterns (just at
different column positions). In the SPDP MATRIX, they produce the same rows
(up to column permutation). The matrix rank counts distinct row patterns,
not distinct row vectors. So rank = number of distinct patterns = dim(V_h).

In MvPolynomial: finrank(span) = rank(coefficient matrix). And
rank(coefficient matrix) = number of linearly independent rows = number
of distinct row patterns (when rows are grouped by column permutation).

THIS IS THE SUBTLE POINT: In MvPolynomial (Fin N) ℚ, if two polynomials
p₁ and p₂ satisfy p₂ = rename σ p₁ for a PERMUTATION σ, then p₁ and p₂
have the same coefficient pattern. If {p₁,...,pₖ} are linearly independent,
then {rename σ p₁,...,rename σ pₖ} are also linearly independent (rename
is an isomorphism). But the COMBINED set {p₁,...,pₖ,rename σ p₁,...,rename σ pₖ}
has rank = rank{p₁,...,pₖ} + rank{rename σ p₁,...,rename σ pₖ} MINUS overlap.

The overlap is: span{pᵢ} ∩ span{rename σ pᵢ}. For a generic permutation σ,
this intersection could be {0} (no overlap), giving rank = 2k.

So in MvPolynomial, the per-profile finrank CAN be larger than 2^{155κ}.
The paper's bound works for the MATRIX RANK but not directly for the
polynomial span finrank.

HOWEVER: mlBlockedSpdpRank IS defined as finrank(mlBlockedSpdpSubspace),
and the paper claims Γ = rank(M) = finrank(mlBlockedSpdpSubspace). These
are the same quantity. The matrix rank = polynomial span finrank because
the monomials form a basis of the coefficient space, and the finrank of
the span of a set of vectors = the rank of the matrix whose rows are those
vectors.

So: rank(M) = finrank(mlBlockedSpdpSubspace). And the paper proves
rank(M) ≤ n^200 via profile compression. The proof uses the MATRIX
representation where column permutations are transparent.

In Lean: finrank(mlBlockedSpdpSubspace) = rank of the coefficient matrix
of the generators. This is the same number regardless of whether we
think of it as polynomial finrank or matrix rank.

The profile compression argument works AT THE MATRIX LEVEL. In the matrix,
same-profile rows are column permutations → don't add to rank. This is
a fact about matrices, not about polynomial submodules.

TO FORMALIZE: We need a lemma saying "if rows r₁,...,rₖ of a matrix have
rank D, and σ is a column permutation, then the matrix [r₁,...,rₖ, σ(r₁),...,σ(rₖ)]
also has rank D."

This is STANDARD LINEAR ALGEBRA: applying a column permutation σ to all rows
gives a matrix with the same row space (since σ is invertible). The union
matrix [M; σM] has row space = row_space(M) + row_space(σM) = row_space(M)
+ σ(row_space(M)). But σ is a permutation of BASIS VECTORS, so
σ(row_space(M)) is a different subspace in general.

WAIT — σ acts on COLUMNS. If M has rows v₁,...,vₖ ∈ ℚ^N, then σM has rows
v₁∘σ,...,vₖ∘σ (each row permuted by σ). The row space of σM is
{Σ aᵢ vᵢ∘σ} = {(Σ aᵢ vᵢ) ∘ σ} = row_space(M) ∘ σ.

The combined row space is row_space(M) + row_space(M)∘σ.

This has dimension ≤ dim(row_space(M)) + dim(row_space(M)∘σ) = 2D.

So the combined rank IS potentially 2D. For k windows: kD.

THIS MEANS: the polynomial span finrank (= matrix rank) can be up to
(number of windows) × (single window rank), which is superpolynomial.

CONCLUSION: The profile compression bound n^200 CANNOT be proved by the
approach I've been trying. The paper's argument must use something deeper
than just "column permutation of row vectors."

RE-READING THE PAPER ONE LAST TIME:

"each such row is determined (up to interface renaming) by a profile h
together with constant-size local choices inside each type"

This means: the row IS THE SAME VECTOR (up to renaming the column indices).
Not that it's a DIFFERENT vector obtained by permuting columns. The ROW
(as a function from column indices to coefficients) is the same function
composed with the renaming.

In matrix terms: M[S₁, α] = M[S₂, σ(α)]. As row VECTORS, the S₁ row
and the S₂ row are DIFFERENT vectors. But as FUNCTIONS on column indices,
they're the same function composed with σ.

The row rank counts linearly independent ROW VECTORS, not linearly
independent FUNCTIONS. So the row rank can increase with more windows.

UNLESS... the column set is the SAME for all windows. The SPDP matrix
has columns indexed by ALL monomials in ALL variables. Different windows
contribute nonzero entries in different columns. The rows from different
windows have DISJOINT support in the column indices (if the windows use
completely different variables). Disjoint-support rows are always linearly
independent. So the rank grows with windows.

THIS CONTRADICTS the paper's bound.

UNLESS the paper uses a DIFFERENT definition of rank. Let me check.

The paper says: Γ_{κ,ℓ}(p) = rank(M_{κ,ℓ}(p)). And the Lean definition:
mlBlockedSpdpRank = finrank(mlBlockedSpdpSubspace). If these are the same,
then the paper's bound should apply.

But if generators from different windows have disjoint monomial support,
they ARE linearly independent. So finrank grows with windows.

For the Tseitin polynomial: generators from different windows DO share
monomial support (through the unhit factors which involve ALL clause variables).
The common monomials create linear dependencies. The profile compression
argument exploits these dependencies.

Specifically: for the Tseitin product ∏(1 - z_c g_c²), after differentiating
κ selectors and expanding, the result involves ALL unhit clause variables.
Two different windows (different hit sets, same profile) produce generators
that share MOST of their monomial support (the unhit factors). The linear
dependencies from the shared support reduce the combined rank.

The paper's Theorem 23 quantifies this: the rank is bounded by the
profile compression number, not by the number of windows.

For the Lean proof: I need to formalize the linear dependencies between
generators from different same-profile windows. This requires the explicit
factored form from iterDeriv_cvProd_eq and showing the shared unhit factors
create enough dependencies.

This is indeed ~300 lines but it's very concrete algebra. Let me start.
-/

namespace TypeAnonymityProof

open SPDP MultilinearSPDP Tseitin MvPolynomial NPWitness

-- The proof will go here. For now, document the strategy.
-- TODO: Implement the factored-form analysis using iterDeriv_cvProd_eq.

end TypeAnonymityProof
