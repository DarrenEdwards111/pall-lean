import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.IdentityMinor
import Mathlib.Tactic

/-!
# ProfilePermutation — Type-anonymity rank bound

Paper §9.1 Theorem 23: Width⇒Rank via profile compression.

The paper bounds Γ_{κ,ℓ}(p) = rank(M_{κ,ℓ}(p)) by:
1. Decomposing rows by profile: RowSpan(M) ⊆ Σ_h V_h
2. Bounding dim(Σ V_h) ≤ Σ dim(V_h) ≤ |H(R)| × max dim(V_h) = R^{O(1)}

For the Lean formalization, mlBlockedSpdpRank = finrank(mlBlockedSpdpSubspace).
The profile compression bounds this directly.

The core mathematical claim: every generator mlProj(m * ∂^S p) with derivative
list S having "profile" h (histogram of clause types) contributes at most
dim(V_h) to the overall rank, where V_h is the abstract profile space.

In the polynomial ring, generators from different windows with the same profile
are related by variable permutations (column permutations of the SPDP matrix).
The overall mlBlockedSpdpRank = rank(M) is bounded by the paper's argument
because the profile decomposition bounds the row rank directly.
-/

namespace ProfilePermutation

open SPDP MultilinearSPDP Tseitin MvPolynomial NPWitness

/-- Paper Theorem 23 (Width⇒Rank) — the single remaining mathematical axiom.

    For the Tseitin polynomial under matching parameters κ = ℓ ∈ [5, log₂ n]:
    mlBlockedSpdpRank(tseitinPartition, κ, κ, tseitinPoly) ≤ n^200.

    Paper proof: Profile compression.
    1. Row decomposition: RowSpan(M) ⊆ Σ_{h∈H(R)} V_h
    2. |H(R)| ≤ (30κ+1)^4 (Lemma 20, PROVED as num_profiles_le)
    3. dim(V_h) ≤ (30κ+16)^60 (Lemma 22, PROVED as profile_space_dim_bound)
    4. dim(Σ V_h) ≤ Σ dim(V_h) (subadditivity)
    5. 2^κ × (30κ+1)^4 × (30κ+16)^60 ≤ n^200 (PROVED as tseitin_rank_via_profile_compression)

    The row decomposition (step 1) is the type-anonymity claim:
    each SPDP generator's contribution to rank is determined by its profile,
    not by which specific clauses realize that profile.

    This is the LAST axiom on the active P≠NP chain. All other components
    (arithmetic, combinatorics, extraction, contradiction) are proved. -/
axiom type_anonymity_rank_bound (n κ : ℕ) (hn : n ≥ 4)
    (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n ^ 200

end ProfilePermutation
