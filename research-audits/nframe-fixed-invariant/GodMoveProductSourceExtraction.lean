import PallLean.PiStarConcrete

/-!
# Genuine product-source extraction by zero substitution

Keep the variables of a target polynomial `Q` and set administrative
variables to zero.  If the administrative factor `R` becomes `1`, this
single concrete projection extracts `Q` from the source `Q * R` and does
not increase the existing strict multilinear blocked SPDP rank.

For the explicit administrative product `R = product_j (1 - X_j)`, the
normalization premise is proved whenever all its variables are dropped.
The last theorem instantiates the target itself as a product of retained
local factors, so neither its extraction identity nor rank comparison is
assumed.

The source already contains the target product.  This does not extract a
product from an additive accumulator energy, and gives no polynomial
P-side rank bound or SAT separation.  All rank comparisons below use the
repository's strict `mlBlockedSpdpRank`, with the same partition and the
same derivative/shift parameters on source and target.
-/

namespace GodMoveProductSourceExtraction

open scoped BigOperators
open MvPolynomial PiStarConcrete MultilinearSPDP

abbrev Poly (N : ℕ) := MvPolynomial (Fin N) ℚ

/-- Exact extraction from a product source using the existing zero-substitution gauge. -/
theorem piZero_extract_product {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (Q R : Poly N) (hQ : ∀ i ∈ Q.vars, keep i)
    (hR : piZero keep R = 1) :
    piZero keep (Q * R) = Q := by
  rw [piZero_mul_eq_of_support_kept keep
    (support_kept_of_vars_kept keep hQ) R, hR, mul_one]

/-- Actual strict SPDP rank monotonicity for this extracted product. -/
theorem extracted_product_rank_le_source {N : ℕ}
    (B : SPDP.BlockPartition N) (kappa ell : ℕ)
    (keep : Fin N → Prop) [DecidablePred keep]
    (Q R : Poly N) (hQ : ∀ i ∈ Q.vars, keep i)
    (hR : piZero keep R = 1) :
    mlBlockedSpdpRank B kappa ell Q ≤ mlBlockedSpdpRank B kappa ell (Q * R) := by
  have hmono := piZero_isRankMonotoneGauge keep B kappa ell (Q * R)
  rwa [piZero_extract_product keep Q R hQ hR] at hmono

/-- A concrete finite product of local factors. -/
noncomputable def localFactorProduct {N : ℕ} (indices : Finset (Fin N)) : Poly N :=
  ∏ j ∈ indices, ((1 : Poly N) - X j)

/-- Dropped administrative factors become `1`, proved directly from substitution. -/
theorem piZero_admin_product_eq_one {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (admin : Finset (Fin N)) (hadmin : ∀ j ∈ admin, ¬ keep j) :
    piZero keep (localFactorProduct admin) = 1 := by
  change substAlgHom keep 0 (∏ j ∈ admin, ((1 : Poly N) - X j)) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j hj
  rw [map_sub, map_one]
  change (1 : Poly N) - piZero keep (X j) = 1
  rw [piZero_X, if_neg (hadmin j hj), sub_zero]

/-- The explicit administrative product requires no separate normalization hypothesis. -/
theorem extract_with_admin_product {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (Q : Poly N) (hQ : ∀ i ∈ Q.vars, keep i)
    (admin : Finset (Fin N)) (hadmin : ∀ j ∈ admin, ¬ keep j) :
    piZero keep (Q * localFactorProduct admin) = Q :=
  piZero_extract_product keep Q (localFactorProduct admin) hQ
    (piZero_admin_product_eq_one keep admin hadmin)

/-- Rank comparison for that concrete administrative extension of any retained target. -/
theorem admin_product_extraction_rank_le {N : ℕ}
    (B : SPDP.BlockPartition N) (kappa ell : ℕ)
    (keep : Fin N → Prop) [DecidablePred keep]
    (Q : Poly N) (hQ : ∀ i ∈ Q.vars, keep i)
    (admin : Finset (Fin N)) (hadmin : ∀ j ∈ admin, ¬ keep j) :
    mlBlockedSpdpRank B kappa ell Q ≤
      mlBlockedSpdpRank B kappa ell (Q * localFactorProduct admin) :=
  extracted_product_rank_le_source B kappa ell keep Q (localFactorProduct admin) hQ
    (piZero_admin_product_eq_one keep admin hadmin)

/-- Retained local factors are fixed by the same concrete projection. -/
theorem piZero_kept_product_eq_self {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (kept : Finset (Fin N)) (hkept : ∀ j ∈ kept, keep j) :
    piZero keep (localFactorProduct kept) = localFactorProduct kept := by
  change substAlgHom keep 0 (∏ j ∈ kept, ((1 : Poly N) - X j)) =
    ∏ j ∈ kept, ((1 : Poly N) - X j)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [map_sub, map_one]
  change (1 : Poly N) - piZero keep (X j) = 1 - X j
  rw [piZero_X, if_pos (hkept j hj)]

/-- Fully explicit product-source extraction, together with the genuine strict SPDP
rank inequality.  Source, target, and the projection are all constructed. -/
theorem explicit_product_source_extraction_and_rank {N : ℕ}
    (B : SPDP.BlockPartition N) (kappa ell : ℕ)
    (keep : Fin N → Prop) [DecidablePred keep]
    (kept admin : Finset (Fin N))
    (hkept : ∀ j ∈ kept, keep j) (hadmin : ∀ j ∈ admin, ¬ keep j) :
    piZero keep (localFactorProduct kept * localFactorProduct admin) =
        localFactorProduct kept ∧
      mlBlockedSpdpRank B kappa ell (localFactorProduct kept) ≤
        mlBlockedSpdpRank B kappa ell
          (localFactorProduct kept * localFactorProduct admin) := by
  have hextract :
      piZero keep (localFactorProduct kept * localFactorProduct admin) =
        localFactorProduct kept := by
    change substAlgHom keep 0 (localFactorProduct kept * localFactorProduct admin) = _
    rw [map_mul]
    change piZero keep (localFactorProduct kept) * piZero keep (localFactorProduct admin) = _
    rw [piZero_kept_product_eq_self keep kept hkept,
      piZero_admin_product_eq_one keep admin hadmin, mul_one]
  refine ⟨hextract, ?_⟩
  have hmono := piZero_isRankMonotoneGauge keep B kappa ell
    (localFactorProduct kept * localFactorProduct admin)
  rwa [hextract] at hmono

end GodMoveProductSourceExtraction

#print axioms GodMoveProductSourceExtraction.piZero_extract_product
#print axioms GodMoveProductSourceExtraction.extracted_product_rank_le_source
#print axioms GodMoveProductSourceExtraction.piZero_admin_product_eq_one
#print axioms GodMoveProductSourceExtraction.extract_with_admin_product
#print axioms GodMoveProductSourceExtraction.admin_product_extraction_rank_le
#print axioms GodMoveProductSourceExtraction.piZero_kept_product_eq_self
#print axioms GodMoveProductSourceExtraction.explicit_product_source_extraction_and_rank
