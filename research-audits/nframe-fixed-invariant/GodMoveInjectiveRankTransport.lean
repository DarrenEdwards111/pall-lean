import GodMoveMonomialMinor

/-!
# Exact parameter transport from assignment variables to machine input positions

Injective renaming preserves the actual strict blocked SPDP rank at the same
derivative and shift parameters, with the block partition pulled back along
the injection. Renaming also preserves every selected derivative coefficient.
These facts transport a verifier minor to distinct encoded machine input
positions without identifying variables or changing its parameters.

The inclusive convention has the corresponding lower-bound transport. None
of these algebraic facts gives a runtime-derived upper bound for machine rank.
-/

namespace GodMoveInjectiveRankTransport

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor (discreteBlocks)

/-- Reversing an injective renaming proves the missing lower inequality;
the existing forward bound gives equality at exactly the same parameters. -/
theorem strict_rank_rename {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B k ell (rename f p) =
      mlBlockedSpdpRank (pullbackPartition B f) k ell p := by
  apply Nat.le_antisymm (mlBlockedSpdpRank_rename_le f hf B k ell p)
  have h := restriction_rank_monotone F f hf B k ell (rename f p)
  simpa only [restrictPoly_rename] using h

/-- Inclusive rank lower bounds survive the same injective embedding. -/
theorem inclusive_rank_le_rename {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRankInc (pullbackPartition B f) k ell p ≤
      mlBlockedSpdpRankInc B k ell (rename f p) := by
  have h := restriction_rank_monotone_inc F f hf B k ell (rename f p)
  simpa only [restrictPoly_rename] using h

/-- Block labels may change, provided the pairs placed together do not. -/
theorem admissible_iff_of_same_blocks {n : ℕ} (B₁ B₂ : BlockPartition n)
    (hB : ∀ i j, B₁.assign i = B₁.assign j ↔ B₂.assign i = B₂.assign j)
    (S : List (Fin n)) : isBlockAdmissible B₁ S ↔ isBlockAdmissible B₂ S := by
  constructor
  · exact isBlockAdmissible_coarsen B₂ B₁ S (fun i j => (hB i j).mpr)
  · exact isBlockAdmissible_coarsen B₁ B₂ S (fun i j => (hB i j).mp)

theorem strict_subspace_eq_of_same_blocks {n : ℕ} {F : Type*} [CommRing F]
    (B₁ B₂ : BlockPartition n)
    (hB : ∀ i j, B₁.assign i = B₁.assign j ↔ B₂.assign i = B₂.assign j)
    (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspace B₁ k ell p = mlBlockedSpdpSubspace B₂ k ell p := by
  unfold mlBlockedSpdpSubspace
  congr 1
  ext q
  simp only [Set.mem_setOf_eq, admissible_iff_of_same_blocks B₁ B₂ hB]

theorem inclusive_subspace_eq_of_same_blocks {n : ℕ} {F : Type*} [CommRing F]
    (B₁ B₂ : BlockPartition n)
    (hB : ∀ i j, B₁.assign i = B₁.assign j ↔ B₂.assign i = B₂.assign j)
    (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpSubspaceInc B₁ k ell p = mlBlockedSpdpSubspaceInc B₂ k ell p := by
  unfold mlBlockedSpdpSubspaceInc
  congr 1
  ext q
  simp only [Set.mem_setOf_eq, admissible_iff_of_same_blocks B₁ B₂ hB]

/-- In particular, adding unused ambient variables does not alter the strict
rank with discrete blocks, including when either variable set is empty. -/
theorem strict_rank_discrete_rename {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank (discreteBlocks m) k ell (rename f p) =
      mlBlockedSpdpRank (discreteBlocks n) k ell p := by
  rw [strict_rank_rename f hf]
  unfold mlBlockedSpdpRank
  rw [strict_subspace_eq_of_same_blocks (pullbackPartition (discreteBlocks m) f)
    (discreteBlocks n) (fun _ _ => hf.eq_iff)]

theorem inclusive_rank_discrete_le_rename {n m : ℕ} {F : Type*} [Field F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (k ell : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRankInc (discreteBlocks n) k ell p ≤
      mlBlockedSpdpRankInc (discreteBlocks m) k ell (rename f p) := by
  have h := inclusive_rank_le_rename f hf (discreteBlocks m) k ell p
  unfold mlBlockedSpdpRankInc at h ⊢
  rwa [inclusive_subspace_eq_of_same_blocks (pullbackPartition (discreteBlocks m) f)
    (discreteBlocks n) (fun _ _ => hf.eq_iff)] at h

/-- Every derivative coefficient, hence every selected minor, is unchanged
when rows and columns are renamed by the same input-coordinate injection. -/
theorem derivative_coefficient_rename {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : MvPolynomial (Fin n) F) (S : List (Fin n)) (d : Fin n →₀ ℕ) :
    coeff (Finsupp.mapDomain f d) (iterDerivList (S.map f) (rename f p)) =
      coeff d (iterDerivList S p) := by
  rw [iterDerivList_rename f hf]
  exact coeff_rename_mapDomain f hf _ d

/-- The explicit monomial identity minor survives in the larger input space. -/
theorem monomial_coefficient_identity_rename {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S T : Finset (Fin n)) :
    coeff (Finsupp.mapDomain f (GodMoveMonomialMinor.complementaryColumn S))
      (iterDerivList (T.toList.map f) (rename f (GodMoveMonomialMinor.fullMonomial n))) =
      if S = T then 1 else 0 := by
  rw [derivative_coefficient_rename f hf]
  exact GodMoveMonomialMinor.coefficient_identity S T

end GodMoveInjectiveRankTransport

#print axioms GodMoveInjectiveRankTransport.strict_rank_rename
#print axioms GodMoveInjectiveRankTransport.inclusive_rank_le_rename
#print axioms GodMoveInjectiveRankTransport.strict_subspace_eq_of_same_blocks
#print axioms GodMoveInjectiveRankTransport.inclusive_subspace_eq_of_same_blocks
#print axioms GodMoveInjectiveRankTransport.strict_rank_discrete_rename
#print axioms GodMoveInjectiveRankTransport.inclusive_rank_discrete_le_rename
#print axioms GodMoveInjectiveRankTransport.derivative_coefficient_rename
#print axioms GodMoveInjectiveRankTransport.monomial_coefficient_identity_rename
