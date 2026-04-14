/-
  CompiledBoolFactorBridge.lean -- Bridge from boolFactorFullProd to compiledPoly

  The NP-side axiom `identity_construction_np_lower_bound` requires:
    C(n, log n) ≤ mlBlockedSpdpRank B κ κ (compiledPoly T)

  We have from BlockedBoolRank:
    |F| ≤ mlBlockedSpdpRank B κ ℓ (boolFactorFullProd N)

  This file bridges the gap by:
  1. Connecting the CookLevinDefs factorization to boolFactorFullProd (Part 1)
  2. Proving block-admissible subset counting under the locality partition (Part 2)
  3. Documenting the remaining gap and what would close it (Part 3)
-/
import PallLean.CookLevinDefs
import PallLean.SymmetricPower
import PallLean.BlockedBoolRank
import PallLean.MultilinearSPDP
import Mathlib.Tactic

namespace CompiledBoolFactorBridge

open MvPolynomial SPDP MultilinearSPDP PaperFaithfulSeparation SymmetricPower TuringMachine

/-! ## Part 1: The booleanity factor product from cook_levin_compilation
equals boolFactorFullProd

CookLevinDefs.boolConstraintFactors_eq shows:
  (boolConstraintList n).map (1 - ·.poly) = (List.finRange n).map (fun v => 1 - X_v(1-X_v))

SymmetricPower.boolFactor n v = 1 - X_v * (1 - X_v)

So the products match: boolConstraintList factors product = boolFactorFullProd n. -/

/-- The booleanity constraint factors match boolFactor exactly. -/
theorem boolConstraint_factor_eq_boolFactor (n : ℕ) (v : Fin n) :
    (1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly = boolFactor n v := by
  unfold boolFactor
  rw [boolLC_factor_eq]

/-- The booleanity factors list matches the boolFactor list. -/
theorem boolConstraint_factors_list_eq (n : ℕ) :
    (boolConstraintList n).map (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly) =
    (List.finRange n).map (boolFactor n) := by
  rw [boolConstraintFactors_eq]
  congr 1

/-- The product of booleanity constraint factors equals boolFactorFullProd. -/
theorem boolConstraint_prod_eq_boolFactorFullProd (n : ℕ) :
    ((boolConstraintList n).map (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)).prod =
    boolFactorFullProd n := by
  rw [boolConstraint_factors_list_eq]
  unfold boolFactorFullProd
  rfl

/-- compiledPoly(cook_levin_compilation ...) = boolFactorFullProd n * restFactorProd' M n.

This is the key structural fact connecting the compiled polynomial to boolFactorFullProd. -/
theorem compiledPoly_eq_boolFactorFullProd_mul_rest (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    compiledPoly (cook_levin_compilation M n hn htb hns) =
    boolFactorFullProd n * restFactorProd' M n := by
  rw [compiledPoly_factored, boolConstraint_prod_eq_boolFactorFullProd]

/-! ## Part 2: Block-admissible subset counting

Under the locality partition (block size 3), variable i is in block i/3.
A block-admissible κ-subset has at most 1 variable per block.

We count: choosing κ blocks from ⌊n/3⌋ full blocks gives C(⌊n/3⌋, κ) families,
each contributing at least one block-admissible κ-subset.

The total count of block-admissible κ-subsets is C(⌊n/3⌋, κ) * 3^κ
(choose 1 of 3 variables from each block). But we only need C(⌊n/3⌋, κ)
distinct subsets for the rank bound, which follows from choosing the FIRST
variable (3*b) from each chosen block b. -/

/-- For block b < ⌊n/3⌋, the variable 3*b is in bounds. -/
theorem three_mul_lt_of_block_lt (n : ℕ) (b : ℕ) (hb : b < n / 3) :
    3 * b < n := by omega

/-- Variables 3*b₁ and 3*b₂ from different blocks are different. -/
theorem first_of_block_injective (n : ℕ) (b₁ b₂ : ℕ)
    (hb₁ : b₁ < n / 3) (hb₂ : b₂ < n / 3) (hne : b₁ ≠ b₂) :
    (⟨3 * b₁, three_mul_lt_of_block_lt n b₁ hb₁⟩ : Fin n) ≠
    ⟨3 * b₂, three_mul_lt_of_block_lt n b₂ hb₂⟩ := by
  intro h
  simp [Fin.ext_iff] at h
  omega

/-- Variables 3*b₁ and 3*b₂ are in different blocks when b₁ ≠ b₂. -/
theorem first_of_block_different_blocks (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b₁ b₂ : ℕ) (hb₁ : b₁ < n / 3) (hb₂ : b₂ < n / 3) (hne : b₁ ≠ b₂) :
    (cook_levin_compilation M n hn htb hns).partition.assign
      ⟨3 * b₁, three_mul_lt_of_block_lt n b₁ hb₁⟩ ≠
    (cook_levin_compilation M n hn htb hns).partition.assign
      ⟨3 * b₂, three_mul_lt_of_block_lt n b₂ hb₂⟩ := by
  intro h
  have := (cook_levin_same_block M n hn htb hns _ _).mp h
  simp at this
  omega

/-! ## Part 2b: The key counting inequality

For the NP-side, we need: the number of distinct block-admissible κ-subsets
under the locality partition (block size 3) on n variables is large enough.

From our analysis:
- The number of full blocks is ⌊n/3⌋
- Choosing κ blocks from ⌊n/3⌋ blocks and picking first-of-block from each
  gives C(⌊n/3⌋, κ) distinct block-admissible κ-subsets
- This count is ≥ (⌊n/3⌋/κ)^κ by the standard binomial bound

For n = 2^804 and κ = log₂ n = 804:
  ⌊n/3⌋ ≈ 2^804/3 ≈ 2^802.4
  C(⌊n/3⌋, 804) ≈ (2^802.4/804)^804 ≈ 2^(804*(802.4-9.7)) ≈ 2^638000

And C(n, 804) ≈ (2^804/804)^804 ≈ 2^(804*(804-9.7)) ≈ 2^639000

So C(⌊n/3⌋, κ) is only slightly smaller than C(n, κ), both superpolynomial.
But the axiom states rank ≥ C(n, κ), not C(n/3, κ). -/

/-- C(n/3, k) ≥ (n/3/k)^k by the standard binomial lower bound. -/
theorem block_admissible_count_lower (n κ : ℕ) (hκ : 0 < κ) :
    (n / 3 / κ) ^ κ ≤ Nat.choose (n / 3) κ :=
  BinomialBound.choose_ge_div_pow (n / 3) κ hκ

/-! ## Part 3: Linking the factorization to the rank bound

The existing result `BlockedBoolRank.mlBlockedSpdpRank_ge_of_general_family_any_ell`
gives:
  |F| ≤ mlBlockedSpdpRank B κ ℓ (boolFactorFullProd N)

We need:
  C(n, log n) ≤ mlBlockedSpdpRank B κ κ (compiledPoly T)

where compiledPoly T = boolFactorFullProd n * restFactorProd'.

The gap is that rank(boolFactorFullProd) and rank(compiledPoly) may differ.
The SPDP subspace generators use derivatives of different polynomials.

Two possible closure strategies:

Strategy A: Product rank monotonicity
  Show rank(f * g) ≥ rank(f) under suitable conditions.
  This would give rank(compiledPoly) ≥ rank(boolFactorFullProd) ≥ |F|.
  Difficulty: this is not true in general. Counterexample: if g vanishes at a
  point where f's SPDP generators are nonzero, the product can have lower rank.

Strategy B: Direct linear independence
  Show that mlProj(iterDerivList S compiledPoly) for distinct block-admissible S
  are linearly independent. By Leibniz on compiledPoly = boolFactorFullProd * Q,
  the leading term of iterDerivList S compiledPoly is boolFactorDerivProd S * Q.
  The other Leibniz terms involve derivatives hitting Q. If the leading term
  dominates in some basis, linear independence follows.
  Difficulty: requires detailed analysis of the Leibniz cross-terms.

Either strategy would eliminate the axiom `identity_construction_np_lower_bound`.
For now, we expose the factorization and counting as stepping stones. -/

/-- The compiled polynomial's rank is at least the boolFactorFullProd's rank
IF a suitable product-monotonicity lemma holds.

This encapsulates the remaining gap: once we know rank(f*g) ≥ rank(f)
for f = boolFactorFullProd and g = restFactorProd', the axiom follows. -/
theorem compiled_rank_ge_bool_rank_of_product_mono
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ)
    (hmono : mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ (boolFactorFullProd n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn htb hns))) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ (boolFactorFullProd n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn htb hns)) :=
  hmono

/-- Combined: if product monotonicity holds, then the block-admissible family
rank bound from BlockedBoolRank transfers to compiledPoly. -/
theorem compiled_rank_ge_family_of_product_mono
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ) (hκ : κ ≥ 1)
    {F : Finset (Finset (Fin n))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hadm : ∀ S ∈ F, isBlockAdmissible
      (cook_levin_compilation M n hn htb hns).partition S.toList)
    (hmono : mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ (boolFactorFullProd n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn htb hns))) :
    F.card ≤ mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn htb hns)) :=
  le_trans
    (BlockedBoolRank.mlBlockedSpdpRank_ge_of_general_family_any_ell hκ _ hcard hadm)
    hmono

end CompiledBoolFactorBridge
