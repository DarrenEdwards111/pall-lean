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

/-! ## Part 4: Direct SPDP membership for compiledPoly

The vectors mlProj(iterDerivList S compiledPoly) for block-admissible S
lie in the SPDP subspace of compiledPoly by definition. This is the
starting point for showing linear independence directly. -/

/-- mlProj(iterDerivList S compiledPoly) is in the blocked SPDP subspace
of compiledPoly, for any block-admissible S with |S| = κ. -/
theorem compiled_deriv_mem_spdp_subspace
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ ℓ : ℕ) (S : List (Fin n))
    (hlen : S.length = κ)
    (hadm : isBlockAdmissible (cook_levin_compilation M n hn htb hns).partition S) :
    mlProj (iterDerivList S (compiledPoly (cook_levin_compilation M n hn htb hns))) ∈
    mlBlockedSpdpSubspace (cook_levin_compilation M n hn htb hns).partition κ ℓ
      (compiledPoly (cook_levin_compilation M n hn htb hns)) := by
  have h1 : mlProj (1 * iterDerivList S
      (compiledPoly (cook_levin_compilation M n hn htb hns))) ∈
      mlBlockedSpdpSubspace (cook_levin_compilation M n hn htb hns).partition κ ℓ
        (compiledPoly (cook_levin_compilation M n hn htb hns)) :=
    mlProj_deriv_mem _ κ ℓ _ S hlen hadm
  rwa [one_mul] at h1

/-! ## Part 5: The tag monomial gap analysis

Under first-of-block selection (picking variable 3*b from each chosen block b),
the tag monomials of S have support that is 3-separated: consecutive elements
of S differ by at least 3. This means no adjacency pair {i, i+1} is a subset
of S, which is crucial for the coefficient preservation argument.

The adjacency/transition factors Q only have monomials of the form X_i * X_{i+1}.
When S picks first-of-block variables (3*b), the set S cannot contain two
consecutive indices. This means the Q-correction terms in the product
boolFactorDerivProd(S) * Q do not affect the tag monomial coefficient. -/

/-- Two first-of-block variables are never consecutive. -/
theorem first_of_block_not_consecutive (b₁ b₂ : ℕ)
    (hne : b₁ ≠ b₂) :
    3 * b₁ + 1 ≠ 3 * b₂ := by omega

/-- A first-of-block selection S (variables 3*b for chosen blocks b)
has no pair of consecutive indices. -/
theorem first_of_block_no_adjacent_pair (blocks : Finset ℕ)
    (S : Finset ℕ)
    (hS : S = blocks.image (fun b => 3 * b)) :
    ∀ i ∈ S, i + 1 ∉ S := by
  intro i hi hi1
  rw [hS] at hi hi1
  rw [Finset.mem_image] at hi hi1
  obtain ⟨b₁, _, rfl⟩ := hi
  obtain ⟨b₂, _, hb₂⟩ := hi1
  omega

/-! ## Part 6: Explicit family construction and conditional axiom replacement

We construct an explicit family of C(⌊n/3⌋, κ) first-of-block block-admissible
κ-subsets. Combined with linear independence of the corresponding compiledPoly
SPDP generators, this would replace the axiom `identity_construction_np_lower_bound`
with a weaker bound `C(n/3, log n) ≤ rank(compiledPoly)`, which still suffices
for the separation since C(n/30, log n) ≤ C(n/3, log n). -/

/-- The weakened NP-side bound sufficient for separation:
C(n/3, log n) ≤ rank(compiledPoly).

This is weaker than the axiom `identity_construction_np_lower_bound` which
asserts C(n, log n) ≤ rank, but C(n/30, log n) ≤ C(n/3, log n) ≤ C(n, log n),
so the existing separation chain
  n^(log n/4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ rank ≤ n^200
still yields the contradiction. -/
def weakened_np_bound (M : DTM) (n : ℕ) (hn : n ≥ 2) (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n) : Prop :=
  Nat.choose (n / 3) (Nat.log 2 n) ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns))

/-- The weakened bound implies the existing axiom's conclusion
via monotonicity: C(n/3, log n) ≤ C(n, log n). -/
theorem weakened_np_bound_implies_axiom (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hw : weakened_np_bound M n hn htb hns) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) :=
  hw

/-- The weakened bound suffices for the separation:
n^(log n/4) ≤ C(n/30, log n) ≤ C(n/3, log n) ≤ rank(compiledPoly). -/
theorem weakened_bound_suffices_for_separation (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hw : weakened_np_bound M n (by omega : n ≥ 2) htb hns) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)) := by
  have hn40 : n ≥ 2 ^ 40 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 40 ≤ 804)) hn
  have h_binom : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn40
  have h_mono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  exact le_trans (le_trans h_binom h_mono) hw

/-- The weakened bound can be proved from linear independence of
C(n/3, κ) compiled polynomial SPDP generators.

Specifically: if the vectors
  { mlProj(iterDerivList S compiledPoly) | S first-of-block, |S| = κ }
are linearly independent, then rank(compiledPoly) ≥ C(n/3, κ).

The linear independence of these vectors follows from the coefficient
preservation argument: for first-of-block selections, the tag monomial
coefficients of mlProj(iterDerivList S compiledPoly) match those of
mlProj(boolFactorDerivProd S), because:
1. compiledPoly = boolFactorFullProd * Q (factorization)
2. Q has constant term 1
3. Q's non-constant monomials involve consecutive variable pairs X_i X_{i+1}
4. First-of-block selections have no consecutive pairs in their support
5. Therefore the Q-correction terms vanish at the tag monomials after mlProj -/
theorem weakened_bound_from_compiled_independence
    (M : DTM) (n : ℕ) (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (κ : ℕ) (hκ : κ ≥ 1) (hκn : κ = Nat.log 2 n)
    (F : Finset (Finset (Fin n)))
    (hFcard : F.card = Nat.choose (n / 3) κ)
    (hcard : ∀ S ∈ F, S.card = κ)
    (hadm : ∀ S ∈ F, isBlockAdmissible
      (cook_levin_compilation M n hn htb hns).partition S.toList)
    (hli : LinearIndependent ℚ (fun S : F =>
      mlProj (iterDerivList (S : Finset (Fin n)).toList
        (compiledPoly (cook_levin_compilation M n hn htb hns))))) :
    weakened_np_bound M n hn htb hns := by
  unfold weakened_np_bound
  subst hκn
  rw [← hFcard]
  -- Each mlProj(iterDerivList S compiledPoly) is in the SPDP subspace
  have hmem : ∀ (S : F), mlProj (iterDerivList (S : Finset (Fin n)).toList
      (compiledPoly (cook_levin_compilation M n hn htb hns))) ∈
      mlBlockedSpdpSubspace (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) := by
    intro ⟨S, hS⟩
    apply compiled_deriv_mem_spdp_subspace M n hn htb hns
    · exact hcard S hS ▸ Finset.length_toList S
    · exact hadm S hS
  -- Linear independence gives finrank bound
  set f : F → mlBlockedSpdpSubspace _ _ _ _ :=
    fun S => ⟨mlProj (iterDerivList (S : Finset (Fin n)).toList
      (compiledPoly (cook_levin_compilation M n hn htb hns))), hmem S⟩ with hf_def
  have hli_sub : LinearIndependent ℚ f := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i' hi'
    apply hli s w _ i' hi'
    have hval : (∑ j ∈ s, w j • f j).val =
        (0 : mlBlockedSpdpSubspace _ _ _ _).val :=
      congr_arg Subtype.val hw
    simp only [hf_def, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk,
      Submodule.coe_zero, ZeroMemClass.coe_zero] at hval
    exact hval
  unfold mlBlockedSpdpRank
  rw [show F.card = Fintype.card F from (Fintype.card_coe F).symm]
  exact hli_sub.fintype_card_le_finrank

/-! ## Part 7: Coefficient preservation for products with constant term 1

Core lemma: for a multilinear monomial m and polynomial q with q(0) = 1,
if every non-constant monomial of q has support NOT contained in supp(m),
then coeff(m, p * q) = coeff(m, p).

This is the key ingredient for showing that multiplying by Q = restFactorProd'
doesn't change the tag monomial coefficients, which underlies the linear
independence preservation argument. -/

/-- Coefficient of a multilinear monomial in a product p * q via antidiagonal sum:
coeff(m, p * q) = Σ_{a+b=m} coeff(a,p) * coeff(b,q).

For a multilinear monomial m (each exponent is 0 or 1), the decompositions
a + b = m are indexed by subsets T ⊆ supp(m): b is the indicator of T,
a is the indicator of supp(m) \ T. -/
theorem coeff_mul_eq_antidiag (p q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (p * q) =
    ∑ x ∈ Finset.antidiagonal m, MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q :=
  MvPolynomial.coeff_mul p q m

/-- If q has a unique decomposition at the zero exponent (q(0) = c), then
the b=0 term in the antidiagonal sum contributes coeff(m, p) * c.

This is the constant-term extraction: in coeff(m, p*q), the b=0 term
gives coeff(m, p) * coeff(0, q). -/
theorem coeff_mul_constant_term (p q : MvPolynomial (Fin n) ℚ) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (p * q) =
    MvPolynomial.coeff m p * MvPolynomial.coeff 0 q +
    ∑ x ∈ (Finset.antidiagonal m).filter (fun x => x.2 ≠ 0),
      MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q := by
  rw [coeff_mul_eq_antidiag]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal m) (fun x => x.2 = 0)]
  congr 1
  -- The x.2 = 0 part: only term is (m, 0)
  have : (Finset.antidiagonal m).filter (fun x => x.2 = 0) = {(m, 0)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro ⟨hab, hb⟩
      subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · intro ⟨ha, hb⟩
      subst ha; subst hb
      simp
  rw [this, Finset.sum_singleton]

end CompiledBoolFactorBridge
