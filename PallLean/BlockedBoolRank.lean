/-
  BlockedBoolRank.lean — Blocked SPDP rank bound for boolFactorFullProd

  Bridges from the unblocked pairwise-disjoint family result
  (spdpRank_ge_of_disjoint_family) to the mlBlockedSpdpRank setting
  needed by the compiled polynomial axiom.

  Key result: mlBlockedSpdpRank_ge_of_disjoint_family
    For m pairwise disjoint, block-admissible κ-subsets of [N] (κ ≥ 1),
    mlBlockedSpdpRank B κ 0 (boolFactorFullProd N) ≥ m.

  The proof uses:
  1. mlProj_deriv_mem: mlProj(1 * ∂_S p) ∈ mlBlockedSpdpSubspace for admissible S
  2. coeff_mlProj_of_isMultilinear_mono: coefficient extraction through mlProj
  3. tagMonomial_isMultilinear: the extraction monomials are multilinear
  4. The existing Kronecker δ / pairwise-disjoint coefficient argument
-/
import PallLean.SymmetricPower
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace BlockedBoolRank

open MvPolynomial SPDP MultilinearSPDP SymmetricPower

/-! ## mlProj(boolFactorDerivProd S) lies in the blocked SPDP subspace -/

/-- boolFactorDerivProd S = 1 * iterDerivList S.toList (boolFactorFullProd N). -/
theorem boolFactorDerivProd_eq_one_mul_iterDeriv {N : ℕ} (S : Finset (Fin N)) :
    boolFactorDerivProd S = 1 * iterDerivList S.toList (boolFactorFullProd N) := by
  rw [one_mul]
  exact boolFactorDerivProd_eq_iterDerivList S

/-- mlProj(boolFactorDerivProd S) ∈ mlBlockedSpdpSubspace B κ ℓ (boolFactorFullProd N)
    when S has card κ and S.toList is block-admissible. -/
theorem mlProj_boolFactorDerivProd_mem_mlBlockedSpdpSubspace
    {N : ℕ} (B : BlockPartition N) (κ ℓ : ℕ) (S : Finset (Fin N))
    (hcard : S.card = κ)
    (hadm : isBlockAdmissible B S.toList) :
    mlProj (boolFactorDerivProd S) ∈
    mlBlockedSpdpSubspace B κ ℓ (boolFactorFullProd N) := by
  rw [boolFactorDerivProd_eq_one_mul_iterDeriv]
  exact mlProj_deriv_mem B κ ℓ (boolFactorFullProd N) S.toList
    (by rw [Finset.length_toList]; exact hcard) hadm

/-! ## Coefficient extraction through mlProj

The key fact: extracting the coefficient at a multilinear monomial from
mlProj(p) gives the same result as extracting it from p. Since tagMonomial
is multilinear, the Kronecker δ structure of the coefficient matrix is
preserved through mlProj. -/

/-- coeff(tagMonomial T)(mlProj(boolFactorDerivProd S)) = 2^|S∩T| for |S|=|T|. -/
theorem coeff_mlProj_boolFactorDerivProd_samesize {N : ℕ}
    (S T : Finset (Fin N)) (hcard : S.card = T.card) :
    MvPolynomial.coeff (tagMonomial S) (mlProj (boolFactorDerivProd T)) =
    (2 : ℚ) ^ (S ∩ T).card := by
  rw [coeff_mlProj_of_isMultilinear_mono _ _ (tagMonomial_isMultilinear S)]
  exact coeff_tagMonomial_boolFactorDerivProd_samesize S T hcard

/-- Diagonal coefficient: coeff(tagMonomial S)(mlProj(boolFactorDerivProd S)) = 2^κ. -/
theorem coeff_mlProj_boolFactorDerivProd_diag {N : ℕ} (S : Finset (Fin N)) :
    MvPolynomial.coeff (tagMonomial S) (mlProj (boolFactorDerivProd S)) =
    (2 : ℚ) ^ S.card := by
  rw [coeff_mlProj_of_isMultilinear_mono _ _ (tagMonomial_isMultilinear S)]
  exact coeff_tagMonomial_boolFactorDerivProd_diag S

/-- Off-diagonal coefficient for disjoint subsets:
    coeff(tagMonomial S)(mlProj(boolFactorDerivProd T)) = 1 when S, T disjoint
    and |S|=|T|. -/
theorem coeff_mlProj_boolFactorDerivProd_disjoint {N : ℕ}
    (S T : Finset (Fin N)) (hcard : S.card = T.card)
    (hdisj : Disjoint S T) :
    MvPolynomial.coeff (tagMonomial S) (mlProj (boolFactorDerivProd T)) = 1 := by
  rw [coeff_mlProj_of_isMultilinear_mono _ _ (tagMonomial_isMultilinear S)]
  exact coeff_tagMonomial_boolFactorDerivProd_disjoint S T hcard hdisj

/-! ## Linear independence of mlProj(boolFactorDerivProd) for disjoint families -/

/-- Coefficient extraction from a linear combination of mlProj(boolFactorDerivProd). -/
theorem coeff_mlProj_sum_smul {N : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset (Fin N))
    (c : ι → ℚ) (m : Fin N →₀ ℕ) :
    MvPolynomial.coeff m
      (∑ i ∈ s, c i • mlProj (boolFactorDerivProd (f i))) =
    ∑ i ∈ s, c i * MvPolynomial.coeff m (mlProj (boolFactorDerivProd (f i))) := by
  simp [coeff_sum, coeff_smul, smul_eq_mul]

/-- For pairwise disjoint κ-subsets (κ ≥ 1), the mlProj(boolFactorDerivProd S)
    are linearly independent.

    The proof mirrors linearIndependent_boolFactorDerivProd_disjoint but works
    with mlProj'd polynomials, using coeff_mlProj_of_isMultilinear_mono to
    transfer the Kronecker δ through mlProj. -/
theorem linearIndependent_mlProj_boolFactorDerivProd_disjoint {N κ : ℕ} (hκ : κ ≥ 1)
    {F : Finset (Finset (Fin N))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hdisj : (F : Set (Finset (Fin N))).PairwiseDisjoint id) :
    LinearIndependent ℚ (fun S : F => mlProj (boolFactorDerivProd (S : Finset (Fin N)))) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  -- Build c : Finset (Fin N) → ℚ from w
  set c : Finset (Fin N) → ℚ := fun S =>
    if h : S ∈ F then
      if ⟨S, h⟩ ∈ s then w ⟨S, h⟩ else 0
    else 0 with hc_def
  -- The linear combination over F equals ∑ over s
  have hzero_F : ∑ S ∈ F, c S • mlProj (boolFactorDerivProd S) = 0 := by
    have : ∑ S ∈ F, c S • mlProj (boolFactorDerivProd S) =
        ∑ S ∈ s, w S • mlProj (boolFactorDerivProd (S : Finset (Fin N))) := by
      rw [show (∑ S ∈ F, c S • mlProj (boolFactorDerivProd S)) =
          (∑ S ∈ F.attach, c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N)))) from by
        rw [Finset.sum_attach F (fun S => c S • mlProj (boolFactorDerivProd S))]]
      have hsplit : ∑ S ∈ F.attach, c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) =
          ∑ S ∈ F.attach.filter (fun S => S ∈ s), c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) +
          ∑ S ∈ F.attach.filter (fun S => S ∉ s), c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) := by
        rw [← Finset.sum_filter_add_sum_filter_not F.attach (fun S => S ∈ s)]
      rw [hsplit]
      have hzero_part : ∑ S ∈ F.attach.filter (fun S => S ∉ s),
          c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) = 0 := by
        apply Finset.sum_eq_zero
        intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        have : c S = 0 := by
          simp only [hc_def, dif_pos hSF, if_neg hmem]
        rw [this, zero_smul]
      rw [hzero_part, add_zero]
      apply Finset.sum_nbij (fun S => S)
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        exact hmem
      · intro ⟨S₁, h₁⟩ _ ⟨S₂, h₂⟩ _ heq
        exact heq
      · intro ⟨S, hSF⟩ hmem
        exact ⟨⟨S, hSF⟩, by simp [hmem], rfl⟩
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        simp only [hc_def, dif_pos hSF, if_pos hmem]
    rw [this, hw]
  -- Establish the matrix equation for arbitrary T ∈ F:
  -- c_T * 2^κ + ∑_{S ∈ F\{T}} c_S = 0 (by extracting tagMonomial T coefficient)
  have hextract : ∀ T ∈ F, c T * (2 : ℚ) ^ κ + ∑ U ∈ F.erase T, c U = 0 := by
    intro T hTF
    have hcoeff_T : MvPolynomial.coeff (tagMonomial T)
        (∑ S ∈ F, c S • mlProj (boolFactorDerivProd S)) = 0 := by
      rw [hzero_F]; simp [MvPolynomial.coeff_zero]
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_T
    rw [← Finset.add_sum_erase F _ hTF] at hcoeff_T
    have hd : c T * MvPolynomial.coeff (tagMonomial T) (mlProj (boolFactorDerivProd T)) =
        c T * (2 : ℚ) ^ κ := by
      rw [coeff_mlProj_boolFactorDerivProd_diag, hcard T hTF]
    rw [hd] at hcoeff_T
    have hod : ∑ S ∈ F.erase T, c S *
        MvPolynomial.coeff (tagMonomial T) (mlProj (boolFactorDerivProd S)) =
        ∑ S ∈ F.erase T, c S := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSF := Finset.mem_of_mem_erase hS
      have hne := Finset.ne_of_mem_erase hS
      rw [coeff_mlProj_boolFactorDerivProd_disjoint T S
        (by rw [hcard T hTF, hcard S hSF]) (hdisj hTF hSF (Ne.symm hne))]
      ring
    rw [hod] at hcoeff_T
    linarith
  -- Now derive c_i = 0 using the same algebraic argument
  set ctotal := ∑ S ∈ F, c S with hctotal_def
  have hrewrite : ∀ S ∈ F, c S * ((2 : ℚ) ^ κ - 1) + ctotal = 0 := by
    intro S hS
    have h1 := hextract S hS
    have h2 : ∑ U ∈ F.erase S, c U = ctotal - c S := by
      rw [hctotal_def, ← Finset.add_sum_erase F _ hS]; ring
    rw [h2] at h1; linarith
  have h2k_ne : (2 : ℚ) ^ κ - 1 ≠ 0 := by
    suffices (2 : ℚ) ^ κ ≥ 2 by linarith
    have : 2 ^ 1 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
    exact_mod_cast (show 2 ≤ 2 ^ κ from by simpa using this)
  have hall_same : ∀ S ∈ F, c S = c (i : Finset (Fin N)) := by
    intro S hS
    have h1 := hrewrite S hS
    have h2 : c S * ((2 : ℚ) ^ κ - 1) = c (i : Finset (Fin N)) * ((2 : ℚ) ^ κ - 1) := by
      linarith [hrewrite (i : Finset (Fin N)) i.2]
    exact mul_right_cancel₀ h2k_ne h2
  have hsum_eq : ctotal = ↑F.card * c (i : Finset (Fin N)) := by
    rw [hctotal_def, show ∑ S ∈ F, c S = ∑ S ∈ F, c (i : Finset (Fin N)) from
      Finset.sum_congr rfl (fun S hS => hall_same S hS)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcombine : c (i : Finset (Fin N)) * ((2 : ℚ) ^ κ - 1 + ↑F.card) = 0 := by
    linarith [hrewrite (i : Finset (Fin N)) i.2]
  have hpos : (2 : ℚ) ^ κ - 1 + ↑F.card > 0 := by
    have h2k : (2 : ℚ) ^ κ ≥ 2 := by
      have : 2 ^ 1 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
      exact_mod_cast (show 2 ≤ 2 ^ κ from by simpa using this)
    have : (0 : ℚ) ≤ ↑F.card := Nat.cast_nonneg F.card
    linarith
  have hci : c (i : Finset (Fin N)) = 0 :=
    (mul_eq_zero.mp hcombine).resolve_right (ne_of_gt hpos)
  simp only [hc_def, dif_pos i.2, if_pos hi] at hci
  exact hci

/-! ## Non-disjoint linear independence via sum-of-squares -/

/-- Equal-size finsets: if S ⊆ T and |S| = |T| then S = T. -/
theorem Finset.eq_of_subset_of_card_eq {α : Type*} [DecidableEq α]
    {S T : Finset α} (hsub : S ⊆ T) (hcard : S.card = T.card) :
    S = T :=
  Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-- Number of subsets of a finset S equals 2^|S|. -/
theorem Finset.card_powerset' {α : Type*} [DecidableEq α] (S : Finset α) :
    S.powerset.card = 2 ^ S.card :=
  Finset.card_powerset S

/-- Indicator function: 1 if U ⊆ S, 0 otherwise. -/
noncomputable def zetaIndicator {N : ℕ} (S : Finset (Fin N)) (U : Finset (Fin N)) : ℚ :=
  if U ⊆ S then 1 else 0

/-- The inner product ∑_U zetaIndicator S U * zetaIndicator T U equals 2^|S ∩ T|. -/
theorem zetaIndicator_inner_product {N : ℕ} (S T : Finset (Fin N)) :
    ∑ U ∈ (Finset.univ : Finset (Fin N)).powerset,
      zetaIndicator S U * zetaIndicator T U =
    (2 : ℚ) ^ (S ∩ T).card := by
  simp only [zetaIndicator]
  -- Simplify (if U ⊆ S then 1 else 0) * (if U ⊆ T then 1 else 0)
  -- into (if U ⊆ S ∩ T then 1 else 0)
  have hsimp : ∀ U, (if U ⊆ S then (1 : ℚ) else 0) * (if U ⊆ T then 1 else 0) =
      if U ⊆ S ∩ T then 1 else 0 := by
    intro U
    by_cases h1 : U ⊆ S <;> by_cases h2 : U ⊆ T <;> simp_all [Finset.subset_inter_iff]
  simp_rw [hsimp]
  -- Sum of (if U ⊆ S ∩ T then 1 else 0) = |{U ∈ powerset(univ) : U ⊆ S ∩ T}|
  rw [Finset.sum_boole]
  -- The filter is just the powerset of S ∩ T
  have hfilt : ((Finset.univ : Finset (Fin N)).powerset.filter (· ⊆ S ∩ T)) =
      (S ∩ T).powerset := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Finset.subset_univ U, h⟩⟩
  rw [hfilt, Finset.card_powerset]
  push_cast
  ring

/-- Sum of squares over ℚ: if ∑ a² = 0 then each a = 0. -/
theorem sum_sq_eq_zero_imp {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → ℚ}
    (h : ∑ i ∈ s, a i ^ 2 = 0) : ∀ i ∈ s, a i = 0 := by
  intro i hi
  have hnn : ∀ j ∈ s, (0 : ℚ) ≤ a j ^ 2 := fun j _ => sq_nonneg (a j)
  have := Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp h i hi
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this

/-- For distinct equal-size κ-subsets (κ ≥ 1), the mlProj(boolFactorDerivProd S) are
    linearly independent.

    This generalises linearIndependent_mlProj_boolFactorDerivProd_disjoint by
    removing the disjointness hypothesis.  The proof uses the sum-of-squares
    / Gram-matrix argument: the matrix M_{S,T} = 2^|S∩T| is the Gram matrix
    of indicator vectors ζ_S, hence positive semi-definite, and its kernel
    is trivial because evaluating ∑ c_i ζ_{S_i} at U = S_j gives c_j
    (using the equal-size distinctness). -/
theorem linearIndependent_mlProj_boolFactorDerivProd_general {N κ : ℕ} (hκ : κ ≥ 1)
    {F : Finset (Finset (Fin N))}
    (hcard : ∀ S ∈ F, S.card = κ) :
    LinearIndependent ℚ (fun S : F => mlProj (boolFactorDerivProd (S : Finset (Fin N)))) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  -- Build c : Finset (Fin N) → ℚ from w
  set c : Finset (Fin N) → ℚ := fun S =>
    if h : S ∈ F then
      if ⟨S, h⟩ ∈ s then w ⟨S, h⟩ else 0
    else 0 with hc_def
  -- The linear combination over F equals ∑ over s
  have hzero_F : ∑ S ∈ F, c S • mlProj (boolFactorDerivProd S) = 0 := by
    have : ∑ S ∈ F, c S • mlProj (boolFactorDerivProd S) =
        ∑ S ∈ s, w S • mlProj (boolFactorDerivProd (S : Finset (Fin N))) := by
      rw [show (∑ S ∈ F, c S • mlProj (boolFactorDerivProd S)) =
          (∑ S ∈ F.attach, c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N)))) from by
        rw [Finset.sum_attach F (fun S => c S • mlProj (boolFactorDerivProd S))]]
      have hsplit : ∑ S ∈ F.attach, c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) =
          ∑ S ∈ F.attach.filter (fun S => S ∈ s), c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) +
          ∑ S ∈ F.attach.filter (fun S => S ∉ s), c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) := by
        rw [← Finset.sum_filter_add_sum_filter_not F.attach (fun S => S ∈ s)]
      rw [hsplit]
      have hzero_part : ∑ S ∈ F.attach.filter (fun S => S ∉ s),
          c (S : Finset (Fin N)) • mlProj (boolFactorDerivProd (S : Finset (Fin N))) = 0 := by
        apply Finset.sum_eq_zero
        intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        have : c S = 0 := by
          simp only [hc_def, dif_pos hSF, if_neg hmem]
        rw [this, zero_smul]
      rw [hzero_part, add_zero]
      apply Finset.sum_nbij (fun S => S)
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        exact hmem
      · intro ⟨S₁, h₁⟩ _ ⟨S₂, h₂⟩ _ heq
        exact heq
      · intro ⟨S, hSF⟩ hmem
        exact ⟨⟨S, hSF⟩, by simp [hmem], rfl⟩
      · intro ⟨S, hSF⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hmem
        simp only [hc_def, dif_pos hSF, if_pos hmem]
    rw [this, hw]
  -- Extract coefficient at tagMonomial T for each T ∈ F
  have hextract : ∀ T ∈ F, ∑ S ∈ F, c S * (2 : ℚ) ^ (T ∩ S).card = 0 := by
    intro T hTF
    have hcoeff_T : MvPolynomial.coeff (tagMonomial T)
        (∑ S ∈ F, c S • mlProj (boolFactorDerivProd S)) = 0 := by
      rw [hzero_F]; simp [MvPolynomial.coeff_zero]
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at hcoeff_T
    convert hcoeff_T using 1
    apply Finset.sum_congr rfl
    intro S hS
    rw [coeff_mlProj_boolFactorDerivProd_samesize T S (by rw [hcard T hTF, hcard S hS])]
  -- Sum-of-squares argument:
  -- ∑_{S,T ∈ F} c_S * c_T * 2^|S∩T|
  --   = ∑_T c_T * (∑_S c_S * 2^|S∩T|)  [by the extracted equations]
  --   = ∑_T c_T * 0 = 0
  have hquad_zero : ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    rw [show ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card =
        c T * ∑ S ∈ F, c S * (2 : ℚ) ^ (T ∩ S).card from by
      rw [Finset.mul_sum]; congr 1; ext S; ring]
    rw [hextract T hT, mul_zero]
  -- Now define g(U) = ∑_{S ∈ F} c_S * zetaIndicator S U
  set g : Finset (Fin N) → ℚ := fun U => ∑ S ∈ F, c S * zetaIndicator S U with hg_def
  -- Show ∑_U g(U)^2 = ∑_{S,T} c_S c_T * 2^|S∩T| = 0
  set allSubsets := (Finset.univ : Finset (Fin N)).powerset with hall_def
  have hg_sq_eq : ∑ U ∈ allSubsets, g U ^ 2 =
      ∑ T ∈ F, ∑ S ∈ F, c T * c S * (2 : ℚ) ^ (T ∩ S).card := by
    -- g(U)^2 = (∑_S c_S * ζ_S(U))^2 = ∑_{S,T} c_S c_T * ζ_S(U) * ζ_T(U)
    simp only [hg_def, sq]
    -- Step 1: expand product of sums
    simp_rw [Finset.sum_mul_sum]
    -- Step 2: swap order of summation ∑_U ∑_T ∑_S → ∑_T ∑_S ∑_U
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1
    funext T
    rw [Finset.sum_comm (s := allSubsets) (t := F)]
    congr 1
    funext S
    -- Step 3: factor out c_T * c_S
    rw [show ∑ U ∈ allSubsets,
        (c T * zetaIndicator T U) * (c S * zetaIndicator S U) =
        c T * c S * ∑ U ∈ allSubsets, zetaIndicator T U * zetaIndicator S U from by
      rw [Finset.mul_sum]; congr 1; funext U; ring]
    rw [zetaIndicator_inner_product]
  -- Combined: ∑_U g(U)^2 = 0
  have hg_sq_zero : ∑ U ∈ allSubsets, g U ^ 2 = 0 := by
    rw [hg_sq_eq, hquad_zero]
  -- Since sum of squares = 0 over ℚ, each g(U) = 0
  have hg_zero : ∀ U ∈ allSubsets, g U = 0 := by
    exact sum_sq_eq_zero_imp hg_sq_zero
  -- Evaluate g at U = S_j: g(S_j) = c_{S_j}
  -- because ζ_{S_i}(S_j) = 1_{S_j ⊆ S_i} = 1_{S_j = S_i} for same-size distinct subsets
  have hg_eval : ∀ T ∈ F, g T = c T := by
    intro T hTF
    show ∑ S ∈ F, c S * zetaIndicator S T = c T
    rw [show ∑ S ∈ F, c S * zetaIndicator S T =
        c T * zetaIndicator T T + ∑ S ∈ F.erase T, c S * zetaIndicator S T from by
      rw [← Finset.add_sum_erase F _ hTF]]
    have h_diag : zetaIndicator T T = 1 := by
      simp [zetaIndicator]
    rw [h_diag, mul_one]
    suffices h : ∑ S ∈ F.erase T, c S * zetaIndicator S T = 0 by linarith
    apply Finset.sum_eq_zero
    intro S hS
    have hSF := Finset.mem_of_mem_erase hS
    have hne := Finset.ne_of_mem_erase hS
    have h_off : zetaIndicator S T = 0 := by
      simp only [zetaIndicator]
      rw [if_neg]
      intro hsub
      have := Finset.eq_of_subset_of_card_eq hsub (by rw [hcard T hTF, hcard S hSF])
      exact hne (this.symm)
    rw [h_off, mul_zero]
  -- Conclude c_i = 0
  have hci : c (i : Finset (Fin N)) = 0 := by
    have hT_mem : (i : Finset (Fin N)) ∈ allSubsets := by
      simp only [hall_def, Finset.mem_powerset]
      exact Finset.subset_univ _
    have := hg_zero _ hT_mem
    rw [hg_eval (i : Finset (Fin N)) i.2] at this
    exact this
  simp only [hc_def, dif_pos i.2, if_pos hi] at hci
  exact hci

/-! ## Main result: mlBlockedSpdpRank lower bound for disjoint families -/

/-- For m pairwise disjoint, block-admissible κ-subsets (κ ≥ 1) of Fin N,
    mlBlockedSpdpRank B κ 0 (boolFactorFullProd N) ≥ m.

    This bridges from the unblocked spdpRank_ge_of_disjoint_family to the
    blocked multilinear SPDP rank. -/
theorem mlBlockedSpdpRank_ge_of_disjoint_family {N κ : ℕ} (hκ : κ ≥ 1)
    (B : BlockPartition N)
    {F : Finset (Finset (Fin N))}
    (hcard : ∀ S ∈ F, S.card = κ)
    (hdisj : (F : Set (Finset (Fin N))).PairwiseDisjoint id)
    (hadm : ∀ S ∈ F, isBlockAdmissible B S.toList) :
    F.card ≤ mlBlockedSpdpRank B κ 0 (boolFactorFullProd N) := by
  -- Linear independence of mlProj(boolFactorDerivProd S) for S ∈ F
  have hli := linearIndependent_mlProj_boolFactorDerivProd_disjoint hκ hcard hdisj
  -- Each mlProj(boolFactorDerivProd S) lies in mlBlockedSpdpSubspace
  have hmem : ∀ (S : F), mlProj (boolFactorDerivProd (S : Finset (Fin N))) ∈
      mlBlockedSpdpSubspace B κ 0 (boolFactorFullProd N) := by
    intro ⟨S, hS⟩
    exact mlProj_boolFactorDerivProd_mem_mlBlockedSpdpSubspace B κ 0 S (hcard S hS) (hadm S hS)
  -- Embed into the subspace
  unfold mlBlockedSpdpRank
  set f : F → mlBlockedSpdpSubspace B κ 0 (boolFactorFullProd N) :=
    fun S => ⟨mlProj (boolFactorDerivProd (S : Finset (Fin N))), hmem S⟩ with hf_def
  have hli_sub : LinearIndependent ℚ f := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i' hi'
    apply hli s w _ i' hi'
    have hval : (∑ j ∈ s, w j • f j).val =
        (0 : mlBlockedSpdpSubspace B κ 0 (boolFactorFullProd N)).val :=
      congr_arg Subtype.val hw
    simp only [hf_def, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk,
      Submodule.coe_zero, ZeroMemClass.coe_zero] at hval
    exact hval
  rw [show F.card = Fintype.card F from (Fintype.card_coe F).symm]
  exact hli_sub.fintype_card_le_finrank

end BlockedBoolRank
