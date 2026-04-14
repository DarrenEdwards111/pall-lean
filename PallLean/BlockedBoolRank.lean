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
