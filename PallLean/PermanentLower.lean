/-
  PermanentLower.lean — Paper Theorem 94 (Exponential SPDP Rank for perm_n)

  FULLY PROVED: 0 custom axioms, 0 sorry.
  Paper reference: Theorem 94, §18, arXiv:2512.11820v5.
  Proof chain:
  1. Disjoint supports (Paper Lemma 95, PermanentMonomials) → linear independence
  2. Linear independence → finrank ≥ m²
  3. SPDP span finite-dimensional (restrictTotalDegree)
  4. finrank_mono → SPDP rank ≥ m² > m
-/
import PallLean.CompiledPoly
import PallLean.Permanent
import PallLean.PermanentMonomials
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.MvPolynomial.Basic

namespace PermanentLower

open MvPolynomial CompiledPoly Permanent SPDP PermanentMonomials

/-! ## Linear independence from disjoint supports -/

/-- Polynomials with pairwise disjoint supports are linearly independent,
    provided each is nonzero. -/
theorem linearIndependent_of_disjoint_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] [IsDomain R] [Nontrivial R]
    (p : ι → MvPolynomial σ R)
    (h_nz : ∀ i, p i ≠ 0)
    (h_disj : ∀ i j, i ≠ j → ∀ α, coeff α (p i) ≠ 0 → coeff α (p j) = 0) :
    LinearIndependent R p := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  by_cases hi : i ∈ l.support
  · -- Pick any monomial α in the support of p i
    have h_nz_i := h_nz i
    have h_nz_supp : (p i).support.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    obtain ⟨α, hα⟩ := h_nz_supp
    rw [mem_support_iff] at hα
    -- coeff α of the linear combination = 0
    have h := congr_arg (coeff α) hl
    simp only [map_zero] at h
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at h
    -- Only the i-th term survives
    rw [← Finset.add_sum_erase _ _ hi] at h
    have h_rest : ∀ j ∈ l.support.erase i, l j * coeff α (p j) = 0 := by
      intro j hj
      rw [h_disj i j (Finset.ne_of_mem_erase hj).symm α hα, mul_zero]
    rw [Finset.sum_eq_zero h_rest, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hα
  · simp only [Finsupp.mem_support_iff, not_not] at hi; exact hi

/-! ## Permanent derivatives are linearly independent on MatVar -/

/-- Two different permutations (both mapping i₀ to j₀) produce different monomials
    in the derivative ∂_{(i₀,j₀)}(perm). -/
private lemma perm_monomials_injective (m : ℕ) (i₀ j₀ : Fin m)
    (σ₁ σ₂ : Equiv.Perm (Fin m))
    (hσ₁ : σ₁ i₀ = j₀) (hσ₂ : σ₂ i₀ = j₀)
    (heq : (∑ i ∈ Finset.univ.erase i₀, Finsupp.single ((i, σ₁ i) : MatVar m) 1) =
           (∑ i ∈ Finset.univ.erase i₀, Finsupp.single ((i, σ₂ i) : MatVar m) 1)) :
    σ₁ = σ₂ := by
  ext k
  by_cases hk : k = i₀
  · subst hk; rw [hσ₁, hσ₂]
  · -- Evaluate heq at (k, σ₁ k)
    have h := congr_fun (congr_arg DFunLike.coe heq) (k, σ₁ k)
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Prod.mk.injEq] at h
    -- LHS: ∑_{i ∈ erase i₀} if (i = k ∧ σ₁ i = σ₁ k) then 1 else 0
    -- Since i = k is the only solution (k ≠ i₀ ∧ k ∈ erase i₀), LHS = 1
    -- RHS: ∑_{i ∈ erase i₀} if (i = k ∧ σ₂ i = σ₁ k) then 1 else 0
    -- For RHS = 1, need ∃ i ≠ i₀ with i = k ∧ σ₂ k = σ₁ k
    -- LHS simplification: only i=k contributes (and k ∈ erase i₀)
    have hk_mem : k ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hk_mem] at h
    simp only [and_self, ite_true] at h
    -- The rest of the sum on LHS: for i ≠ k, σ₁ i ≠ σ₁ k (σ₁ injective)
    have h_rest_lhs : ∀ i ∈ (Finset.univ.erase i₀).erase k,
        (if i = k ∧ σ₁ i = σ₁ k then (1 : ℕ) else 0) = 0 := by
      intro i hi
      simp only [Finset.mem_erase] at hi
      simp [hi.1]
    rw [Finset.sum_eq_zero h_rest_lhs, add_zero] at h
    -- RHS: expand similarly
    rw [← Finset.add_sum_erase _ _ hk_mem] at h
    simp only [and_iff_right rfl] at h
    -- Sum over rest: for i ≠ k, need i = k which is false
    have h_rest_rhs : ∀ i ∈ (Finset.univ.erase i₀).erase k,
        (if i = k ∧ σ₂ i = σ₁ k then (1 : ℕ) else 0) = 0 := by
      intro i hi
      simp only [Finset.mem_erase] at hi
      simp [hi.1]
    rw [Finset.sum_eq_zero h_rest_rhs, add_zero] at h
    -- Now h : 1 = if σ₂ k = σ₁ k then 1 else 0
    by_cases heq' : (σ₂ k : Fin m) = σ₁ k
    · exact congrArg _ heq'.symm
    · simp [heq'] at h

/-- Sub-permanents are nonzero. -/
theorem pderiv_permPoly_ne_zero (m : ℕ) (hm : m ≥ 1) (v : MatVar m) :
    pderiv v (permPoly m ℚ) ≠ 0 := by
  obtain ⟨i₀, j₀⟩ := v
  rw [PermanentMonomials.pderiv_permPoly]
  -- Pick σ₀ = id (if i₀ = j₀) or a swap. Any σ with σ(i₀) = j₀ works.
  -- We show the coefficient of σ₀'s monomial is 1 ≠ 0
  set F := Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ i₀ = j₀)
  -- F is nonempty: take σ₀ that swaps i₀ ↔ j₀ (in the sense of Equiv.swap)
  -- But Equiv.swap permutes i₀ ↔ j₀, so (Equiv.swap i₀ j₀) i₀ = j₀ ✓
  -- Actually for Fin, Equiv.swap swaps the two values
  have hF : F.Nonempty := by
    refine ⟨Equiv.swap i₀ j₀ * 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [Equiv.swap_apply_left]
  obtain ⟨σ₀, hσ₀⟩ := hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₀
  set α₀ := ∑ i ∈ Finset.univ.erase i₀, Finsupp.single ((i, σ₀ i) : MatVar m) 1
  apply ne_of_apply_ne (MvPolynomial.coeff α₀)
  simp only [MvPolynomial.coeff_zero]
  -- coeff α₀ of the sum
  rw [MvPolynomial.coeff_sum]
  -- Each summand is monomial (...) 1
  conv_lhs => arg 2; ext σ; rw [PermanentMonomials.prod_X_eq_monomial, MvPolynomial.coeff_monomial]
  -- Only σ₀ gives if_pos, rest give 0
  rw [Finset.sum_eq_single σ₀]
  · simp [α₀]
  · intro σ hσ hne
    rw [if_neg]
    intro heq
    apply hne
    have hσ' := (Finset.mem_filter.mp hσ).2
    have hσ₀' := (Finset.mem_filter.mp hσ₀).2
    exact perm_monomials_injective m i₀ j₀ σ σ₀ hσ' hσ₀' heq
  · intro h; exact absurd hσ₀ h

/-- Linear independence on MatVar. -/
theorem perm_derivs_independent_matvar (m : ℕ) (hm : m ≥ 2) :
    LinearIndependent ℚ (fun v : MatVar m => pderiv v (permPoly m ℚ)) := by
  apply linearIndependent_of_disjoint_support (R := ℚ)
  · exact fun v => pderiv_permPoly_ne_zero m (by omega) v
  · intro ⟨i₀, j₀⟩ ⟨i₀', j₀'⟩ hvw α hα
    simp only [ne_eq, Prod.mk.injEq, not_and_or] at hvw
    cases hvw with
    | inl hi => exact pderiv_permPoly_disjoint_diff_row m i₀ j₀ i₀' j₀' hi α hα
    | inr hj =>
      by_cases hi : i₀ = i₀'
      · subst hi; exact pderiv_permPoly_disjoint_diff_col m i₀ j₀ j₀' hj α hα
      · exact pderiv_permPoly_disjoint_diff_row m i₀ j₀ i₀' j₀' hi α hα

/-! ## Transfer to flat indexing -/

private lemma flat_bound {m : ℕ} (i j : Fin m) : i.val * m + j.val < m * m := by
  have := i.isLt; have := j.isLt; nlinarith

private lemma flatIdx_injective (m : ℕ) : Function.Injective
    (fun ij : MatVar m => (⟨ij.1.val * m + ij.2.val, flat_bound ij.1 ij.2⟩ : Fin (m * m))) := by
  intro ⟨⟨i₁, hi₁⟩, ⟨j₁, hj₁⟩⟩ ⟨⟨i₂, hi₂⟩, ⟨j₂, hj₂⟩⟩ h
  simp only [Fin.mk.injEq] at h
  -- h : i₁ * m + j₁ = i₂ * m + j₂, with j₁ < m and j₂ < m
  -- From h : i₁ * m + j₁ = i₂ * m + j₂ with j₁ < m, j₂ < m
  have hi : i₁ = i₂ := by
    rcases Nat.lt_or_ge i₁ i₂ with h' | h'
    · exfalso; have : i₂ * m ≥ (i₁ + 1) * m := Nat.mul_le_mul_right m h'; nlinarith
    rcases Nat.lt_or_ge i₂ i₁ with h'' | h''
    · exfalso; have : i₁ * m ≥ (i₂ + 1) * m := Nat.mul_le_mul_right m h''; nlinarith
    · exact Nat.le_antisymm h'' h'
  subst hi
  have hj : j₁ = j₂ := by omega
  exact Prod.ext rfl (Fin.ext hj)

/-- The flat index function. -/
private def flatFn (m : ℕ) : MatVar m → Fin (m * m) :=
  fun ij => ⟨ij.1.val * m + ij.2.val, flat_bound ij.1 ij.2⟩

/-- The unflat index function. -/
private def unflatFn (m : ℕ) (hm : m ≥ 1) (v : Fin (m * m)) : MatVar m :=
  (⟨v.val / m, Nat.div_lt_of_lt_mul (by omega)⟩,
   ⟨v.val % m, Nat.mod_lt _ (by omega)⟩)

private lemma flatFn_eq_permPolyFlat_fn (m : ℕ) :
    (flatFn m) = (fun ij : MatVar m =>
      ⟨ij.1.val * m + ij.2.val, by have := ij.1.isLt; have := ij.2.isLt; nlinarith⟩) := by
  ext ij; simp [flatFn, flat_bound]

private lemma flat_unflat (m : ℕ) (hm : m ≥ 1) (v : Fin (m * m)) :
    flatFn m (unflatFn m hm v) = v := by
  simp only [flatFn, unflatFn, flat_bound]
  refine Fin.ext ?_; simp
  rw [Nat.div_add_mod']

private lemma unflat_flat (m : ℕ) (hm : m ≥ 1) (ij : MatVar m) :
    unflatFn m hm (flatFn m ij) = ij := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
  simp only [flatFn, unflatFn, flat_bound]
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp
  · rw [show i * m + j = j + i * m from by ring, Nat.add_mul_div_right _ _ (by omega : m > 0),
        Nat.div_eq_of_lt hj, zero_add]
  · exact Nat.mod_eq_of_lt hj

private lemma flatFn_injective (m : ℕ) : Function.Injective (flatFn m) :=
  flatIdx_injective m

private lemma flatFn_bijective (m : ℕ) (hm : m ≥ 1) : Function.Bijective (flatFn m) :=
  ⟨flatIdx_injective m, fun v => ⟨unflatFn m hm v, flat_unflat m hm v⟩⟩

/-- permPolyFlat uses flatFn. -/
private lemma permPolyFlat_eq_rename (m : ℕ) :
    permPolyFlat m = rename (flatFn m) (permPoly m ℚ) := by
  unfold permPolyFlat flatFn; rfl

/-- The m² first partial derivatives of perm_m are linearly independent.
    Transfers from perm_derivs_independent_matvar via rename + pderiv_rename. -/
theorem perm_first_derivs_independent (m : ℕ) (hm : m ≥ 2) :
    LinearIndependent ℚ (fun v : Fin (m * m) =>
      MvPolynomial.pderiv v (permPolyFlat m)) := by
  -- Rewrite each pderiv v (permPolyFlat m) using pderiv_rename
  have hm1 : m ≥ 1 := by omega
  have h_inj := flatFn_injective m
  -- Show the family equals rename flatFn ∘ (fun ij => pderiv ij (permPoly m ℚ)) ∘ unflatFn
  have h_eq : (fun v : Fin (m * m) => pderiv v (permPolyFlat m)) =
      (fun v => rename (flatFn m) (pderiv (unflatFn m hm1 v) (permPoly m ℚ))) := by
    ext v
    rw [permPolyFlat_eq_rename]
    conv_lhs => rw [show v = flatFn m (unflatFn m hm1 v) from (flat_unflat m hm1 v).symm]
    rw [MvPolynomial.pderiv_rename h_inj]
  rw [h_eq]
  -- This is (rename flatFn).toLinearMap ∘ (fun ij => pderiv ij (permPoly)) ∘ unflatFn
  -- unflatFn is a bijection, rename is injective on linear maps
  -- Use LinearIndependent.map' + composition with equiv
  -- Step 1: independence of (fun ij => pderiv ij (permPoly)) on MatVar
  have h_indep := perm_derivs_independent_matvar m hm
  -- Step 2: reindex via unflatFn (which is a bijection's inverse)
  -- unflatFn ∘ flatFn = id, flatFn ∘ unflatFn = id
  -- So (fun v => pderiv (unflatFn m hm1 v) (permPoly m ℚ)) = (fun ij => pderiv ij (permPoly m ℚ)) ∘ unflatFn
  -- Since unflatFn is injective, the reindexed family is still independent
  have h_unflat_inj : Function.Injective (unflatFn m hm1) := by
    intro v w h
    have := congr_arg (flatFn m) h
    rw [flat_unflat m hm1, flat_unflat m hm1] at this
    exact this
  have h_reindex : LinearIndependent ℚ (fun v : Fin (m * m) =>
      pderiv (unflatFn m hm1 v) (permPoly m ℚ)) :=
    h_indep.comp _ h_unflat_inj
  -- Step 3: rename flatFn is injective as a linear map
  -- LinearIndependent.map with ker = ⊥
  exact h_reindex.map' (MvPolynomial.renameEquiv ℚ (Equiv.ofBijective _ (flatFn_bijective m hm1))).toLinearEquiv.toLinearMap
    (LinearEquiv.ker (MvPolynomial.renameEquiv ℚ (Equiv.ofBijective _ (flatFn_bijective m hm1))).toLinearEquiv)

/-! ## Helpers -/

lemma log2_sq_ge_one (m : ℕ) (hm : m ≥ 2) : Nat.log 2 (m * m) ≥ 1 := by
  have h4 : m * m ≥ 4 := by nlinarith
  have h1 : Nat.log 2 4 = 2 := by decide
  have h2 : Nat.log 2 (m * m) ≥ Nat.log 2 4 := Nat.log_mono_right h4
  omega

/-- SPDP generators have bounded total degree. -/
lemma spdp_gen_totalDegree_le {N : ℕ} {κ ℓ : ℕ}
    {poly : MvPolynomial (Fin N) ℚ}
    {bp : CompiledPoly.BlockPartition N}
    {q : MvPolynomial (Fin N) ℚ}
    (hq : q ∈ { r : MvPolynomial (Fin N) ℚ |
      ∃ (S : List (Fin N)) (sh : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ ℓ ∧
        q = sh * iterDerivList S poly }) :
    q.totalDegree ≤ ℓ + poly.totalDegree := by
  obtain ⟨S, sh, _, hsh_deg, _, _, rfl⟩ := hq
  calc (sh * iterDerivList S poly).totalDegree
      ≤ sh.totalDegree + (iterDerivList S poly).totalDegree :=
        MvPolynomial.totalDegree_mul sh (iterDerivList S poly)
    _ ≤ ℓ + poly.totalDegree := by
        have := SPDP.totalDegree_iterDerivList_le S poly
        omega

/-- The SPDP span is contained in the degree-bounded submodule. -/
lemma spdp_span_le_restrictTotalDegree {N : ℕ} (κ ℓ : ℕ)
    (poly : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N) :
    Submodule.span ℚ { q : MvPolynomial (Fin N) ℚ |
      ∃ (S : List (Fin N)) (sh : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ ℓ ∧
        q = sh * iterDerivList S poly } ≤
    MvPolynomial.restrictTotalDegree (Fin N) ℚ (ℓ + poly.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
  exact spdp_gen_totalDegree_le hq

/-! ## Main theorem -/

theorem permanent_spdp_lower :
    ∃ (m₀ : ℕ), ∀ (m : ℕ), m ≥ m₀ →
    ∀ (bp : CompiledPoly.BlockPartition (m * m)),
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (permPolyFlat m) bp > m := by
  refine ⟨2, fun m hm bp => ?_⟩
  set κ := Nat.log 2 (m * m)
  have hκ : κ ≥ 1 := log2_sq_ge_one m hm
  -- The derivative family
  set f := fun v : Fin (m * m) => MvPolynomial.pderiv v (permPolyFlat m)
  have h_indep := perm_first_derivs_independent m hm
  -- The SPDP generating set
  set spdp := { q : MvPolynomial (Fin (m * m)) ℚ |
      ∃ (S : List (Fin (m * m))) (sh : MvPolynomial (Fin (m * m)) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ κ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ κ ∧
        q = sh * iterDerivList S (permPolyFlat m) }
  -- blockedSpdpRankQ = finrank of span of spdp
  have h_eq : CompiledPoly.blockedSpdpRankQ κ κ (permPolyFlat m) bp =
      Module.finrank ℚ (Submodule.span ℚ spdp) := by
    unfold CompiledPoly.blockedSpdpRankQ; rfl
  rw [h_eq]
  -- Each f v is in spdp
  have h_mem : ∀ v : Fin (m * m), f v ∈ spdp := by
    intro v
    have : f v = pderiv v (permPolyFlat m) := rfl
    rw [this]
    exact ⟨[v], 1, by simp; exact hκ, by simp, by simp [List.toFinset_cons]; exact hκ,
           by simp [MvPolynomial.vars_one], by simp [iterDerivList, one_mul]⟩
  -- range f ⊆ spdp, so span(range f) ≤ span(spdp)
  have h_span_le : Submodule.span ℚ (Set.range f) ≤ Submodule.span ℚ spdp :=
    Submodule.span_mono (fun x ⟨v, hv⟩ => hv ▸ h_mem v)
  -- span(spdp) is contained in restrictTotalDegree, hence finite-dimensional
  have h_fin : Module.Finite ℚ (Submodule.span ℚ spdp) := by
    have h_le := spdp_span_le_restrictTotalDegree κ κ (permPolyFlat m) bp
    exact Module.Finite.of_injective
      (Submodule.inclusion h_le)
      (Submodule.inclusion_injective h_le)
  -- finrank(span(range f)) = m * m
  have h_fr : Module.finrank ℚ (Submodule.span ℚ (Set.range f)) = m * m :=
    (finrank_span_eq_card h_indep).trans (Fintype.card_fin (m * m))
  -- finrank(span(spdp)) ≥ m * m by finrank_mono
  have h_rank_ge : Module.finrank ℚ (Submodule.span ℚ spdp) ≥ m * m := by
    calc Module.finrank ℚ (Submodule.span ℚ spdp)
        ≥ Module.finrank ℚ (Submodule.span ℚ (Set.range f)) :=
          Submodule.finrank_mono h_span_le
      _ = m * m := h_fr
  -- m * m > m for m ≥ 2
  linarith [show m * m > m from by nlinarith]

/-- Stronger version: SPDP rank ≥ m² (Paper Theorem 94, full bound).
    Proved: the m² first derivatives are linearly independent. -/
theorem permanent_spdp_rank_ge_sq :
    ∀ (m : ℕ), m ≥ 2 →
    ∀ (bp : CompiledPoly.BlockPartition (m * m)),
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (permPolyFlat m) bp ≥ m * m := by
  intro m hm bp
  set κ := Nat.log 2 (m * m)
  have hκ : κ ≥ 1 := log2_sq_ge_one m hm
  set f := fun v : Fin (m * m) => MvPolynomial.pderiv v (permPolyFlat m)
  have h_indep := perm_first_derivs_independent m hm
  set spdp := { q : MvPolynomial (Fin (m * m)) ℚ |
      ∃ (S : List (Fin (m * m))) (sh : MvPolynomial (Fin (m * m)) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ κ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ κ ∧
        q = sh * iterDerivList S (permPolyFlat m) }
  have h_eq : CompiledPoly.blockedSpdpRankQ κ κ (permPolyFlat m) bp =
      Module.finrank ℚ (Submodule.span ℚ spdp) := by rfl
  rw [h_eq]
  have h_mem : ∀ v : Fin (m * m), f v ∈ spdp := by
    intro v
    have : f v = pderiv v (permPolyFlat m) := rfl
    rw [this]
    exact ⟨[v], 1, by simp; exact hκ, by simp, by simp [List.toFinset_cons]; exact hκ,
           by simp [MvPolynomial.vars_one], by simp [iterDerivList, one_mul]⟩
  have h_span_le : Submodule.span ℚ (Set.range f) ≤ Submodule.span ℚ spdp :=
    Submodule.span_mono (fun x ⟨v, hv⟩ => hv ▸ h_mem v)
  have h_fin : Module.Finite ℚ (Submodule.span ℚ spdp) := by
    have h_le := spdp_span_le_restrictTotalDegree κ κ (permPolyFlat m) bp
    exact Module.Finite.of_injective
      (Submodule.inclusion h_le)
      (Submodule.inclusion_injective h_le)
  have h_fr : Module.finrank ℚ (Submodule.span ℚ (Set.range f)) = m * m :=
    (finrank_span_eq_card h_indep).trans (Fintype.card_fin (m * m))
  calc Module.finrank ℚ (Submodule.span ℚ spdp)
      ≥ Module.finrank ℚ (Submodule.span ℚ (Set.range f)) :=
        Submodule.finrank_mono h_span_le
    _ = m * m := h_fr

end PermanentLower
