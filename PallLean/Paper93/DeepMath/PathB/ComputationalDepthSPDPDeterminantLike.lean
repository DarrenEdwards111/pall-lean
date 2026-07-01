import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPFullProdLB

/-!
# A determinant-like family: SPDP rank of a two-block product sum

Applies the SPDP-rank machinery to a *sum of products* — the shape of the determinant/permanent — via the new
structural ingredient that **differentiating a product by an off-support variable vanishes** (`pderiv_prodX_zero`),
so a partial derivative picks out the term whose support it hits.

For a subset `s` and its complement `sᶜ`, the two-block polynomial `∏_{i∈s} Xᵢ + ∏_{i∈sᶜ} Xᵢ` has, for
`1 ≤ κ < |s|`:

  `spdpRank_twoBlock_ge` — `spdpRank κ 0 (∏_{i∈s} Xᵢ + ∏_{i∈sᶜ} Xᵢ) ≥ C(|s|, κ) + C(|sᶜ|, κ)`.

Both blocks contribute independently: differentiating by a `κ`-subset of `s` gives the `s`-complement monomial (the
`sᶜ`-term vanishes), and symmetrically; the two families of monomials have disjoint supports, so the ranks add — the
sum of products has strictly more SPDP rank than either product alone.

## Honest scope

This is a genuine SPDP-rank lower bound for a **sum-of-products** (determinant/permanent *shape*), but the two blocks
have **disjoint** variable supports — the read-once / block-diagonal simplification.  The *real* determinant /
permanent has **overlapping** monomials (`n!` permutation products on `n²` variables); its SPDP rank is the classic
`C(n,κ)²`-style bound whose use for an *explicit hard* family (`A3` hard-survival) is barriered short of `P/poly`.
This file does not cross that; it shows the machinery handles sums of products where the supports are disjoint.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Finset Module

variable {n : ℕ} {F : Type*} [Field F]

-- off-support derivative vanishes
theorem pderiv_prodX_zero (s : Finset (Fin n)) (k : Fin n) (hk : k ∉ s) :
    pderiv k (∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) = 0 := by
  rw [prodX_eq_monomial s, pderiv_monomial]
  convert monomial_zero using 2
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hk]
-- iterDerivList of 0 is 0
theorem iterDerivList_zero : ∀ (L : List (Fin n)),
    iterDerivList L (0 : MvPolynomial (Fin n) F) = 0
  | [] => rfl
  | k :: L' => by
      have : iterDerivList (k :: L') (0 : MvPolynomial (Fin n) F) = iterDerivList L' (pderiv k 0) := rfl
      rw [this, map_zero, iterDerivList_zero L']
-- iterDerivList is additive
theorem iterDerivList_add : ∀ (L : List (Fin n)) (a b : MvPolynomial (Fin n) F),
    iterDerivList L (a + b) = iterDerivList L a + iterDerivList L b
  | [], a, b => rfl
  | k :: L', a, b => by
      have h1 : iterDerivList (k :: L') (a + b) = iterDerivList L' (pderiv k (a + b)) := rfl
      have h2 : ∀ c : MvPolynomial (Fin n) F, iterDerivList (k :: L') c = iterDerivList L' (pderiv k c) := fun _ => rfl
      rw [h1, map_add, iterDerivList_add L', h2 a, h2 b]
-- indicator multidegree is injective in the set
theorem indicator_inj : Function.Injective
    (fun T : Finset (Fin n) => ∑ i ∈ T, Finsupp.single i (1 : ℕ)) := by
  intro T T' h
  ext j
  have hj := DFunLike.congr_fun h j
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at hj
  by_cases h1 : j ∈ T <;> by_cases h2 : j ∈ T' <;> simp_all
-- vanishing: derivative of a product by a nonempty off-support set is 0
theorem iterDeriv_prodX_vanish (U t : Finset (Fin n)) (hU : U.Nonempty) (hdisj : ∀ i ∈ U, i ∉ t) :
    iterDerivList U.toList (∏ i ∈ t, (X i : MvPolynomial (Fin n) F)) = 0 := by
  obtain ⟨k, rest, hc⟩ := List.exists_cons_of_ne_nil
    (fun h => hU.ne_empty (Finset.toList_eq_nil.mp h))
  have hk : k ∈ U := by rw [← Finset.mem_toList, hc]; simp
  have hstep : iterDerivList (k :: rest) (∏ i ∈ t, (X i : MvPolynomial (Fin n) F))
      = iterDerivList rest (pderiv k (∏ i ∈ t, X i)) := rfl
  rw [hc, hstep, pderiv_prodX_zero t k (hdisj k hk), iterDerivList_zero]

-- helper: reconstruct a subset from its complement within s
theorem sdiff_sdiff_self_of_subset {s U : Finset (Fin n)} (h : U ⊆ s) : s \ (s \ U) = U :=
  Finset.sdiff_sdiff_eq_self h

theorem spdpRank_twoBlock_ge (s : Finset (Fin n)) (κ : ℕ)
    (hκ1 : 1 ≤ κ) (hκs : κ < s.card) :
    s.card.choose κ + sᶜ.card.choose κ ≤
      spdpRank κ 0 ((∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) + ∏ i ∈ sᶜ, X i) := by
  classical
  set P : MvPolynomial (Fin n) F := (∏ i ∈ s, X i) + ∏ i ∈ sᶜ, X i with hP
  set f : ↥(s.powersetCard κ) → (Fin n →₀ ℕ) := fun U => ∑ i ∈ s \ U.1, Finsupp.single i 1 with hf
  set g : ↥(sᶜ.powersetCard κ) → (Fin n →₀ ℕ) := fun V => ∑ i ∈ sᶜ \ V.1, Finsupp.single i 1 with hg
  set v : (↥(s.powersetCard κ)) ⊕ (↥(sᶜ.powersetCard κ)) → MvPolynomial (Fin n) F :=
    fun x => monomial (Sum.elim f g x) 1 with hv
  -- membership of the inl block
  have hmem_inl : ∀ U : ↥(s.powersetCard κ), v (Sum.inl U) ∈ spdpSubspace κ 0 P := by
    intro U
    have hUs : U.1 ⊆ s := (Finset.mem_powersetCard.mp U.2).1
    have hUc : U.1.card = κ := (Finset.mem_powersetCard.mp U.2).2
    have hUne : U.1.Nonempty := Finset.card_pos.mp (by omega)
    apply Submodule.subset_span
    refine ⟨U.1.toList, 1, by rw [Finset.length_toList]; exact hUc, totalDegree_one.le, ?_⟩
    rw [one_mul, hv, hP, iterDerivList_add,
      iterDeriv_prodX U.1.toList s U.1.nodup_toList (fun i hi => hUs (Finset.mem_toList.mp hi)),
      Finset.toList_toFinset,
      iterDeriv_prodX_vanish U.1 sᶜ hUne (fun i hi h => (Finset.mem_compl.mp h) (hUs hi)),
      add_zero]
    simp only [Sum.elim_inl, hf]
    rw [← prodX_eq_monomial]
  have hmem_inr : ∀ V : ↥(sᶜ.powersetCard κ), v (Sum.inr V) ∈ spdpSubspace κ 0 P := by
    intro V
    have hVs : V.1 ⊆ sᶜ := (Finset.mem_powersetCard.mp V.2).1
    have hVc : V.1.card = κ := (Finset.mem_powersetCard.mp V.2).2
    have hVne : V.1.Nonempty := Finset.card_pos.mp (by omega)
    apply Submodule.subset_span
    refine ⟨V.1.toList, 1, by rw [Finset.length_toList]; exact hVc, totalDegree_one.le, ?_⟩
    rw [one_mul, hv, hP, iterDerivList_add,
      iterDeriv_prodX_vanish V.1 s hVne (fun i hi h => (Finset.mem_compl.mp (hVs hi)) h),
      iterDeriv_prodX V.1.toList sᶜ V.1.nodup_toList (fun i hi => hVs (Finset.mem_toList.mp hi)),
      Finset.toList_toFinset, zero_add]
    simp only [Sum.elim_inr, hg]
    rw [← prodX_eq_monomial]
  have hmem : ∀ x, v x ∈ spdpSubspace κ 0 P := fun x => x.rec hmem_inl hmem_inr
  -- injectivity of the exponent
  have hexpinj : Function.Injective (Sum.elim f g) := by
    rintro (U|V) (U'|V') h <;> simp only [Sum.elim_inl, Sum.elim_inr, hf, hg] at h
    · have he := indicator_inj h
      refine congrArg Sum.inl (Subtype.ext ?_)
      have hthis : s \ (s \ U.1) = s \ (s \ U'.1) := by rw [he]
      rwa [sdiff_sdiff_self_of_subset (Finset.mem_powersetCard.mp U.2).1,
        sdiff_sdiff_self_of_subset (Finset.mem_powersetCard.mp U'.2).1] at hthis
    · exfalso
      have he := indicator_inj h
      have hsub : s \ U.1 ⊆ s := Finset.sdiff_subset
      have hne : (s \ U.1).Nonempty := by
        rw [Finset.sdiff_nonempty]; exact fun hc => by
          have := Finset.card_le_card hc; rw [(Finset.mem_powersetCard.mp U.2).2] at this; omega
      obtain ⟨i, hi⟩ := hne
      have : i ∈ sᶜ \ V'.1 := he ▸ hi
      exact (Finset.mem_compl.mp (Finset.sdiff_subset this)) (Finset.sdiff_subset hi)
    · exfalso
      have he := (indicator_inj h).symm
      have hne : (s \ U'.1).Nonempty := by
        rw [Finset.sdiff_nonempty]; exact fun hc => by
          have := Finset.card_le_card hc; rw [(Finset.mem_powersetCard.mp U'.2).2] at this; omega
      obtain ⟨i, hi⟩ := hne
      have : i ∈ sᶜ \ V.1 := he ▸ hi
      exact (Finset.mem_compl.mp (Finset.sdiff_subset this)) (Finset.sdiff_subset hi)
    · have he := indicator_inj h
      refine congrArg Sum.inr (Subtype.ext ?_)
      have hthis : sᶜ \ (sᶜ \ V.1) = sᶜ \ (sᶜ \ V'.1) := by rw [he]
      rwa [sdiff_sdiff_self_of_subset (Finset.mem_powersetCard.mp V.2).1,
        sdiff_sdiff_self_of_subset (Finset.mem_powersetCard.mp V'.2).1] at hthis
  have hLI : LinearIndependent F v := by
    have heq : v = ⇑(basisMonomials (Fin n) F) ∘ (Sum.elim f g) := by
      funext x; simp [hv, Function.comp_apply, coe_basisMonomials]
    rw [heq]; exact (basisMonomials (Fin n) F).linearIndependent.comp _ hexpinj
  have hsub : Submodule.span F (Set.range v) ≤ spdpSubspace κ 0 P := by
    rw [Submodule.span_le]; rintro _ ⟨x, rfl⟩; exact hmem x
  have hfin : finrank F (Submodule.span F (Set.range v)) = s.card.choose κ + sᶜ.card.choose κ := by
    rw [finrank_span_eq_card hLI, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
      Finset.card_powersetCard, Finset.card_powersetCard]
  haveI : FiniteDimensional F (spdpSubspace κ 0 P) :=
    Submodule.finiteDimensional_of_le
      (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 P)
  calc s.card.choose κ + sᶜ.card.choose κ = _ := hfin.symm
    _ ≤ finrank F (spdpSubspace κ 0 P) := Submodule.finrank_mono hsub
    _ = spdpRank κ 0 P := rfl

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_twoBlock_ge
