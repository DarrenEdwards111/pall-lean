import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSPDPBridge

/-!
# A concrete SPDP-rank lower bound: `spdpRank 1 0 (∏ Xᵢ) ≥ n`

A genuine (proved, no socket) lower bound on the literal `SPDP.spdpRank` for a concrete family — the **full product**
`fullProd = ∏ᵢ Xᵢ`.  Its `n` first-order partial derivatives `∂ₖ(∏ᵢ Xᵢ) = ∏_{i≠k} Xᵢ` are `n` distinct
degree-`(n-1)` monomials, hence linearly independent, so the order-`(κ=1)` SPDP subspace has dimension `≥ n`:

  `spdpRank_fullProd_ge` — `n ≤ spdpRank 1 0 (∏ᵢ Xᵢ)`.

## Honest scope

This is a **real** SPDP-rank lower bound for a **concrete** family, but the full product is an *easy* polynomial, so
this does **not** separate complexity classes — it is not the barriered `A3` hard-survival bound (a super-polynomial
SPDP rank lower bound for an *explicit hard* family, which would give a `VP`-vs-`VNP`-flavoured separation and is open
/ barriered short of `P/poly`).  It is the honest, reachable kind of SPDP-rank lower bound: a concrete computation,
proved clean.  The general bound `spdpRank κ 0 (∏ Xᵢ) ≥ C(n, κ)` (`spdpRank_fullProd_choose_ge`, **exponential**
`≈ 2ⁿ/√n` at `κ = n/2`) is also proved here, via the iterated derivative `iterDeriv_prodX`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Finset Module

variable {n : ℕ} {F : Type*} [Field F]

/-- `∏_{i∈s} Xᵢ` is the monomial of the indicator multidegree of `s`. -/
theorem prodX_eq_monomial (s : Finset (Fin n)) :
    (∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) = monomial (∑ i ∈ s, Finsupp.single i 1) 1 := by
  rw [monomial_sum_one]
  exact Finset.prod_congr rfl (fun i _ => by rw [← X_pow_eq_monomial, pow_one])

/-- **Differentiating the product removes one factor (proved).**  `∂ₖ(∏_{i∈s} Xᵢ) = ∏_{i∈s.erase k} Xᵢ` for `k ∈ s`. -/
theorem pderiv_prodX (s : Finset (Fin n)) (k : Fin n) (hk : k ∈ s) :
    pderiv k (∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) = ∏ i ∈ s.erase k, X i := by
  rw [prodX_eq_monomial s, pderiv_monomial, prodX_eq_monomial (s.erase k), monomial_eq_monomial_iff]
  left
  refine ⟨?_, ?_⟩
  · rw [← Finset.add_sum_erase s _ hk, add_tsub_cancel_left]
  · rw [Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hk]

/-- **Iterated differentiation removes the differentiated factors (proved).**  For a nodup list `L ⊆ s`,
`∂_L(∏_{i∈s} Xᵢ) = ∏_{i∈s∖L} Xᵢ`. -/
theorem iterDeriv_prodX : ∀ (L : List (Fin n)) (s : Finset (Fin n)), L.Nodup → (∀ i ∈ L, i ∈ s) →
    iterDerivList L (∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) = ∏ i ∈ s \ L.toFinset, X i
  | [], s, _, _ => by rw [List.toFinset_nil, Finset.sdiff_empty]; rfl
  | k :: L', s, hnd, hsub => by
      have hk : k ∈ s := hsub k (by simp)
      have hkL : k ∉ L' := (List.nodup_cons.mp hnd).1
      have hndL : L'.Nodup := (List.nodup_cons.mp hnd).2
      have hsubL : ∀ i ∈ L', i ∈ s.erase k := by
        intro i hi
        exact mem_erase.mpr ⟨fun h => hkL (h ▸ hi), hsub i (by simp [hi])⟩
      have hstep : iterDerivList (k :: L') (∏ i ∈ s, (X i : MvPolynomial (Fin n) F))
          = iterDerivList L' (pderiv k (∏ i ∈ s, X i)) := rfl
      rw [hstep, pderiv_prodX s k hk, iterDeriv_prodX L' (s.erase k) hndL hsubL]
      congr 1
      ext i
      simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto

/-- The full product `∏ᵢ Xᵢ`. -/
noncomputable def fullProd : MvPolynomial (Fin n) F := ∏ i, X i

/-- **Concrete SPDP-rank lower bound (proved).**  `spdpRank 1 0 (∏ᵢ Xᵢ) ≥ n`: the `n` first-order derivatives are
linearly independent. -/
theorem spdpRank_fullProd_ge : n ≤ spdpRank 1 0 (fullProd : MvPolynomial (Fin n) F) := by
  classical
  -- each first-order derivative monomial lies in the order-1 SPDP subspace
  have hmem : ∀ k, monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) (1 : F)
      ∈ spdpSubspace 1 0 (fullProd : MvPolynomial (Fin n) F) := by
    intro k
    apply Submodule.subset_span
    refine ⟨[k], 1, rfl, totalDegree_one.le, ?_⟩
    rw [one_mul]
    show monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) 1 = pderiv k (∏ i, X i)
    rw [pderiv_prodX univ k (mem_univ k), ← prodX_eq_monomial]
  -- the derivative monomials are indexed by an injective exponent map
  have hinj : Function.Injective (fun k : Fin n => ∑ i ∈ univ.erase k, Finsupp.single i (1 : ℕ)) := by
    intro k k' h
    by_contra hne
    have hk_mem : k ∈ univ.erase k' := mem_erase.mpr ⟨hne, mem_univ k⟩
    have hkk := DFunLike.congr_fun h k
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', hk_mem] at hkk
  -- hence they are linearly independent (distinct monomials)
  have hLI : LinearIndependent F
      (fun k : Fin n => monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) (1 : F)) := by
    have heq : (fun k : Fin n => monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) (1 : F))
        = ⇑(basisMonomials (Fin n) F) ∘ (fun k => ∑ i ∈ univ.erase k, Finsupp.single i 1) := by
      funext k
      simp [Function.comp_apply, coe_basisMonomials]
    rw [heq]
    exact (basisMonomials (Fin n) F).linearIndependent.comp _ hinj
  -- assemble: n linearly independent elements inside the (finite-dimensional) SPDP subspace
  have hsub : Submodule.span F
      (Set.range (fun k : Fin n => monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) (1 : F)))
        ≤ spdpSubspace 1 0 (fullProd : MvPolynomial (Fin n) F) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hmem k
  have hfin : finrank F (Submodule.span F
      (Set.range (fun k : Fin n => monomial (∑ i ∈ univ.erase k, Finsupp.single i 1) (1 : F)))) = n := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  haveI : FiniteDimensional F (spdpSubspace 1 0 (fullProd : MvPolynomial (Fin n) F)) :=
    Submodule.finiteDimensional_of_le
      (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree 1 0 fullProd)
  calc n = _ := hfin.symm
    _ ≤ finrank F (spdpSubspace 1 0 (fullProd : MvPolynomial (Fin n) F)) := Submodule.finrank_mono hsub
    _ = spdpRank 1 0 (fullProd : MvPolynomial (Fin n) F) := rfl

/-- **Exponential concrete SPDP-rank lower bound (proved).**  `spdpRank κ 0 (∏ᵢ Xᵢ) ≥ C(n, κ)`: differentiating the
full product by each of the `C(n,κ)` `κ`-subsets gives the `C(n,κ)` distinct complement monomials `∏_{i∉S} Xᵢ`, which
are linearly independent.  Exponential (`≈ 2ⁿ/√n`) at `κ = n/2`. -/
theorem spdpRank_fullProd_choose_ge (κ : ℕ) :
    n.choose κ ≤ spdpRank κ 0 (fullProd : MvPolynomial (Fin n) F) := by
  classical
  set v : {S : Finset (Fin n) // S.card = κ} → MvPolynomial (Fin n) F :=
    fun S => monomial (∑ i ∈ S.1ᶜ, Finsupp.single i 1) 1 with hv
  -- each complement monomial is the order-κ derivative by the subset, hence in the SPDP subspace
  have hmem : ∀ S, v S ∈ spdpSubspace κ 0 (fullProd : MvPolynomial (Fin n) F) := by
    intro S
    apply Submodule.subset_span
    refine ⟨S.1.toList, 1, ?_, totalDegree_one.le, ?_⟩
    · rw [Finset.length_toList]; exact S.2
    · rw [one_mul, hv]
      show monomial (∑ i ∈ S.1ᶜ, Finsupp.single i 1) 1 = iterDerivList S.1.toList (∏ i, X i)
      rw [iterDeriv_prodX S.1.toList univ S.1.nodup_toList (fun i _ => mem_univ i),
        Finset.toList_toFinset, ← Finset.compl_eq_univ_sdiff, ← prodX_eq_monomial]
  -- the complement-exponent map is injective ⇒ the monomials are linearly independent
  have hinj : Function.Injective
      (fun S : {S : Finset (Fin n) // S.card = κ} => ∑ i ∈ S.1ᶜ, Finsupp.single i (1 : ℕ)) := by
    intro S S' h
    apply Subtype.ext
    apply compl_injective
    ext j
    have hj := DFunLike.congr_fun h j
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at hj
    by_cases h1 : j ∈ S.1ᶜ <;> by_cases h2 : j ∈ S'.1ᶜ <;> simp_all
  have hLI : LinearIndependent F v := by
    have heq : v = ⇑(basisMonomials (Fin n) F) ∘
        (fun S : {S : Finset (Fin n) // S.card = κ} => ∑ i ∈ S.1ᶜ, Finsupp.single i 1) := by
      funext S
      simp [hv, Function.comp_apply, coe_basisMonomials]
    rw [heq]
    exact (basisMonomials (Fin n) F).linearIndependent.comp _ hinj
  have hsub : Submodule.span F (Set.range v) ≤ spdpSubspace κ 0 (fullProd : MvPolynomial (Fin n) F) := by
    rw [Submodule.span_le]
    rintro _ ⟨S, rfl⟩
    exact hmem S
  have hfin : finrank F (Submodule.span F (Set.range v)) = n.choose κ := by
    rw [finrank_span_eq_card hLI, Fintype.card_finset_len]
    simp
  haveI : FiniteDimensional F (spdpSubspace κ 0 (fullProd : MvPolynomial (Fin n) F)) :=
    Submodule.finiteDimensional_of_le
      (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 fullProd)
  calc n.choose κ = _ := hfin.symm
    _ ≤ finrank F (spdpSubspace κ 0 (fullProd : MvPolynomial (Fin n) F)) := Submodule.finrank_mono hsub
    _ = spdpRank κ 0 (fullProd : MvPolynomial (Fin n) F) := rfl

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_fullProd_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_fullProd_choose_ge
