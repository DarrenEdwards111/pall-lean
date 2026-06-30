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
proved clean.  The same method (differentiate by a `κ`-subset, get the complement monomial) gives
`spdpRank κ 0 (∏ Xᵢ) ≥ C(n, κ)` (exponential at `κ = n/2`) via the iterated derivative — the natural generalization.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
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

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_fullProd_ge
