import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineProdBound

/-!
# The observer-boundary SPDP invariant: MOD_q is boundary-robust, ∏Xᵢ is fragile (quantitative)

The N-Frame "observer boundary" picture, made quantitative.  An `ObserverBoundary` selects which variables stay
*visible* (free) and fixes the rest to Boolean values (the environment/context).  The boundary SPDP cost is the SPDP
rank of the polynomial restricted to that boundary — how much derivative-span structure survives on the visible slice.

  `spdpRank_affProd_subset_ge` — the visible-slice affine bound: `spdpRank κ 0 (∏_{i∈s}(1+cXᵢ)) ≥ C(|s|, κ)` (the
        `s`-generalisation of `spdpRank_affProd_choose_ge`, via the same affine-automorphism engine).
  `spdpRank_le_C_mul` — a nonzero constant factor does not change SPDP rank (restricting fixes factors to constants).
  `spdpRank_restrictBoundary_modqPoly_ge` — **`MOD_q` is boundary-robust**: for `c ≠ 0`, `1+c ≠ 0`,
        `spdpRank κ 0 (restrictBoundary B (∏ᵢ(1+cXᵢ))) ≥ (B.visible.card).choose κ`.  Restricting `MOD_q` outside the
        boundary leaves `(nonzero const)·∏_{visible}(1+cXᵢ)` (its affine factors evaluate to `1`/`ω`, never `0`), whose
        SPDP rank is `≥ C(m, κ)` on the `m = |visible|` variables.
  `fullProd_restrictBoundary_zero` — **`∏Xᵢ` is fragile**: any boundary fixing an outside variable to `0` kills it
        (`restrictBoundary B (∏Xᵢ) = 0`), so its boundary SPDP can drop to `0`.

So the observer-boundary invariant separates them quantitatively: `BoundarySPDP MOD_q m κ ≥ C(m,κ)` (structure survives
across every Boolean boundary) versus `BoundarySPDP ∏Xᵢ = 0` (killable) — where raw rank and `pcrank` could not.  This
is the N-Frame reading: hardness = the observer cannot select a context that trivialises the derivative structure.

## Honest scope

`MOD_q`'s polynomial is an *easy* function; this is a genuine proved invariant that distinguishes it from the easy
product, but it does not separate complexity classes.  Whether boundary-robust SPDP rank is low for *all* of `ACC⁰`
(so that a genuinely hard target's boundary robustness would separate) is the open barrier.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Finset Module

variable {n : ℕ} {F : Type*} [Field F]

/-- An **observer boundary**: `visible` variables stay free; the rest are fixed to Boolean values. -/
structure ObserverBoundary (n : ℕ) where
  visible : Finset (Fin n)
  fixed : Fin n → Bool

theorem spdpRank_affProd_subset_ge (s : Finset (Fin n)) (c : F) (hc : c ≠ 0) (κ : ℕ) :
    s.card.choose κ ≤ spdpRank κ 0 (∏ i ∈ s, (1 + C c * X i) : MvPolynomial (Fin n) F) := by
  classical
  set P : MvPolynomial (Fin n) F := ∏ i ∈ s, (1 + C c * X i) with hP_def
  have hPaff : P = aeval (aff c) (∏ i ∈ s, (X i : MvPolynomial (Fin n) F)) := by
    rw [hP_def, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by simp [aff])
  set v : ↥(s.powersetCard κ) → MvPolynomial (Fin n) F :=
    fun U => aeval (aff c) (∏ i ∈ s \ U.1, (X i : MvPolynomial (Fin n) F)) with hv
  have hmem : ∀ U, v U ∈ spdpSubspace κ 0 P := by
    intro U
    have hUs : U.1 ⊆ s := (Finset.mem_powersetCard.mp U.2).1
    have hUc : U.1.card = κ := (Finset.mem_powersetCard.mp U.2).2
    apply Submodule.subset_span
    refine ⟨U.1.toList, C ((c ^ κ)⁻¹), by rw [Finset.length_toList]; exact hUc,
      le_of_eq (totalDegree_C _), ?_⟩
    have hcomp : iterDerivList U.1.toList P = C (c ^ κ) * v U := by
      rw [hPaff, iterDerivList_aeval_aff, Finset.length_toList, hUc, hv,
        iterDeriv_prodX U.1.toList s U.1.nodup_toList (fun i hi => hUs (Finset.mem_toList.mp hi)),
        Finset.toList_toFinset]
    rw [hcomp, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero κ hc), map_one, one_mul]
  have hexpinj : Function.Injective
      (fun U : ↥(s.powersetCard κ) => ∑ i ∈ s \ U.1, Finsupp.single i (1 : ℕ)) := by
    intro U U' h
    apply Subtype.ext
    have hUs : U.1 ⊆ s := (Finset.mem_powersetCard.mp U.2).1
    have hU's : U'.1 ⊆ s := (Finset.mem_powersetCard.mp U'.2).1
    have hthis : s \ (s \ U.1) = s \ (s \ U'.1) := by rw [indicator_inj h]
    rwa [sdiff_sdiff_self_of_subset hUs, sdiff_sdiff_self_of_subset hU's] at hthis
  have hLI : LinearIndependent F v := by
    have hbase : LinearIndependent F
        (⇑(basisMonomials (Fin n) F) ∘ (fun U : ↥(s.powersetCard κ) => ∑ i ∈ s \ U.1, Finsupp.single i 1)) :=
      (basisMonomials (Fin n) F).linearIndependent.comp _ hexpinj
    have heq : v = (aeval (aff c)).toLinearMap ∘
        (⇑(basisMonomials (Fin n) F) ∘ (fun U : ↥(s.powersetCard κ) => ∑ i ∈ s \ U.1, Finsupp.single i 1)) := by
      funext U
      simp only [Function.comp_apply, coe_basisMonomials, hv, AlgHom.toLinearMap_apply]
      rw [← prodX_eq_monomial]
    rw [heq]
    exact hbase.map' (aeval (aff c)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (aeval_aff_injective c hc))
  have hsub : Submodule.span F (Set.range v) ≤ spdpSubspace κ 0 P := by
    rw [Submodule.span_le]; rintro _ ⟨U, rfl⟩; exact hmem U
  have hfin : finrank F (Submodule.span F (Set.range v)) = s.card.choose κ := by
    rw [finrank_span_eq_card hLI, Fintype.card_coe, Finset.card_powersetCard]
  haveI : FiniteDimensional F (spdpSubspace κ 0 P) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 P)
  calc s.card.choose κ = _ := hfin.symm
    _ ≤ finrank F (spdpSubspace κ 0 P) := Submodule.finrank_mono hsub
    _ = spdpRank κ 0 P := rfl

theorem spdpSubspace_le_C_mul (a : F) (ha : a ≠ 0) (κ ℓ : ℕ) (q : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ q ≤ spdpSubspace κ ℓ (C a * q) := by
  rw [spdpSubspace, Submodule.span_le]
  rintro _ ⟨S, m, hSlen, hmdeg, rfl⟩
  rw [SetLike.mem_coe]
  have hrw : m * iterDerivList S q = (m * C a⁻¹) * iterDerivList S (C a * q) := by
    rw [iterDerivList_C_mul, ← mul_assoc, mul_assoc m, ← C_mul, inv_mul_cancel₀ ha, C_1, mul_one]
  rw [hrw]
  exact Submodule.subset_span ⟨S, m * C a⁻¹, hSlen,
    le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, add_zero]; exact hmdeg), rfl⟩

theorem spdpRank_le_C_mul (a : F) (ha : a ≠ 0) (κ : ℕ) (q : MvPolynomial (Fin n) F) :
    spdpRank κ 0 q ≤ spdpRank κ 0 (C a * q) := by
  haveI : FiniteDimensional F (spdpSubspace κ 0 (C a * q)) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 (C a * q))
  exact Submodule.finrank_mono (spdpSubspace_le_C_mul a ha κ 0 q)

noncomputable def restrictBoundary (s : Finset (Fin n)) (assign : Fin n → Bool)
    (p : MvPolynomial (Fin n) F) : MvPolynomial (Fin n) F :=
  aeval (fun i => if i ∈ s then X i else C (if assign i then (1 : F) else 0)) p

theorem restrictBoundary_modqPoly_eq (s : Finset (Fin n)) (assign : Fin n → Bool) (c : F) :
    restrictBoundary s assign (∏ i, (1 + C c * X i))
      = C (∏ i ∈ sᶜ, (1 + c * (if assign i then (1 : F) else 0))) * ∏ i ∈ s, (1 + C c * X i) := by
  unfold restrictBoundary
  rw [map_prod, ← Finset.prod_mul_prod_compl s, mul_comm]
  congr 1
  · rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [map_add, map_mul, map_one, aeval_C, MvPolynomial.algebraMap_eq, aeval_X,
      if_neg (Finset.mem_compl.mp hi), C_add, C_1, C_mul]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [map_add, map_mul, map_one, aeval_C, MvPolynomial.algebraMap_eq, aeval_X, if_pos hi]

theorem spdpRank_restrictBoundary_modqPoly_ge (s : Finset (Fin n)) (assign : Fin n → Bool)
    (c : F) (hc : c ≠ 0) (hc1 : (1 : F) + c ≠ 0) (κ : ℕ) :
    s.card.choose κ ≤ spdpRank κ 0 (restrictBoundary s assign (∏ i, (1 + C c * X i))) := by
  rw [restrictBoundary_modqPoly_eq]
  have hscalar : (∏ i ∈ sᶜ, (1 + c * (if assign i then (1 : F) else 0))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    cases assign i <;> simp [hc1]
  exact le_trans (spdpRank_affProd_subset_ge s c hc κ) (spdpRank_le_C_mul _ hscalar κ _)

/-- `∏Xᵢ` is fragile: a boundary fixing an outside variable to `0` kills it. -/
theorem fullProd_restrictBoundary_zero (s : Finset (Fin n)) (assign : Fin n → Bool) (j : Fin n)
    (hj : j ∉ s) (hassign : assign j = false) :
    restrictBoundary s assign (∏ i, (X i : MvPolynomial (Fin n) F)) = 0 := by
  unfold restrictBoundary
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, hassign]

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_restrictBoundary_modqPoly_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.fullProd_restrictBoundary_zero
