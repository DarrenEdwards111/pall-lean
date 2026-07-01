import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffinePderiv
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPDeterminantLike

/-!
# The affine-product SPDP lower bound: `spdpRank κ 0 (∏ᵢ(1+cXᵢ)) ≥ C(n,κ)`

The payoff of the affine-automorphism engine (`…AffinePderiv`).  `MOD_q`'s multilinear polynomial is the affine
product `∏ᵢ(1+(ω-1)Xᵢ)`; this proves it has *exponential* order-`κ` SPDP rank (`≈ 2ⁿ/√n` at `κ = n/2`), just like the
plain product `∏Xᵢ` — so raw rank alone cannot tell `MOD_q` from an easy product (which is exactly why the
*restriction*-based invariant is the right refinement, `…SPDPRestricted`).

  `spdpRank_affProd_choose_ge` — `n.choose κ ≤ spdpRank κ 0 (∏ᵢ(1 + C c · Xᵢ))` for `c ≠ 0`.

Proof: the affine automorphism `φ = aeval (Xᵢ ↦ 1+cXᵢ)` sends the complement monomials `∏_{i∈Sᶜ} Xᵢ` to the affine
products `∏_{i∈Sᶜ}(1+cXᵢ)`; these are the order-`κ` derivatives up to the unit scalar `C(c^κ)`
(`iterDerivList_aeval_aff` + `iterDeriv_prodX`), hence lie in the SPDP subspace, and they are linearly independent
because `φ` is injective (`aeval_aff_injective`) and the monomials are (`basisMonomials`).  `C(n,κ)` independent
elements ⇒ rank `≥ C(n,κ)`.

## Honest scope

A genuine, proved exponential SPDP-rank lower bound for `MOD_q`'s (easy) polynomial.  Composed with `…SPDPRestricted`
(`restrictPoly (modqPoly c) = (unit)·∏_{visible}(1+cXᵢ)`), the subset version of this bound gives the quantitative
observer-boundary robustness `BoundarySPDP MOD_q m κ ≥ C(m,κ)` (the visible-slice version — `s`-generalisation of this
proof).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Finset Module

variable {n : ℕ} {F : Type*} [Field F]

theorem spdpRank_affProd_choose_ge (c : F) (hc : c ≠ 0) (κ : ℕ) :
    n.choose κ ≤ spdpRank κ 0 (∏ i, (1 + C c * X i) : MvPolynomial (Fin n) F) := by
  classical
  set P : MvPolynomial (Fin n) F := ∏ i, (1 + C c * X i) with hP_def
  have hPaff : P = aeval (aff c) (∏ i, X i : MvPolynomial (Fin n) F) := by
    rw [hP_def, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by simp [aff])
  set v : {S : Finset (Fin n) // S.card = κ} → MvPolynomial (Fin n) F :=
    fun S => aeval (aff c) (∏ i ∈ S.1ᶜ, (X i : MvPolynomial (Fin n) F)) with hv
  have hmem : ∀ S, v S ∈ spdpSubspace κ 0 P := by
    intro S
    apply Submodule.subset_span
    refine ⟨S.1.toList, C ((c ^ κ)⁻¹), by rw [Finset.length_toList]; exact S.2,
      le_of_eq (totalDegree_C _), ?_⟩
    have hcomp : iterDerivList S.1.toList P = C (c ^ κ) * v S := by
      rw [hPaff, iterDerivList_aeval_aff, Finset.length_toList, S.2, hv]
      congr 2
      rw [show (∏ i, X i : MvPolynomial (Fin n) F) = ∏ i ∈ Finset.univ, X i from rfl,
        iterDeriv_prodX S.1.toList Finset.univ S.1.nodup_toList (fun i _ => Finset.mem_univ i),
        Finset.toList_toFinset, ← Finset.compl_eq_univ_sdiff]
    rw [hcomp, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero κ hc), map_one, one_mul]
  have hexpinj : Function.Injective
      (fun S : {S : Finset (Fin n) // S.card = κ} => ∑ i ∈ S.1ᶜ, Finsupp.single i (1 : ℕ)) :=
    fun S S' h => Subtype.ext (compl_injective (indicator_inj h))
  have hLI : LinearIndependent F v := by
    have hbase : LinearIndependent F
        (⇑(basisMonomials (Fin n) F) ∘ (fun S : {S : Finset (Fin n) // S.card = κ} => ∑ i ∈ S.1ᶜ, Finsupp.single i 1)) :=
      (basisMonomials (Fin n) F).linearIndependent.comp _ hexpinj
    have heq : v = (aeval (aff c)).toLinearMap ∘
        (⇑(basisMonomials (Fin n) F) ∘ (fun S : {S : Finset (Fin n) // S.card = κ} => ∑ i ∈ S.1ᶜ, Finsupp.single i 1)) := by
      funext S
      simp only [Function.comp_apply, coe_basisMonomials, hv, AlgHom.toLinearMap_apply]
      rw [← prodX_eq_monomial]
    rw [heq]
    exact hbase.map' (aeval (aff c)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (aeval_aff_injective c hc))
  have hsub : Submodule.span F (Set.range v) ≤ spdpSubspace κ 0 P := by
    rw [Submodule.span_le]; rintro _ ⟨S, rfl⟩; exact hmem S
  have hfin : finrank F (Submodule.span F (Set.range v)) = n.choose κ := by
    rw [finrank_span_eq_card hLI, Fintype.card_finset_len]
    simp
  haveI : FiniteDimensional F (spdpSubspace κ 0 P) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 P)
  calc n.choose κ = _ := hfin.symm
    _ ≤ finrank F (spdpSubspace κ 0 P) := Submodule.finrank_mono hsub
    _ = spdpRank κ 0 P := rfl


end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_affProd_choose_ge
