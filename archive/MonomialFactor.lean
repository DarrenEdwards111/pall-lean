/-
  MonomialFactor.lean — Monomials factor per block partition

  Key lemma: x^α = ∏_c x^{α|_c} where α|_c restricts α to block c's variables.
  This allows absorbing the shift monomial m_poly into per-block local spaces.
-/
import PallLean.SPDPDefs
import PallLean.SpanProduct
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Basic

namespace MonomialFactor

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [CommRing F]

/-- Restrict a finsupp to variables in a specific block. -/
noncomputable def restrictToBlock (B : BlockPartition n) (c : Fin B.numBlocks)
    (α : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  α.filter (fun i => B.assign i = c)

/-- The restrictions partition α: ∑_c α|_c = α -/
theorem sum_restrictToBlock (B : BlockPartition n) (α : Fin n →₀ ℕ) :
    Finset.univ.sum (fun c => restrictToBlock B c α) = α := by
  classical
  ext i
  simp only [Finsupp.finset_sum_apply, restrictToBlock, Finsupp.filter_apply]
  rw [Finset.sum_eq_single (B.assign i)]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Monomial factors per block: monomial α 1 = ∏_c monomial (α|_c) 1 -/
theorem monomial_prod_restrictToBlock (B : BlockPartition n) (α : Fin n →₀ ℕ) :
    (monomial α (1 : F)) = Finset.univ.prod (fun c =>
      monomial (restrictToBlock B c α) (1 : F)) := by
  conv_lhs => rw [← sum_restrictToBlock B α]
  exact monomial_sum_one (σ := Fin n) (R := F) Finset.univ (fun c => restrictToBlock B c α)

attribute [local instance] Classical.dec

/-- For a product ∏ t_c where t_c ∈ span(W_c), and a monomial shift x^α,
    the product x^α * ∏ t_c = ∏ (x^{α|_c} * t_c) lies in the span of
    the product of shifted bases. -/
theorem monomial_mul_prod_eq {B : BlockPartition n}
    (t : Fin B.numBlocks → MvPolynomial (Fin n) F)
    (α : Fin n →₀ ℕ) :
    monomial α (1 : F) * Finset.univ.prod t =
    Finset.univ.prod (fun c => monomial (restrictToBlock B c α) (1 : F) * t c) := by
  rw [monomial_prod_restrictToBlock B α, Finset.prod_mul_distrib]

/-- Key: x^β * w ∈ span({x^β * w' | w' ∈ W}) when w ∈ span(W). -/
theorem monomial_smul_mem_span (β : Fin n →₀ ℕ) (W : Set (MvPolynomial (Fin n) F))
    (w : MvPolynomial (Fin n) F) (hw : w ∈ Submodule.span F W) :
    monomial β (1 : F) * w ∈
      Submodule.span F { monomial β 1 * w' | w' ∈ W } := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ihx

/-- Combined per-block basis: all monomial shifts of W elements. -/
noncomputable def shiftedBasis (W : Finset (MvPolynomial (Fin n) F))
    (shifts : Finset (Fin n →₀ ℕ)) : Finset (MvPolynomial (Fin n) F) :=
  shifts.product W |>.image (fun ⟨β, w⟩ => monomial β (1 : F) * w)

/-- m_poly * ∏ t_c ∈ span of product of shifted bases.
    m_poly = ∑ a_α x^α, and x^α * ∏ t_c = ∏ (x^{α|_c} * t_c).
    Each factor x^{α|_c} * t_c ∈ span(shiftedBasis W_c shifts_c).
    Product of span elements ∈ span(finsetProd of shifted bases). -/
theorem mpoly_mul_prod_mem_span {B : BlockPartition n}
    (t : Fin B.numBlocks → MvPolynomial (Fin n) F)
    (m_poly : MvPolynomial (Fin n) F)
    (W : Fin B.numBlocks → Finset (MvPolynomial (Fin n) F))
    (ht : ∀ c, t c ∈ Submodule.span F (W c : Set (MvPolynomial (Fin n) F))) :
    m_poly * Finset.univ.prod t ∈
      Submodule.span F ↑(SpanProduct.finsetProd B.numBlocks
        (fun c => shiftedBasis (W c) (m_poly.support.image (fun α => restrictToBlock B c α)))) := by
  -- Decompose m_poly = ∑ a_α · monomial α 1
  have hexp : m_poly * Finset.univ.prod t =
      (∑ α ∈ m_poly.support, monomial α (coeff α m_poly)) * Finset.univ.prod t := by
    conv_lhs => rw [m_poly.as_sum]
  rw [hexp, Finset.sum_mul]
  apply Submodule.sum_mem
  intro α hα
  -- monomial α (coeff α m_poly) = (coeff α m_poly) • monomial α 1
  rw [show monomial α (coeff α m_poly) = (coeff α m_poly) • monomial α (1 : F) from by
    simp [smul_monomial, mul_one]]
  rw [smul_mul_assoc]
  apply Submodule.smul_mem
  -- monomial α 1 * ∏ t_c = ∏ (monomial (α|_c) 1 * t_c)
  rw [monomial_mul_prod_eq t α]
  -- Each factor: monomial (α|_c) 1 * t_c ∈ span(shiftedBasis W_c shifts_c)
  apply SpanProduct.prod_mem_span_finsetProd
  intro c
  -- monomial (restrictToBlock B c α) 1 * t_c ∈ span(shiftedBasis ...)
  -- t_c ∈ span(W_c), so by monomial_smul_mem_span, the product ∈ span({mono * w | w ∈ W_c})
  -- and that ⊆ span(shiftedBasis W_c shifts_c)
  apply Submodule.span_mono _ (monomial_smul_mem_span (restrictToBlock B c α) _ _ (ht c))
  intro q hq
  obtain ⟨w, hw, rfl⟩ := hq
  simp only [shiftedBasis, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
  exact ⟨(restrictToBlock B c α, w),
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨α, hα, rfl⟩, hw⟩, rfl⟩

end MonomialFactor
