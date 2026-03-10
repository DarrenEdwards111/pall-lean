/-
  LocalBasis.lean — Per-block local derivative spanning set

  Proves that all iterated derivatives of f lie in span of a finite set
  determined by f's support (downward closure under componentwise ≤).
-/
import PallLean.SPDPDefs
import PallLean.DisjointLeibniz
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Finsupp.Interval

namespace LocalBasis

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-! ## Downward closure spanning set -/

/-- The downward closure monomial basis: {monomial t 1 | t ≤ some s ∈ f.support}. -/
noncomputable def downClosureBasis (f : MvPolynomial σ F) : Set (MvPolynomial σ F) :=
  { q | ∃ (t : σ →₀ ℕ), (∃ s ∈ f.support, t ≤ s) ∧ q = monomial t (1 : F) }

/-- f itself lies in span of its downClosureBasis. -/
theorem self_mem_span_downClosure (f : MvPolynomial σ F) :
    f ∈ Submodule.span F (downClosureBasis f) := by
  classical
  have key : ∀ s ∈ f.support, monomial s (coeff s f) ∈
      Submodule.span F (downClosureBasis f) := by
    intro s hs
    have hmem : monomial s (1 : F) ∈ downClosureBasis f :=
      ⟨s, ⟨s, hs, le_refl s⟩, rfl⟩
    have heq : monomial s (coeff s f) = coeff s f • monomial s (1 : F) := by
      simp [smul_monomial]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hsum := Submodule.sum_mem _ key
  rwa [← f.as_sum] at hsum

/-- Support of pderiv x f ⊆ {s - single x 1 | s ∈ f.support}. -/
theorem support_pderiv_subset (x : σ) (f : MvPolynomial σ F) :
    (pderiv x f).support ⊆ f.support.image (fun s => s - Finsupp.single x 1) := by
  classical
  intro t ht
  simp only [Finset.mem_image]
  by_contra h
  push_neg at h
  have : pderiv x f = ∑ s ∈ f.support, pderiv x (monomial s (coeff s f)) := by
    conv_lhs => rw [f.as_sum]; rw [map_sum]
  have hzero : ∀ s ∈ f.support, coeff t (pderiv x (monomial s (coeff s f))) = 0 := by
    intro s hs
    rw [pderiv_monomial, coeff_monomial]
    exact if_neg (fun heq => h s hs heq)
  have hcoeff : coeff t (pderiv x f) = 0 := by
    conv_lhs => rw [this]
    rw [show coeff t (∑ s ∈ f.support, pderiv x (monomial s (coeff s f))) =
      ∑ s ∈ f.support, coeff t (pderiv x (monomial s (coeff s f))) from
      Finsupp.finset_sum_apply _ _ _]
    exact Finset.sum_eq_zero hzero
  exact (Finsupp.mem_support_iff.mp ht) hcoeff

/-- Downward closure is closed under pderiv. -/
theorem downClosure_pderiv_subset (x : σ) (f : MvPolynomial σ F) :
    downClosureBasis (pderiv x f) ⊆ downClosureBasis f := by
  intro q hq
  obtain ⟨t, ⟨s, hs, hts⟩, rfl⟩ := hq
  have hsub : s ∈ f.support.image (fun s => s - Finsupp.single x 1) :=
    support_pderiv_subset x f hs
  simp only [Finset.mem_image] at hsub
  obtain ⟨s', hs', rfl⟩ := hsub
  exact ⟨t, ⟨s', hs', le_trans hts tsub_le_self⟩, rfl⟩

/-- Key theorem: pderiv x f lies in span of downClosureBasis f. -/
theorem pderiv_mem_span_downClosure (x : σ) (f : MvPolynomial σ F) :
    pderiv x f ∈ Submodule.span F (downClosureBasis f) := by
  -- pderiv x f lies in span of downClosureBasis(pderiv x f) by self_mem_span_downClosure
  -- and downClosureBasis(pderiv x f) ⊆ downClosureBasis(f)
  exact Submodule.span_mono (downClosure_pderiv_subset x f)
    (self_mem_span_downClosure (pderiv x f))

/-- iterDerivList S f lies in span of downClosureBasis f. -/
theorem iterDerivList_mem_span_downClosure {n : ℕ}
    (S : List (Fin n)) (f : MvPolynomial (Fin n) F) :
    SPDP.iterDerivList S f ∈ Submodule.span F (downClosureBasis f) := by
  induction S generalizing f with
  | nil =>
    simp only [SPDP.iterDerivList, List.foldl_nil]
    exact self_mem_span_downClosure f
  | cons x S ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons]
    exact Submodule.span_mono (downClosure_pderiv_subset x f)
      (ih (pderiv x f))

/-! ## Finite spanning set with bounded cardinality -/

/-- The finite downward closure: all exponents componentwise ≤ some s ∈ f.support,
    realized as a Finset via Finsupp.Iic. -/
noncomputable def finiteDownClosure [Fintype σ] (f : MvPolynomial σ F) : Finset (σ →₀ ℕ) :=
  f.support.biUnion (fun s => Finset.Iic s)

theorem mem_finiteDownClosure_iff [Fintype σ] (f : MvPolynomial σ F) (t : σ →₀ ℕ) :
    t ∈ finiteDownClosure f ↔ ∃ s ∈ f.support, t ≤ s := by
  simp [finiteDownClosure, Finset.mem_biUnion, Finset.mem_Iic]

/-- The monomial Finset spanning all derivatives. -/
noncomputable def monomialSpanFinset [Fintype σ] [DecidableEq F] (f : MvPolynomial σ F) : Finset (MvPolynomial σ F) :=
  (finiteDownClosure f).image (fun t => monomial t (1 : F))

/-- downClosureBasis f ⊆ ↑(monomialSpanFinset f) -/
theorem downClosureBasis_subset_monomialSpan [Fintype σ] [DecidableEq F] (f : MvPolynomial σ F) :
    downClosureBasis f ⊆ ↑(monomialSpanFinset f) := by
  intro q hq
  obtain ⟨t, ⟨s, hs, hts⟩, rfl⟩ := hq
  simp only [monomialSpanFinset, Finset.coe_image, Set.mem_image]
  exact ⟨t, (mem_finiteDownClosure_iff f t).mpr ⟨s, hs, hts⟩, rfl⟩

/-- Cardinality bound: monomialSpanFinset has card ≤ |finiteDownClosure|,
    which for multilinear polynomials (degree ≤ 1 per var) with d vars
    is ≤ 2^d. General bound: ∏_{i ∈ vars} (degree_i + 1). -/
theorem monomialSpanFinset_card_le [Fintype σ] [DecidableEq F]
    (f : MvPolynomial σ F) :
    (monomialSpanFinset f).card ≤ (finiteDownClosure f).card := by
  exact Finset.card_image_le

theorem iterDerivList_mem_span_monomialFinset {n : ℕ} [DecidableEq F]
    (S : List (Fin n)) (f : MvPolynomial (Fin n) F) :
    SPDP.iterDerivList S f ∈
      Submodule.span F ↑(monomialSpanFinset f) :=
  Submodule.span_mono (downClosureBasis_subset_monomialSpan f)
    (iterDerivList_mem_span_downClosure S f)

end LocalBasis

