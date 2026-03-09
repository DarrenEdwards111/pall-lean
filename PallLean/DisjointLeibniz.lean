/-
  DisjointLeibniz.lean — Disjoint-variable Leibniz factorization
-/
import PallLean.LeibnizProduct
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace DisjointLeibniz

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- General iterDerivList for any variable type σ -/
noncomputable def iterDeriv (indices : List σ) (p : MvPolynomial σ F) :
    MvPolynomial σ F :=
  indices.foldl (fun q i => pderiv i q) p

@[simp] theorem iterDeriv_nil (p : MvPolynomial σ F) : iterDeriv [] p = p := rfl

theorem iterDeriv_cons (x : σ) (S : List σ) (p : MvPolynomial σ F) :
    iterDeriv (x :: S) p = iterDeriv S (pderiv x p) := rfl

/-! ## vars(pderiv x f) ⊆ vars(f) -/

/-- vars(pderiv x f) ⊆ vars(f).
    Proof: pderiv x (monomial s a) = monomial (s - single x 1) (a * s x).
    By Finsupp.support_tsub, (s - single x 1).support ⊆ s.support.
    So vars of each monomial term are contained in vars of the original.
    The sum over monomials preserves this via vars_sum_subset. -/
theorem vars_pderiv_subset (x : σ) (f : MvPolynomial σ F) :
    (pderiv x f).vars ⊆ f.vars := by
  -- Write f = ∑_{s ∈ f.support} monomial s (coeff s f)
  -- pderiv x f = ∑_{s ∈ f.support} pderiv x (monomial s (coeff s f))
  --            = ∑_{s ∈ f.support} monomial (s - single x 1) (coeff s f * s x)
  -- vars of each term ⊆ (s - single x 1).support ⊆ s.support ⊆ f.vars
  -- vars of sum ⊆ ⋃ vars of terms ⊆ f.vars
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply (vars_sum_subset _ _).trans
  intro v hv
  simp only [Finset.mem_biUnion] at hv
  obtain ⟨s, hs_mem, hv_s⟩ := hv
  rw [pderiv_monomial] at hv_s
  by_cases ha : f.coeff s * ↑(s x) = 0
  · simp [ha] at hv_s
  · rw [vars_monomial ha] at hv_s
    -- v ∈ (s - single x 1).support ⊆ s.support
    have := Finsupp.support_tsub (f1 := s) (f2 := Finsupp.single x 1)
    have hv_s' := this hv_s
    -- v ∈ s.support and s ∈ f.support → v ∈ f.vars
    rw [mem_vars]
    exact ⟨s, Finsupp.mem_support_iff.mpr (by
      rwa [MvPolynomial.mem_support_iff] at hs_mem), hv_s'⟩

/-! ## pderiv of product with disjoint variables -/

theorem pderiv_mul_right (x : σ) (f g : MvPolynomial σ F) (hg : x ∉ g.vars) :
    pderiv x (f * g) = pderiv x f * g := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars hg, mul_zero, add_zero]

theorem pderiv_mul_left (x : σ) (f g : MvPolynomial σ F) (hf : x ∉ f.vars) :
    pderiv x (f * g) = f * pderiv x g := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars hf, zero_mul, zero_add]

/-! ## iterDeriv of two-factor product with disjoint variables -/

theorem iterDeriv_mul_disjoint
    (f g : MvPolynomial σ F) (P Q : σ → Prop) [DecidablePred P] [DecidablePred Q]
    (hf : ∀ v ∈ f.vars, P v)
    (hg : ∀ v ∈ g.vars, Q v)
    (hdisj : ∀ v, P v → ¬ Q v)
    (S : List σ) (hS : ∀ x ∈ S, P x ∨ Q x) :
    iterDeriv S (f * g) =
      iterDeriv (S.filter P) f * iterDeriv (S.filter Q) g := by
  induction S generalizing f g with
  | nil => simp [iterDeriv]
  | cons x S ih =>
    rw [iterDeriv_cons]
    have hx := hS x (by simp)
    have hS' : ∀ y ∈ S, P y ∨ Q y := fun y hy => hS y (by simp [hy])
    simp only [List.filter_cons]
    rcases hx with hP | hQ
    · -- x ∈ P: pderiv x hits f only
      have hxg : x ∉ g.vars := fun h => hdisj x hP (hg x h)
      have hnQ : ¬ Q x := hdisj x hP
      simp only [decide_eq_true_eq]
      rw [if_pos hP, if_neg hnQ]
      rw [pderiv_mul_right x f g hxg]
      rw [iterDeriv_cons]
      exact ih (pderiv x f) g (fun v hv => hf v (vars_pderiv_subset x f hv)) hg hS'
    · -- x ∈ Q: pderiv x hits g only
      have hxf : x ∉ f.vars := fun h => hdisj x (hf x h) hQ
      have hnP : ¬ P x := fun hp => hdisj x hp hQ
      simp only [decide_eq_true_eq]
      rw [if_neg hnP, if_pos hQ]
      rw [pderiv_mul_left x f g hxf]
      rw [iterDeriv_cons]
      exact ih f (pderiv x g) hf (fun v hv => hg v (vars_pderiv_subset x g hv)) hS'

end DisjointLeibniz
