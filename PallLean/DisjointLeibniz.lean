/-
  DisjointLeibniz.lean — Disjoint-variable Leibniz factorization
-/
import PallLean.LeibnizProduct
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables

namespace DisjointLeibniz

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

noncomputable def iterDeriv (indices : List σ) (p : MvPolynomial σ F) :
    MvPolynomial σ F :=
  indices.foldl (fun q i => pderiv i q) p

@[simp] theorem iterDeriv_nil (p : MvPolynomial σ F) : iterDeriv [] p = p := rfl
theorem iterDeriv_cons (x : σ) (S : List σ) (p : MvPolynomial σ F) :
    iterDeriv (x :: S) p = iterDeriv S (pderiv x p) := rfl

/-! ## vars(pderiv x f) ⊆ vars(f) — PROVED -/

theorem vars_pderiv_subset (x : σ) (f : MvPolynomial σ F) :
    (pderiv x f).vars ⊆ f.vars := by
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
    have := Finsupp.support_tsub (f1 := s) (f2 := Finsupp.single x 1)
    rw [mem_vars]
    exact ⟨s, Finsupp.mem_support_iff.mpr (by rwa [mem_support_iff] at hs_mem), this hv_s⟩

/-! ## 2-factor disjoint Leibniz — PROVED -/

theorem pderiv_mul_right (x : σ) (f g : MvPolynomial σ F) (hg : x ∉ g.vars) :
    pderiv x (f * g) = pderiv x f * g := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars hg, mul_zero, add_zero]

theorem pderiv_mul_left (x : σ) (f g : MvPolynomial σ F) (hf : x ∉ f.vars) :
    pderiv x (f * g) = f * pderiv x g := by
  rw [pderiv_mul, pderiv_eq_zero_of_notMem_vars hf, zero_mul, zero_add]

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
    · have hxg : x ∉ g.vars := fun h => hdisj x hP (hg x h)
      have hnQ : ¬ Q x := hdisj x hP
      simp only [decide_eq_true_eq]
      rw [if_pos hP, if_neg hnQ, pderiv_mul_right x f g hxg, iterDeriv_cons]
      exact ih (pderiv x f) g (fun v hv => hf v (vars_pderiv_subset x f hv)) hg hS'
    · have hxf : x ∉ f.vars := fun h => hdisj x (hf x h) hQ
      have hnP : ¬ P x := fun hp => hdisj x hp hQ
      simp only [decide_eq_true_eq]
      rw [if_neg hnP, if_pos hQ, pderiv_mul_left x f g hxf, iterDeriv_cons]
      exact ih f (pderiv x g) hf (fun v hv => hg v (vars_pderiv_subset x g hv)) hS'

/-! ## R-factor disjoint Leibniz — PROVED -/

theorem iterDeriv_prod_disjoint {ι : Type*} [DecidableEq ι]
    (f : ι → MvPolynomial σ F) (T : Finset ι)
    (block : ι → σ → Prop) [∀ c, DecidablePred (block c)]
    (hf_vars : ∀ c ∈ T, ∀ v ∈ (f c).vars, block c v)
    (hdisjoint : ∀ c₁ ∈ T, ∀ c₂ ∈ T, c₁ ≠ c₂ → ∀ v, block c₁ v → ¬ block c₂ v)
    (S : List σ) (hS : ∀ x ∈ S, ∃ c ∈ T, block c x) :
    iterDeriv S (T.prod f) = T.prod (fun c => iterDeriv (S.filter (block c)) (f c)) := by
  induction T using Finset.induction_on generalizing S with
  | empty =>
    have : S = [] := by
      by_contra h
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil S h
      obtain ⟨c, hc, _⟩ := hS x hx
      simp at hc
    subst this; simp [iterDeriv]
  | @insert c₀ T' hc₀ ih =>
    classical
    rw [Finset.prod_insert hc₀]
    -- Define Q = "belongs to some block in T'"
    let Q : σ → Prop := fun v => ∃ c ∈ T', block c v
    -- Apply 2-factor version
    have hf0 : ∀ v ∈ (f c₀).vars, block c₀ v :=
      hf_vars c₀ (Finset.mem_insert_self c₀ T')
    have hprod_vars : ∀ v ∈ (T'.prod f).vars, Q v := by
      intro v hv
      obtain ⟨c, hc, hcv⟩ := Finset.mem_biUnion.mp (vars_prod f hv)
      exact ⟨c, hc, hf_vars c (Finset.mem_insert_of_mem hc) v hcv⟩
    have hdisj' : ∀ v, block c₀ v → ¬ Q v := by
      intro v hv ⟨c, hc, hcv⟩
      exact hdisjoint c₀ (Finset.mem_insert_self c₀ T') c
        (Finset.mem_insert_of_mem hc) (fun h => hc₀ (h ▸ hc)) v hv hcv
    have hS' : ∀ x ∈ S, block c₀ x ∨ Q x := by
      intro x hx; obtain ⟨c, hc, hcx⟩ := hS x hx
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact Or.inl hcx
      · exact Or.inr ⟨c, hc', hcx⟩
    rw [iterDeriv_mul_disjoint (f c₀) (T'.prod f) (block c₀) Q hf0 hprod_vars hdisj' S hS']
    -- LHS: iterDeriv (S.filter (block c₀)) (f c₀) * iterDeriv (S.filter Q) (T'.prod f)
    -- Apply IH to the second factor
    have hIH_vars : ∀ c ∈ T', ∀ v ∈ (f c).vars, block c v :=
      fun c hc => hf_vars c (Finset.mem_insert_of_mem hc)
    have hIH_disj : ∀ c₁ ∈ T', ∀ c₂ ∈ T', c₁ ≠ c₂ → ∀ v, block c₁ v → ¬ block c₂ v :=
      fun c₁ hc₁ c₂ hc₂ => hdisjoint c₁ (Finset.mem_insert_of_mem hc₁) c₂
        (Finset.mem_insert_of_mem hc₂)
    have hSQ : ∀ x ∈ S.filter Q, ∃ c ∈ T', block c x := by
      intro x hx
      have := (List.mem_filter.mp hx).2
      simp only [decide_eq_true_eq] at this
      exact this
    rw [ih hIH_vars hIH_disj (S.filter Q) hSQ]
    -- Now: LHS = iterDeriv (filter c₀) (f c₀) * ∏_{c∈T'} iterDeriv (filter Q |> filter c) (f c)
    -- RHS = ∏_{c ∈ insert c₀ T'} iterDeriv (filter c) (f c)
    --     = iterDeriv (filter c₀) (f c₀) * ∏_{c∈T'} iterDeriv (filter c) (f c)
    rw [Finset.prod_insert hc₀]
    congr 1
    -- Need: for c ∈ T', (S.filter Q).filter (block c) = S.filter (block c)
    apply Finset.prod_congr rfl
    intro c hc
    congr 1
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    -- (decide (Q x) && decide (block c x)) = decide (block c x)
    cases hb : decide (block c x)
    · simp [hb]
    · simp [hb]; exact ⟨c, hc, decide_eq_true_eq.mp hb⟩

end DisjointLeibniz
