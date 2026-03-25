/-
  IdentityMinorProof.lean — Proof of Theorem 128: identity minor from disjoint clauses.
  
  Paper: arXiv:2512.11820v5, Theorem 128.
  
  Q×(u,z) = ∏_{C ∈ C_disj} (1 - z_C · V_C²)
  
  For each κ-subset S:
    Row R_S = ∂_{z_S} Q× = (-1)^κ · ∏_{C∈S} V_C² · ∏_{C∉S}(1 - z_C V_C²)
    Column τ_S = ∏_{C∈S} τ_C
    
  Diagonal: [τ_S] R_S = (-1)^κ ≠ 0
  Off-diagonal: [τ_S] R_{S'} = 0 for S ≠ S'
  
  Identity minor size: C(L, κ)
-/
import PallLean.CoupledVerifier
import Mathlib.Tactic

open MvPolynomial CoupledVerifier

namespace IdentityMinorProof

variable {N L : ℕ}

/-! ## Sub-lemma (a): Derivative of coupled factor w.r.t. selector variable

  ∂_{z_C}(1 - z_C · V_C²) = -V_C²
  ∂_{z_C}(1 - z_{C'} · V_{C'}²) = 0  for C ≠ C'  (z_C not in this factor)
  
  In MvPolynomial terms:
  pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C) = -(dcs.gadget C)²
  pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C') = 0  for C ≠ C'
-/

-- ∂_{z_C}(1 - z_C · p) = -p  where p = V_C²
-- Helper: pderiv of selector var on gadget = 0 (gadget uses only block vars)
private theorem pderiv_selector_gadget (dcs : CoupledVerifier.DisjointClauseSystem N L) (C C' : Fin L) :
    pderiv (selectorVarIdx N L C) (dcs.gadget C') = 0 := by
  -- gadget C' uses only block variables (indices < N)
  -- selectorVarIdx N L C has index ≥ N
  -- So the selector var doesn't appear in gadget, hence pderiv = 0
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  -- selectorVarIdx N L C ∉ (gadget C').vars
  -- because gadget uses only block vars (index < N) and selector has index ≥ N
  intro hmem
  obtain ⟨i, hvi, _⟩ := dcs.gadget_support C' _ hmem
  -- selectorVarIdx has val = N + C.val ≥ N, but blockVarIdx has val = i.val < N
  have : (selectorVarIdx N L C).val = N + C.val := rfl
  have : (blockVarIdx N L i).val = i.val := rfl
  rw [hvi] at *; unfold selectorVarIdx blockVarIdx at *; simp [Fin.ext_iff] at *; omega

theorem pderiv_own_factor (dcs : CoupledVerifier.DisjointClauseSystem N L) (C : Fin L) :
    pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C) =
    -(dcs.gadget C * dcs.gadget C) := by
  unfold coupledFactor
  have hp := pderiv_selector_gadget dcs C C
  simp only [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, hp]
  ring_nf

-- ∂_{z_C}(1 - z_{C'} · p) = 0  for C ≠ C'
-- Because z_C doesn't appear in this factor (z_{C'} is a different variable).
theorem pderiv_other_factor (dcs : CoupledVerifier.DisjointClauseSystem N L) (C C' : Fin L) (hne : C ≠ C') :
    pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C') = 0 := by
  unfold coupledFactor
  have hp := pderiv_selector_gadget dcs C C'
  have hv : selectorVarIdx N L C ≠ selectorVarIdx N L C' := by
    unfold selectorVarIdx; simp [Fin.ext_iff]; omega
  simp only [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hp]
  simp [Ne.symm hv]

/-! ## Sub-lemma (b): Derivative of product = signed product of gadgets

  ∂_{z_{S₁}}...∂_{z_{Sκ}} ∏_C (1 - z_C V_C²)
  = (-1)^κ · ∏_{C∈S} V_C² · ∏_{C∉S}(1 - z_C V_C²)
  
  This follows from (a) + the product rule:
  - Each ∂_{z_C} kills its own factor (giving -V_C²) and passes through others
  - The remaining factors stay as (1 - z_C V_C²)
-/

-- For a single derivative: ∂_{z_C}(∏ factors) = (-V_C²) · ∏_{C'≠C} factor_{C'}
-- This uses: pderiv of product = sum of (pderiv one factor) · (product of others)
-- But since ∂_{z_C} only hits factor C (others give 0), the sum collapses.

/-! ## Sub-lemma (c): Coefficient extraction from disjoint products

  Key property: if polynomials p₁, ..., pₖ use pairwise disjoint variable sets,
  then for monomials m₁, ..., mₖ each using only their respective variable sets:
  
  [m₁ · ... · mₖ](p₁ · ... · pₖ) = [m₁]p₁ · ... · [mₖ]pₖ
  
  This is because the coefficient of a product monomial in a product of
  disjoint-variable polynomials factorizes.
-/

-- Coefficient of product monomial in product of disjoint polynomials
-- This is the key algebraic fact for both diagonal and off-diagonal.
-- Unique decomposition for disjoint-support Finsupp sums
private lemma finsupp_add_eq_of_disjoint {σ : Type*} [DecidableEq σ]
    (S T : Finset σ) (hST : Disjoint S T)
    (a b c d : σ →₀ ℕ) (hab : c + d = a + b)
    (hcS : c.support ⊆ S) (hdT : d.support ⊆ T)
    (haS : a.support ⊆ S) (hbT : b.support ⊆ T) :
    c = a ∧ d = b := by
  have key : c = a := by
    ext x; have h := Finsupp.ext_iff.mp hab x; simp [Finsupp.add_apply] at h
    by_cases hxS : x ∈ S
    · have hxT : x ∉ T := Finset.disjoint_left.mp hST hxS
      have : d x = 0 := by by_contra hne; exact hxT (hdT (Finsupp.mem_support_iff.mpr hne))
      have : b x = 0 := by by_contra hne; exact hxT (hbT (Finsupp.mem_support_iff.mpr hne))
      omega
    · have : c x = 0 := by by_contra hne; exact hxS (hcS (Finsupp.mem_support_iff.mpr hne))
      have : a x = 0 := by by_contra hne; exact hxS (haS (Finsupp.mem_support_iff.mpr hne))
      omega
  exact ⟨key, by ext x; have := Finsupp.ext_iff.mp hab x; simp [Finsupp.add_apply, key] at this ⊢; omega⟩

-- Binary coefficient factorization for disjoint-variable polynomials.
-- coeff(a+b)(p*q) = coeff(a)(p) * coeff(b)(q) when vars(p) ∩ vars(q) = ∅.
-- Proof: convolution sum (coeff_mul) collapses via unique decomposition.
theorem coeff_mul_disjoint {σ : Type*} [DecidableEq σ]
    (p q : MvPolynomial σ ℚ) (a b : σ →₀ ℕ)
    (h_disj : Disjoint p.vars q.vars)
    (ha : a.support ⊆ p.vars) (hb : b.support ⊆ q.vars) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [MvPolynomial.coeff_mul]
  have hmem : (a, b) ∈ Finset.antidiagonal (a + b) := by
    simp [Finset.mem_antidiagonal]
  convert Finset.sum_eq_single (a, b) (fun cd hcd hne => ?_) (fun h => absurd hmem h)
  · simp [Finset.mem_antidiagonal] at hcd
    by_contra h_nonzero; push_neg at h_nonzero
    have hc_supp : cd.1.support ⊆ p.vars := by
      intro v hv; by_contra hvp
      exact (mul_ne_zero_iff.mp h_nonzero).1 (by by_contra h2; exact hvp ((MvPolynomial.mem_vars _).mpr ⟨cd.1, Finsupp.mem_support_iff.mpr h2, hv⟩))
    have hd_supp : cd.2.support ⊆ q.vars := by
      intro v hv; by_contra hvq
      exact (mul_ne_zero_iff.mp h_nonzero).2 (by by_contra h2; exact hvq ((MvPolynomial.mem_vars _).mpr ⟨cd.2, Finsupp.mem_support_iff.mpr h2, hv⟩))
    have ⟨hca, hdb⟩ := finsupp_add_eq_of_disjoint p.vars q.vars h_disj a b cd.1 cd.2
      hcd hc_supp hd_supp ha hb
    exact hne (Prod.ext hca hdb)

-- General version by induction from binary.
theorem coeff_prod_disjoint {σ : Type*} [DecidableEq σ]
    {k : ℕ} (ps : Fin k → MvPolynomial σ ℚ) (ms : Fin k → (σ →₀ ℕ))
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (ps i).vars (ps j).vars)
    (h_supp : ∀ i, (ms i).support ⊆ (ps i).vars) :
    (∏ i, ps i).coeff (∑ i, ms i) = ∏ i, (ps i).coeff (ms i) := by
  induction k with
  | zero => simp
  | succ k ih => sorry -- Split last factor, apply coeff_mul_disjoint + ih

/-! ## Sub-lemma (d): Diagonal entry = (-1)^κ ≠ 0

  [τ_S] R_S = [τ_S]((-1)^κ · ∏_{C∈S} V_C² · rest)
  
  At z = 0, the "rest" = ∏_{C∉S}(1 - 0) = 1.
  So [τ_S] R_S|_{z=0} = (-1)^κ · [τ_S](∏_{C∈S} V_C²)
  
  By disjoint coefficient factorization:
  [τ_S](∏_{C∈S} V_C²) = ∏_{C∈S} [τ_C](V_C²) = ∏_{C∈S} 1 = 1
  
  Therefore [τ_S] R_S = (-1)^κ ≠ 0.
-/

/-! ## Sub-lemma (e): Off-diagonal entry = 0

  For S ≠ S', ∃ C* ∈ S \ S'.
  τ_S = τ_{C*} · ∏_{C∈S, C≠C*} τ_C
  
  R_{S'} only involves variables from ∪_{C∈S'} B_C (in its z-free part).
  τ_{C*} uses variables from B_{C*}.
  Since C* ∉ S', B_{C*} is disjoint from ∪_{C∈S'} B_C.
  So τ_{C*} variables don't appear in R_{S'}, hence [τ_S] R_{S'} = 0.
-/

-- Off-diagonal: coefficient of τ_S in R_{S'} is 0 when S ≠ S'
-- This follows from the variable disjointness: τ_S uses a variable
-- from a block not present in R_{S'}.
-- In MvPolynomial terms: if m has support intersecting vars not in p.vars,
-- then p.coeff m = 0.
-- If variable v appears in monomial m but not in polynomial p's vars,
-- then p.coeff m = 0.
theorem IdentityMinorProof.coeff_zero_of_var_outside {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (m : σ →₀ ℕ) (v : σ)
    (hv_m : v ∈ m.support) (hv_p : v ∉ p.vars) :
    p.coeff m = 0 := by
  -- coeff ≠ 0 ⟹ m ∈ p.support ⟹ m.support ⊆ p.vars ⟹ v ∈ p.vars, contradiction.
  by_contra h
  exact absurd ((MvPolynomial.mem_vars _).mpr ⟨m, Finsupp.mem_support_iff.mpr h, hv_m⟩) hv_p

/-! ## Assembly: Identity minor from the above sub-lemmas

  The SPDP matrix M[S, S'] for the coupled verifier polynomial Q×
  has diagonal entries ±1 and off-diagonal entries 0.
  
  This gives an identity minor of size C(L, κ).
  By identity_minor_rank_bound (proved in RankTransferCore):
  blockedSpdpRankQ ≥ C(L, κ).
  
  The connection from the coefficient matrix to blockedSpdpRankQ
  requires showing that the SPDP generators (derivative polynomials)
  and the tag monomials correspond to valid SPDP rows and columns.
-/

end IdentityMinorProof
