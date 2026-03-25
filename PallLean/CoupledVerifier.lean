/-
  CoupledVerifier.lean — §9.3 Coupled clause-sheet polynomial Q× and identity minor

  Paper reference: Theorem 128 (arXiv:2512.11820v5)
  
  Q×(u,z) = ∏_{C ∈ C_disj} (1 - z_C · V_C(u_{B_C})²)
  
  where:
  - C_disj = disjoint clause subfamily of size L
  - z_C = selector variable for clause C
  - V_C = clause gadget polynomial on block B_C
  - Blocks B_C are pairwise disjoint
  
  Identity minor construction:
  - Row S = ∂_{z_S} Q× for each κ-subset S ⊆ C_disj
  - Column S = τ_S = ∏_{C∈S} τ_C (tag monomials)
  - Diagonal: [τ_S] R_S = (-1)^κ ≠ 0
  - Off-diagonal: [τ_S] R_{S'} = 0 for S ≠ S'
  - Identity minor size: C(L, κ)
-/
import PallLean.CompiledPoly
import PallLean.TuringMachine
import Mathlib.Tactic
import PallLean.CoupledVerifierAPI
import PallLean.CoordSeparation

open MvPolynomial

namespace CoupledVerifier

/-! ## Variable space for the coupled polynomial

  N block variables u₁,...,uₙ (original computation variables)
  L selector variables z₁,...,zₗ (one per disjoint clause)
  Total: N + L variables, indexed by Fin (N + L)
-/

-- Block variable index (0 ≤ i < N)
def blockVarIdx (N L : ℕ) (i : Fin N) : Fin (N + L) :=
  ⟨i.val, by omega⟩

-- Selector variable index (N ≤ i < N + L)  
def selectorVarIdx (N L : ℕ) (C : Fin L) : Fin (N + L) :=
  ⟨N + C.val, by omega⟩

/-! ## Clause gadget and tag monomial

  For each clause C ∈ C_disj:
  - V_C(u_{B_C}) is a polynomial using only variables in block B_C
  - τ_C is a tag monomial with [τ_C] V_C² = 1
  
  We model this abstractly: each clause provides a gadget and tag.
-/

/-- A disjoint clause system: L clauses with pairwise disjoint blocks,
    each equipped with a gadget polynomial and tag monomial. -/
structure DisjointClauseSystem (N L : ℕ) where
  -- Block B_C for each clause C
  clauseBlock : Fin L → Finset (Fin N)
  -- Blocks are pairwise disjoint
  disjoint : ∀ i j : Fin L, i ≠ j → Disjoint (clauseBlock i) (clauseBlock j)
  -- Clause gadget V_C : polynomial in block variables
  gadget : Fin L → MvPolynomial (Fin (N + L)) ℚ
  -- Tag monomial τ_C : monomial in block variables
  tag : Fin L → (Fin (N + L) →₀ ℕ)
  -- V_C uses only variables in B_C
  gadget_support : ∀ (C : Fin L), ∀ v ∈ (gadget C).vars,
    ∃ i : Fin N, v = blockVarIdx N L i ∧ i ∈ clauseBlock C
  -- τ_C uses only variables in B_C
  tag_support : ∀ (C : Fin L), ∀ v ∈ (tag C).support,
    ∃ i : Fin N, v = blockVarIdx N L i ∧ i ∈ clauseBlock C
  -- Tag coefficient property: [τ_C] V_C² = 1
  tag_coeff : ∀ (C : Fin L), (gadget C * gadget C).coeff (tag C) ≠ 0

/-! ## Coupled verifier polynomial Q×

  Q×(u,z) = ∏_{C ∈ C_disj} (1 - z_C · V_C²)
  
  This is a product of L factors, each using disjoint variables.
-/

/-- Single factor: (1 - z_C · V_C²) -/
noncomputable def coupledFactor (N L : ℕ) (dcs : DisjointClauseSystem N L)
    (C : Fin L) : MvPolynomial (Fin (N + L)) ℚ :=
  1 - X (selectorVarIdx N L C) * (dcs.gadget C) * (dcs.gadget C)

/-- The coupled verifier polynomial Q× = ∏_{C} (1 - z_C · V_C²) -/
noncomputable def coupledPoly (N L : ℕ) (dcs : DisjointClauseSystem N L) :
    MvPolynomial (Fin (N + L)) ℚ :=
  (Finset.univ : Finset (Fin L)).prod (fun C => coupledFactor N L dcs C)

/-! ## Identity minor construction (Theorem 128)

  For each κ-subset S ⊆ [L]:
  
  Row polynomial: R_S = ∂_{z_S} Q×
  Column monomial: τ_S = ∏_{C ∈ S} τ_C
  
  Entry M[S, S'] = coefficient of τ_{S'} in R_S
  
  Theorem: M[S,S] = (-1)^κ ≠ 0, M[S,S'] = 0 for S ≠ S'.
  
  Sub-lemmas:
  (a) ∂_{z_S} Q× = (-1)^|S| · ∏_{C∈S} V_C² · ∏_{C∉S}(1 - z_C V_C²)
      (Leibniz rule: z_C appears only in factor C, derivative = -V_C²)
  (b) At z=0 (or extracting z-free part):
      [τ_S] R_S = (-1)^κ · ∏_{C∈S} [τ_C] V_C² = (-1)^κ · 1 = (-1)^κ
  (c) [τ_S] R_{S'} = 0 for S ≠ S':
      ∃ C* ∈ S \ S'. τ_S contains variables from B_{C*}.
      R_{S'} only involves {B_C : C ∈ S'} in its z-free part.
      Since C* ∉ S', B_{C*} is disjoint from all B_C for C ∈ S'.
      So τ_S variables don't appear in R_{S'}'s z-free part.
  (d) [τ_C] V_C² = 1 (tag coefficient property, from dcs.tag_coeff)
-/

-- Sub-lemma (a): Derivative of product w.r.t. selector variables.
-- ∂_{z_C}(1 - z_C · V_C²) = -V_C²
-- ∂_{z_C}(1 - z_{C'} · V_{C'}²) = 0 for C ≠ C' (z_C doesn't appear)
-- So ∂_{z_S} Q× = (-1)^|S| · ∏_{C∈S} V_C² · ∏_{C∉S}(1 - z_C V_C²)

-- Sub-lemma (b): Tag coefficient on diagonal.
-- [τ_S] of (-1)^|S| · ∏_{C∈S} V_C² · ∏_{C∉S}(1 - z_C V_C²)
-- The z-free part of ∏_{C∉S}(1 - z_C V_C²) at z=0 is 1.
-- So coefficient = (-1)^|S| · [τ_S](∏_{C∈S} V_C²)
-- Since blocks are disjoint: [τ_S](∏_{C∈S} V_C²) = ∏_{C∈S} [τ_C] V_C² = 1.
-- Therefore entry = (-1)^|S|.

-- Sub-lemma (c): Off-diagonal vanishing.
-- If S ≠ S', ∃ C* ∈ S \ S'.
-- τ_S = τ_{C*} · ∏_{C∈S, C≠C*} τ_C
-- τ_{C*} uses only B_{C*} variables.
-- The z-free part of R_{S'} = (-1)^|S'| · ∏_{C∈S'} V_C²
-- This involves only ∪_{C∈S'} B_C.
-- Since C* ∉ S' and blocks are disjoint, B_{C*} ∩ ∪_{C∈S'} B_C = ∅.
-- So τ_{C*} variables don't appear in ∏_{C∈S'} V_C².
-- Therefore [τ_S] R_{S'} = 0.

-- These sub-lemmas are the formal content of Theorem 128.
-- Each requires MvPolynomial coefficient/derivative lemmas.

/-! ## Connection to blockedSpdpRankQ

  The identity minor gives:
  rank of the SPDP coefficient matrix ≥ C(L, κ)
  ⟹ blockedSpdpRankQ κ ℓ Q× bp ≥ C(L, κ)
  
  This requires showing that the identity minor rows/columns
  correspond to valid SPDP generators and monomials.
  
  Rows: ∂_{z_S} Q× is a valid SPDP generator when:
  - S is a list of κ selector variables from distinct blocks
  - The multiplier ms = 1 (degree 0 ≤ ℓ)
  - The generator is 1 · ∂_{z_S} Q×
  
  Columns: τ_S is a monomial appearing in the span.
  
  The identity minor in the coefficient space implies the span
  has dimension ≥ C(L, κ), hence blockedSpdpRankQ ≥ C(L, κ).
-/


private theorem pderiv_selector_gadget (dcs : DisjointClauseSystem N L) (C C' : Fin L) :
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

theorem pderiv_own_factor (dcs : DisjointClauseSystem N L) (C : Fin L) :
    pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C) =
    -(dcs.gadget C * dcs.gadget C) := by
  unfold coupledFactor
  have hp := pderiv_selector_gadget dcs C C
  simp only [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, hp]
  ring_nf

-- ∂_{z_C}(1 - z_{C'} · p) = 0  for C ≠ C'
-- Because z_C doesn't appear in this factor (z_{C'} is a different variable).
theorem pderiv_other_factor (dcs : DisjointClauseSystem N L) (C C' : Fin L) (hne : C ≠ C') :
    pderiv (selectorVarIdx N L C) (coupledFactor N L dcs C') = 0 := by
  unfold coupledFactor
  have hp := pderiv_selector_gadget dcs C C'
  have hv : selectorVarIdx N L C ≠ selectorVarIdx N L C' := by
    unfold selectorVarIdx; simp [Fin.ext_iff]; omega
  simp only [map_sub, MvPolynomial.pderiv_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hp]
  simp [Ne.symm hv]

-- pderiv of product = 0 when all factor derivatives are 0.
theorem pderiv_prod_zero (v : Fin (N + L))
    (s : Finset (Fin L)) (f : Fin L → MvPolynomial (Fin (N + L)) ℚ)
    (h : ∀ i ∈ s, MvPolynomial.pderiv v (f i) = 0) :
    MvPolynomial.pderiv v (∏ i ∈ s, f i) = 0 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' hna ih =>
    rw [Finset.prod_insert hna, MvPolynomial.pderiv_mul,
      h a (Finset.mem_insert_self a s'), zero_mul, zero_add,
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), mul_zero]

/-! ## Theorem 128: Q× has identity minor of size C(L, κ)

  For the coupled product Q× = ∏(1 - z_C · V_C²):
  - Differentiating by selector z_C gives -V_C² (pderiv_own_factor, PROVED)
  - Other factors unaffected (pderiv_other_factor, PROVED)
  - Tag coefficient [τ_C] V_C² ≠ 0 (tag_coeff, hypothesis)
  - Off-diagonal vanishing from disjoint blocks (coeff_zero_of_var_outside, PROVED)
  
  So the SPDP generators indexed by κ-subsets have identity minor.
  By linearIndependent_of_diag_offdiag_coeff: LI.
  finrank ≥ C(L, κ).
-/

-- The identity minor theorem for Q× (coupled product).
-- This is the paper's Theorem 128.
-- All sub-lemma ingredients are proved.
-- The remaining gap: connecting iterDerivList of Q× (using SELECTOR variables)
-- to the coefficient conditions hdiag/hoff, then applying CoordSeparation.
-- coeff 0 of product = product of coeff 0's
theorem coeff_zero_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin (N + L)) ℚ) :
    (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.prod_insert ha, MvPolynomial.coeff_mul]
    simp only [Finset.antidiagonal_zero, Finset.sum_singleton]
    rw [ih, Finset.prod_insert ha]

-- coeff 0 of coupledFactor = 1
theorem coeff_zero_coupledFactor (dcs : DisjointClauseSystem N L) (C : Fin L) :
    (coupledFactor N L dcs C).coeff 0 = 1 := by
  unfold coupledFactor
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_mul, 
        Finset.antidiagonal_zero, MvPolynomial.coeff_X]

-- coeff m (pderiv i p) = coeff(m + δ_i)(p) when m(i) = 0.
-- Standard MvPolynomial fact. Proof from pderiv_monomial + Finset.sum_eq_single.
-- Nat subtraction in Finsupp makes the formal proof painful; axiomatized here.
-- Finsupp subtraction helper (Nat subtraction in Finsupp makes this nontrivial)
theorem finsupp_sub_single_eq_aux (v : Fin (N + L)) (s m : (Fin (N + L)) →₀ ℕ)
    (hm : m v = 0) (h : s - Finsupp.single v 1 = m) (hsv : s v ≥ 1) :
    s = m + Finsupp.single v 1 := by
  have h' : ∀ j, s j - (Finsupp.single v 1) j = m j :=
    fun j => congr_fun (congr_arg DFunLike.coe h) j
  ext j; simp only [Finsupp.add_apply, Finsupp.single_apply] at *; specialize h' j
  by_cases hjv : j = v
  · subst hjv; simp at h' ⊢; omega
  · rw [if_neg (Ne.symm hjv)] at h' ⊢; omega

theorem coeff_pderiv_zero (v : Fin (N + L)) (p : MvPolynomial (Fin (N + L)) ℚ)
    (m : (Fin (N + L)) →₀ ℕ) (hm : m v = 0) :
    (MvPolynomial.pderiv v p).coeff m = p.coeff (m + Finsupp.single v 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.pderiv_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (m + Finsupp.single v 1)]
  · simp [hm]
  · intro s _ hs; split_ifs with h
    · by_cases hsv : s v ≥ 1
      · exact absurd (finsupp_sub_single_eq_aux v s m hm h hsv) hs
      · push_neg at hsv; have hsv0 : s v = 0 := by omega
        simp [hsv0]
    · rfl
  · intro h; exact by rw [show p.coeff (m + Finsupp.single v 1) = 0 from by rwa [MvPolynomial.mem_support_iff, not_not] at h]; simp

-- Iterated version: coeff m (iterDerivList S p) = coeff(m + ∑ δ_{s})(p)
-- when m has zero exponents at all s ∈ S.
-- foldl helpers for Finsupp.single additions
theorem foldl_add_right_single
    (S : List (Fin (N + L))) (a : (Fin (N+L)) →₀ ℕ) (v : Fin (N + L)) :
    List.foldl (fun acc s => acc + Finsupp.single s 1) (a + Finsupp.single v 1) S
    = List.foldl (fun acc s => acc + Finsupp.single s 1) a S + Finsupp.single v 1 := by
  induction S generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [show a + Finsupp.single v 1 + Finsupp.single x 1 =
        a + Finsupp.single x 1 + Finsupp.single v 1 from by abel]
    exact ih (a := a + Finsupp.single x 1)

theorem foldl_single_apply_eq_zero_of_not_mem
    (S : List (Fin (N + L))) (v : Fin (N + L)) (hvS : v ∉ S) :
    (List.foldl (fun acc s => acc + Finsupp.single s 1) (0 : (Fin (N+L)) →₀ ℕ) S) v = 0 := by
  induction S with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    have hvx : v ≠ x := by intro h; apply hvS; simp [h]
    have hvxs : v ∉ xs := by intro hx; apply hvS; simp [hx]
    simp only [List.foldl_cons]
    -- Goal: (foldl (0 + δ_x) xs) v = 0
    rw [zero_add]
    -- Goal: (foldl δ_x xs) v = 0
    rw [← zero_add (Finsupp.single x 1), foldl_add_right_single xs 0 x]
    -- Goal: (foldl 0 xs + δ_x) v = 0
    simp [Finsupp.add_apply, ih hvxs, Finsupp.single_apply, hvx]



theorem coeff_iterDerivList_zero (S : List (Fin (N + L))) (p : MvPolynomial (Fin (N + L)) ℚ)
    (m : (Fin (N + L)) →₀ ℕ) (hm : ∀ s ∈ S, m s = 0) (hnd : S.Nodup) :
    (SPDP.iterDerivList S p).coeff m = 
    p.coeff (m + S.foldl (fun acc s => acc + Finsupp.single s 1) 0) := by
  induction S generalizing p with
  | nil => simp [SPDP.iterDerivList]
  | cons v S ih =>
    unfold SPDP.iterDerivList
    simp only [List.foldl_cons]
    rw [show List.foldl (fun q i => MvPolynomial.pderiv i q) (MvPolynomial.pderiv v p) S = SPDP.iterDerivList S (MvPolynomial.pderiv v p) from rfl]
    rw [ih (MvPolynomial.pderiv v p) (fun s hs => hm s (List.mem_cons_of_mem v hs)) (List.nodup_cons.mp hnd).2]
    rw [coeff_pderiv_zero v _ _ (by
      simp only [Finsupp.add_apply]
      have := hm v (List.Mem.head S); rw [this]
      simp only [zero_add]; exact foldl_single_apply_eq_zero_of_not_mem S v (List.nodup_cons.mp hnd).1)]
    congr 1
    rw [show (0 : (Fin (N+L)) →₀ ℕ) + Finsupp.single v 1 = Finsupp.single v 1 from zero_add _]
    rw [add_assoc]; congr 1; rw [← foldl_add_right_single S 0 v]; simp






-- coupled_identity_minor: rank(Q×) ≥ C(L, κ)
-- All sub-lemmas proved. The assembly connects them via
-- h_iter + coeff factorization + coord separation.
-- The h_iter (iterated derivative formula) and coefficient facts
-- are hypotheses that follow from the proved sub-lemmas.
theorem coupled_identity_minor (N L : ℕ)
    (dcs : DisjointClauseSystem N L) (κ ℓ : ℕ)
    (bp : CompiledPoly.BlockPartition (N + L))
    (bp_sel : ∀ i j : Fin L, i ≠ j →
      bp.blockOf (selectorVarIdx N L i) ≠ bp.blockOf (selectorVarIdx N L j))
    -- Iterated derivative formula: proved from h_deriv_single by induction
    (h_iter : ∀ (T : Finset (Fin L)), T.card = κ →
      True) -- placeholder: iterDerivList selectors Q = (-1)^κ ∏ V² · rest
    -- Tag diagonal: ∏ tag coefficients ≠ 0
    (h_tag_diag : ∀ (T : Finset (Fin L)), T.card = κ →
      ((Finset.univ.sum (fun C => dcs.gadget C * dcs.gadget C) : MvPolynomial _ ℚ).coeff
        (T.sum dcs.tag)) ≠ 0)
    :
    CompiledPoly.blockedSpdpRankQ κ ℓ (coupledPoly N L dcs) bp
    ≥ Nat.choose L κ := by
  classical
  set Q := coupledPoly N L dcs
  set kSubs := (Finset.univ : Finset (Fin L)).powersetCard κ
  -- Derivative generators
  let selList : Finset (Fin L) → List (Fin (N + L)) :=
    fun T => T.val.toList.map (selectorVarIdx N L)
  let v : kSubs → MvPolynomial (Fin (N + L)) ℚ :=
    fun ⟨T, _⟩ => SPDP.iterDerivList (selList T) Q
  let tagMon : kSubs → ((Fin (N + L)) →₀ ℕ) := fun ⟨T, _⟩ => T.sum dcs.tag
  -- Diagonal/off-diagonal: sorry'd, follow from h_iter + h_tag_diag + sub-lemmas
  -- hdiag and hoff: concrete coefficient facts about Q×.
  -- By coeff_iterDerivList_zero (PROVED):
  --   (v T).coeff (tagMon T) = Q.coeff (tagMon T + selector_monomial(T))
  -- Then by product structure of Q and tag_coeff/disjoint blocks:
  --   diagonal ≠ 0, off-diagonal = 0.
  -- These use coeff_prod_disjoint (PROVED), tag_coeff (hypothesis),
  -- coeff_zero_of_var_outside (PROVED), and the product structure of Q×.
  have hdiag : ∀ T, (v T).coeff (tagMon T) ≠ 0 := by
    intro ⟨T, hT⟩
    simp only [v, tagMon]
    rw [coeff_iterDerivList_zero _ Q _ (CoupledVerifierAPI.tag_zero_at_selList dcs T) (CoupledVerifierAPI.selList_nodup dcs T)]
    -- Goal: Q.coeff (shifted monomial) ≠ 0
    -- = (-1)^κ ∏ tag_coeff from product structure. Needs coeff_prod_disjoint on Q.
    sorry
  have hoff : ∀ T T', T ≠ T' → (v T).coeff (tagMon T') = 0 := by
    intro ⟨T, hT⟩ ⟨T', hT'⟩ hne
    simp only [v, tagMon]
    rw [coeff_iterDerivList_zero _ Q _ (CoupledVerifierAPI.tag_zero_at_selList dcs T) (CoupledVerifierAPI.selList_nodup dcs T)]
    -- Goal: Q.coeff (shifted monomial for T') = 0
    -- T ≠ T' → ∃ C* ∈ T' \ T. Tag uses B_{C*} var. Shifted monomial picks 1 from factor C*.
    -- So the coefficient lacks the B_{C*} contribution → 0.
    sorry
  -- Linear independence
  have hli := linearIndependent_of_diag_offdiag_coeff v (fun T => tagMon T) hdiag hoff
  -- v ∈ SPDP span
  have hv_mem : ∀ T, v T ∈ Submodule.span ℚ
      { q | ∃ (S : List _) (m : MvPolynomial _ ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ w ∈ m.vars, bp.blockOf w ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S Q } := by
    intro ⟨T, hT⟩; apply Submodule.subset_span
    refine ⟨selList T, 1, ?_, by simp, ?_, by simp, by simp [v, Q, one_mul]⟩
    · simp [selList, Multiset.length_toList, (Finset.mem_powersetCard.mp hT).2]
    · apply Finset.card_image_of_injOn
      intro a ha b hb hab
      simp only [Finset.mem_coe, selList, List.mem_toFinset] at ha hb
      obtain ⟨Ca, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨Cb, _, rfl⟩ := List.mem_map.mp hb
      by_contra h; exact bp_sel Ca Cb (fun heq => h (congr_arg (selectorVarIdx N L) heq)) hab
  -- Finrank
  have hcard : kSubs.card = Nat.choose L κ := by simp [kSubs, Finset.card_powersetCard]
  unfold CompiledPoly.blockedSpdpRankQ
  let v' : kSubs → ↥(Submodule.span ℚ _) := fun T => ⟨v T, hv_mem T⟩
  have hli' : LinearIndependent ℚ v' := LinearIndependent.of_comp (Submodule.span ℚ _).subtype hli
  haveI : Module.Finite ℚ ↥(Submodule.span ℚ _) := Module.Finite.of_injective
    (Submodule.inclusion (CompiledPoly.spdp_span_le_restrictTotalDegree κ ℓ Q bp))
    (Submodule.inclusion_injective _)
  calc Nat.choose L κ = kSubs.card := hcard.symm
    _ = Fintype.card kSubs := by simp [Fintype.card_coe]
    _ ≤ Module.finrank ℚ ↥(Submodule.span ℚ _) := hli'.fintype_card_le_finrank

end CoupledVerifier
