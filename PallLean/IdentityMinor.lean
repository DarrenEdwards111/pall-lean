import PallLean.TseitinDefs
import PallLean.TagMonomial
import PallLean.ProductDeriv
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.Data.List.Sublists
/-!
# Identity Minor Construction (Theorem 9.3)

We prove that Q× = ∏(1 - z_C V_C) has a Kronecker δ identity minor
of size (L choose κ), where L = |C_disj| is the disjoint packing size.

## Proof outline (modular):

1. **Derivative lemma**: ∂_{z_S} Q× = (-1)^|S| · ∏_{C∈S} V_C · ∏_{C∉S}(1-z_C V_C)
2. **Tag selection**: For each C, tag_monomial_property gives τ_C with [τ_C]V_C = ±1
3. **Dual monomial**: τ_S = (∑_{C∈S} τ_C) + (∑_{C∉S} single(z_C, 1))
4. **Kronecker δ**: [τ_S] R_{S'} = δ_{S,S'} · (±1)

The index type is Fin (Nat.choose L κ) to match the axiom signature.
-/

namespace IdentityMinor

open MvPolynomial Tseitin ProductDeriv SPDP

variable {F : Type*} [Field F]

/-! ## Step 1: Iterated derivative of coupled verifier along selector subset -/

/-- Derivative of a single factor (1 - z_C V_C) w.r.t. z_C gives -V_C -/
theorem pderiv_selector_factor (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ c) (1 - X (selectorIdx Φ c) * clauseGadget F Φ c) =
    -(clauseGadget F Φ c) := by
  apply ProductDeriv.pderiv_one_sub_mul
  -- Need: selectorIdx Φ c ∉ (clauseGadget F Φ c).vars
  exact selector_not_in_gadget F Φ c c

/-- Derivative of factor (1 - z_{C'} V_{C'}) w.r.t. z_C for C ≠ C' gives 0 -/
theorem pderiv_selector_factor_ne (Φ : TseitinFormula)
    (c c' : Fin Φ.clauses.length) (hne : c ≠ c') :
    pderiv (selectorIdx Φ c) (1 - X (selectorIdx Φ c') * clauseGadget F Φ c') = 0 := by
  apply ProductDeriv.pderiv_one_sub_mul_ne
  · -- selectorIdx Φ c ≠ selectorIdx Φ c'
    intro heq
    exact hne (selectorIdx_injective Φ heq)
  · -- selectorIdx Φ c ∉ (clauseGadget F Φ c').vars
    exact selector_not_in_gadget F Φ c c'

/-! ## Step 2: Tag monomial selection -/

/-- For each clause, choose a tag monomial with coefficient ±1 -/
noncomputable def chooseTagMonomial (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    (Fin (tseitinNumVars Φ)) →₀ ℕ :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose

theorem chooseTagMonomial_support (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    ∀ i ∈ (chooseTagMonomial (F := F) Φ c).support,
      i.val < Φ.graph.numEdges + 3 * Φ.clauses.length :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose_spec.1

theorem chooseTagMonomial_coeff (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    coeff (chooseTagMonomial (F := F) Φ c) (clauseGadget F Φ c) = 1 ∨
    coeff (chooseTagMonomial (F := F) Φ c) (clauseGadget F Φ c) = -1 :=
  (TagMonomial.tag_monomial_property_proof F Φ c).choose_spec.2

/-! ## Proof assembly — this is the main construction -/

/-! ## Step 3: Single-step pderiv of coupled verifier

We show that differentiating the coupled verifier ∏(1 - z_C V_C) w.r.t.
one selector z_k pulls out -V_k and leaves the remaining product. -/

/-- The coupled verifier factor for clause c -/
noncomputable def cvFactor (F : Type*) [CommRing F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  1 - X (selectorIdx Φ c) * clauseGadget F Φ c

theorem coupledVerifier_eq_prod (Φ : TseitinFormula) :
    coupledVerifier F Φ = Finset.univ.prod (cvFactor F Φ) := by
  unfold coupledVerifier cvFactor; rfl

/-- pderiv z_k of cvFactor c:
    - If c = k: gives -V_k
    - If c ≠ k: gives 0 -/
theorem pderiv_cvFactor_eq (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ c) (cvFactor F Φ c) =
    -(clauseGadget F Φ c) := by
  unfold cvFactor
  exact pderiv_selector_factor Φ c

theorem pderiv_cvFactor_ne (Φ : TseitinFormula)
    (k c : Fin Φ.clauses.length) (hne : k ≠ c) :
    pderiv (selectorIdx Φ k) (cvFactor F Φ c) = 0 := by
  unfold cvFactor
  exact pderiv_selector_factor_ne Φ k c hne

/-- Applying pderiv z_k to the coupled verifier pulls out -V_k
    and leaves the product over remaining factors.

    ∂_{z_k} ∏_c (1 - z_c V_c) = -V_k · ∏_{c≠k} (1 - z_c V_c) -/
theorem pderiv_coupledVerifier_single (Φ : TseitinFormula)
    (k : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ k) (coupledVerifier F Φ) =
    -(clauseGadget F Φ k) * (Finset.univ.erase k).prod (cvFactor F Φ) := by
  rw [coupledVerifier_eq_prod]
  have hother : ∀ j ∈ (Finset.univ : Finset (Fin Φ.clauses.length)),
      j ≠ k → pderiv (selectorIdx Φ k) (cvFactor F Φ j) = 0 :=
    fun j _ hne => pderiv_cvFactor_ne Φ k j hne.symm
  rw [pderiv_prod_single (Finset.mem_univ k) hother,
      pderiv_cvFactor_eq Φ k]

/-! ## Step 3.5: Selector derivatives kill clause gadgets -/

/-- pderiv of clauseGadget w.r.t. any selector is 0 -/
theorem pderiv_selector_clauseGadget_eq_zero (Φ : TseitinFormula) [Nontrivial F]
    (k c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ k) (clauseGadget F Φ c) = 0 :=
  pderiv_eq_zero_of_notMem_vars (selector_not_in_gadget F Φ k c)

/-- pderiv of -clauseGadget w.r.t. any selector is 0 -/
theorem pderiv_selector_neg_clauseGadget_eq_zero (Φ : TseitinFormula) [Nontrivial F]
    (k c : Fin Φ.clauses.length) :
    pderiv (selectorIdx Φ k) (-(clauseGadget F Φ c)) = 0 := by
  rw [map_neg, pderiv_selector_clauseGadget_eq_zero Φ k c, neg_zero]

/-! ## Step 3.6: iterDerivList passes through constant factors -/

/-- If pderiv i f = 0 for all i in the index list, then
    iterDerivList indices (f * g) = f * iterDerivList indices g -/
theorem iterDerivList_mul_const_left
    {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (f g : MvPolynomial (Fin n) F)
    (hf : ∀ i ∈ indices, pderiv i f = 0) :
    iterDerivList indices (f * g) = f * iterDerivList indices g := by
  induction indices generalizing g with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    have hi : pderiv i f = 0 := hf i (by simp)
    rw [pderiv_mul, hi, zero_mul, zero_add]
    exact ih _ (fun j hj => hf j (by simp [hj]))

/-! ## Step 4: Iterated derivative of product along selector list

For a list of distinct selectors [z₁,...,zₖ], differentiating
∏_c (1-z_c V_c) gives (-1)^k · ∏_{c∈S} V_c · ∏_{c∉S} (1-z_c V_c)

We prove this by induction on the selector list. -/

/-- Iterated pderiv along a list of selector variables applied to a
    Finset.prod of cvFactors. After differentiating w.r.t. selectors in `ks`,
    the result is: (-1)^|ks| · (∏_{c∈ks} V_c) · (∏_{c∈remaining} cvFactor c)

    We state this for a product over a finset `s` containing all of `ks`. -/
theorem iterDeriv_cvProd_eq [Nontrivial F] (Φ : TseitinFormula)
    (ks : List (Fin Φ.clauses.length)) (hnd : ks.Nodup)
    (s : Finset (Fin Φ.clauses.length)) (hks : ∀ k ∈ ks, k ∈ s) :
    iterDerivList (ks.map (selectorIdx Φ)) (s.prod (cvFactor F Φ)) =
    C ((-1 : F)^ks.length) * (ks.map (clauseGadget F Φ)).prod *
      (s \ ks.toFinset).prod (cvFactor F Φ) := by
  induction ks generalizing s with
  | nil =>
    simp only [List.map_nil, List.length_nil, pow_zero, map_one, List.prod_nil, mul_one, one_mul,
               List.toFinset_nil, Finset.sdiff_empty]
    rfl
  | cons k rest ih =>
    -- iterDerivList (sel(k) :: rest.map sel) p = iterDerivList (rest.map sel) (pderiv sel(k) p)
    simp only [List.map_cons]
    show iterDerivList (selectorIdx Φ k :: rest.map (selectorIdx Φ)) (s.prod (cvFactor F Φ)) = _
    rw [show iterDerivList (selectorIdx Φ k :: rest.map (selectorIdx Φ)) (s.prod (cvFactor F Φ)) =
        iterDerivList (rest.map (selectorIdx Φ)) (pderiv (selectorIdx Φ k) (s.prod (cvFactor F Φ)))
      from by unfold iterDerivList; simp [List.foldl]]
    -- pderiv sel(k) of the product gives -V_k * (s\{k}).prod cvFactor
    have hk_mem : k ∈ s := hks k (by simp)
    have hother : ∀ j ∈ s, j ≠ k →
        pderiv (selectorIdx Φ k) (cvFactor F Φ j) = 0 :=
      fun j _ hne => pderiv_cvFactor_ne Φ k j hne.symm
    rw [pderiv_prod_single hk_mem hother, pderiv_cvFactor_eq Φ k]
    -- Now: iterDerivList (rest.map sel) (-V_k * (s.erase k).prod cvFactor)
    -- -V_k is constant w.r.t. remaining selector pderivs
    have hconst : ∀ i ∈ rest.map (selectorIdx Φ),
        pderiv i (-(clauseGadget F Φ k)) = 0 := by
      intro i hi
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hi
      exact pderiv_selector_neg_clauseGadget_eq_zero Φ c k
    rw [iterDerivList_mul_const_left _ _ _ hconst]
    -- Apply IH to rest and s.erase k
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hk_not : k ∉ rest := (List.nodup_cons.mp hnd).1
    have hrest_in : ∀ j ∈ rest, j ∈ s.erase k := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h => hk_not (h ▸ hj), hks j (by simp [hj])⟩
    rw [ih hnd' (s.erase k) hrest_in]
    -- Simplify: (-V_k) * (C((-1)^|rest|) * ∏V * ∏cvFactor)
    -- = C((-1)^(|rest|+1)) * (V_k * ∏V) * ∏cvFactor
    -- and s.erase k \ rest.toFinset = s \ (k :: rest).toFinset
    have hset : s.erase k \ rest.toFinset = s \ (k :: rest).toFinset := by
      ext x
      simp [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons]
      tauto
    rw [hset]
    simp only [List.length_cons, List.prod_cons]
    rw [pow_succ, map_mul, map_neg, map_one]
    ring

end IdentityMinor
