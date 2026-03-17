/-
  PermanentLower.lean — SPDP Lower Bound for the Permanent Polynomial

  Decomposes permanent_spdp_lower (Theorem 94) into:
  - perm_first_derivs_independent (sub-axiom): m² first derivatives of
    perm_m are linearly independent
  - permanent_spdp_lower (THEOREM): SPDP rank > m

  The derivation uses:
  1. Each first derivative is an SPDP generator (admissibility)
  2. span(derivatives) ≤ span(SPDP set)
  3. SPDP set ⊆ restrictTotalDegree, which is Module.Finite
  4. finrank_mono gives SPDP rank ≥ m²
  5. m² > m for m ≥ 2
-/
import PallLean.CompiledPoly
import PallLean.Permanent
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.MvPolynomial.Basic

namespace PermanentLower

open MvPolynomial CompiledPoly Permanent SPDP

/-! ## Unique monomial implies linear independence -/

/-- If each polynomial p_i has a "witness" monomial α_i with nonzero coefficient,
    and for j ≠ i the coefficient of α_i in p_j is zero,
    then the p_i are linearly independent. -/
theorem linearIndependent_of_unique_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] [IsDomain R]
    (p : ι → MvPolynomial σ R)
    (α : ι → (σ →₀ ℕ))  -- witness monomials
    (h_nonzero : ∀ i, MvPolynomial.coeff (α i) (p i) ≠ 0)
    (h_unique : ∀ i j, i ≠ j → MvPolynomial.coeff (α i) (p j) = 0) :
    LinearIndependent R p := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  -- Evaluate the coefficient of α i in the linear combination = 0
  have h := congr_arg (MvPolynomial.coeff (α i)) hl
  simp only [map_zero] at h
  -- Rewrite the linear combination as a sum
  rw [Finsupp.linearCombination_apply] at h
  simp only [Finsupp.sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at h
  -- Only the i-th term survives (others have coeff 0 at α i)
  by_cases hi : i ∈ l.support
  · rw [← Finset.add_sum_erase _ _ hi] at h
    have h_rest : ∀ j ∈ l.support.erase i, l j * MvPolynomial.coeff (α i) (p j) = 0 := by
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      rw [h_unique i j hne.symm, mul_zero]
    rw [Finset.sum_eq_zero h_rest, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (h_nonzero i)
  · simp only [Finsupp.mem_support_iff, not_not] at hi; exact hi

/-! ## Sub-axiom: permanent's derivatives have unique monomials -/

/-- Each first derivative of the permanent has a "diagonal" monomial
    that appears in no other first derivative. This is the content
    needed for linear independence.

    For ∂_{flat(i₀,j₀)}(perm_m): the witness monomial is the product
    ∏_{i≠i₀} x_{i, π_{j₀}(i)} where π_{j₀} maps remaining rows to
    columns in {0,...,m-1}\{j₀} in order (identity-like permutation).

    Proving this requires computing pderiv on permPolyFlat and
    extracting specific coefficients — substantial monomial algebra. -/
axiom perm_derivs_have_unique_monomials (m : ℕ) (hm : m ≥ 2) :
    ∃ (α : Fin (m * m) → ((Fin (m * m)) →₀ ℕ)),
      (∀ v, MvPolynomial.coeff (α v) (MvPolynomial.pderiv v (permPolyFlat m)) ≠ 0) ∧
      (∀ v w, v ≠ w → MvPolynomial.coeff (α v) (MvPolynomial.pderiv w (permPolyFlat m)) = 0)

/-- The m² first partial derivatives of perm_m are linearly independent. -/
theorem perm_first_derivs_independent (m : ℕ) (hm : m ≥ 2) :
    LinearIndependent ℚ (fun v : Fin (m * m) =>
      MvPolynomial.pderiv v (permPolyFlat m)) := by
  obtain ⟨α, h_nz, h_uniq⟩ := perm_derivs_have_unique_monomials m hm
  exact linearIndependent_of_unique_coeff _ α h_nz h_uniq

/-! ## Helpers -/

lemma log2_sq_ge_one (m : ℕ) (hm : m ≥ 2) : Nat.log 2 (m * m) ≥ 1 := by
  have h4 : m * m ≥ 4 := by nlinarith
  have h1 : Nat.log 2 4 = 2 := by native_decide
  have h2 : Nat.log 2 (m * m) ≥ Nat.log 2 4 := Nat.log_mono_right h4
  omega

/-- SPDP generators have bounded total degree. -/
lemma spdp_gen_totalDegree_le {N : ℕ} {κ ℓ : ℕ}
    {poly : MvPolynomial (Fin N) ℚ}
    {bp : CompiledPoly.BlockPartition N}
    {q : MvPolynomial (Fin N) ℚ}
    (hq : q ∈ { r : MvPolynomial (Fin N) ℚ |
      ∃ (S : List (Fin N)) (sh : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ ℓ ∧
        q = sh * iterDerivList S poly }) :
    q.totalDegree ≤ ℓ + poly.totalDegree := by
  obtain ⟨S, sh, _, hsh_deg, _, _, rfl⟩ := hq
  calc (sh * iterDerivList S poly).totalDegree
      ≤ sh.totalDegree + (iterDerivList S poly).totalDegree :=
        MvPolynomial.totalDegree_mul sh (iterDerivList S poly)
    _ ≤ ℓ + poly.totalDegree := by
        have := SPDP.totalDegree_iterDerivList_le S poly
        omega

/-- The SPDP span is contained in the degree-bounded submodule. -/
lemma spdp_span_le_restrictTotalDegree {N : ℕ} (κ ℓ : ℕ)
    (poly : MvPolynomial (Fin N) ℚ)
    (bp : CompiledPoly.BlockPartition N) :
    Submodule.span ℚ { q : MvPolynomial (Fin N) ℚ |
      ∃ (S : List (Fin N)) (sh : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ ℓ ∧
        q = sh * iterDerivList S poly } ≤
    MvPolynomial.restrictTotalDegree (Fin N) ℚ (ℓ + poly.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
  exact spdp_gen_totalDegree_le hq

/-! ## Main theorem -/

theorem permanent_spdp_lower :
    ∃ (m₀ : ℕ), ∀ (m : ℕ), m ≥ m₀ →
    ∀ (bp : CompiledPoly.BlockPartition (m * m)),
    CompiledPoly.blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (permPolyFlat m) bp > m := by
  refine ⟨2, fun m hm bp => ?_⟩
  set κ := Nat.log 2 (m * m)
  have hκ : κ ≥ 1 := log2_sq_ge_one m hm
  -- The derivative family
  set f := fun v : Fin (m * m) => MvPolynomial.pderiv v (permPolyFlat m)
  have h_indep := perm_first_derivs_independent m hm
  -- The SPDP generating set
  set spdp := { q : MvPolynomial (Fin (m * m)) ℚ |
      ∃ (S : List (Fin (m * m))) (sh : MvPolynomial (Fin (m * m)) ℚ),
        S.length ≤ κ ∧ sh.totalDegree ≤ κ ∧
        (S.toFinset.image bp.blockOf).card ≤ κ ∧
        (sh.vars.image bp.blockOf).card ≤ κ ∧
        q = sh * iterDerivList S (permPolyFlat m) }
  -- blockedSpdpRankQ = finrank of span of spdp
  have h_eq : CompiledPoly.blockedSpdpRankQ κ κ (permPolyFlat m) bp =
      Module.finrank ℚ (Submodule.span ℚ spdp) := by
    unfold CompiledPoly.blockedSpdpRankQ; rfl
  rw [h_eq]
  -- Each f v is in spdp
  have h_mem : ∀ v : Fin (m * m), f v ∈ spdp := by
    intro v
    have : f v = pderiv v (permPolyFlat m) := rfl
    rw [this]
    exact ⟨[v], 1, by simp; exact hκ, by simp, by simp [List.toFinset_cons]; exact hκ,
           by simp [MvPolynomial.vars_one], by simp [iterDerivList, one_mul]⟩
  -- range f ⊆ spdp, so span(range f) ≤ span(spdp)
  have h_span_le : Submodule.span ℚ (Set.range f) ≤ Submodule.span ℚ spdp :=
    Submodule.span_mono (fun x ⟨v, hv⟩ => hv ▸ h_mem v)
  -- span(spdp) is contained in restrictTotalDegree, hence finite-dimensional
  have h_fin : Module.Finite ℚ (Submodule.span ℚ spdp) := by
    have h_le := spdp_span_le_restrictTotalDegree κ κ (permPolyFlat m) bp
    exact Module.Finite.of_injective
      (Submodule.inclusion h_le)
      (Submodule.inclusion_injective h_le)
  -- finrank(span(range f)) = m * m
  have h_fr : Module.finrank ℚ (Submodule.span ℚ (Set.range f)) = m * m :=
    (finrank_span_eq_card h_indep).trans (Fintype.card_fin (m * m))
  -- finrank(span(spdp)) ≥ m * m by finrank_mono
  have h_rank_ge : Module.finrank ℚ (Submodule.span ℚ spdp) ≥ m * m := by
    calc Module.finrank ℚ (Submodule.span ℚ spdp)
        ≥ Module.finrank ℚ (Submodule.span ℚ (Set.range f)) :=
          Submodule.finrank_mono h_span_le
      _ = m * m := h_fr
  -- m * m > m for m ≥ 2
  linarith [show m * m > m from by nlinarith]

end PermanentLower
