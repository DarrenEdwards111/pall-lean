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

/-! ## Sub-axiom -/

/-- The m² first partial derivatives of perm_m are linearly independent.
    Each ∂_{flat(i,j)}(perm_m) is the (m-1)×(m-1) sub-permanent.
    Linear independence: each has a unique monomial (identity permutation
    on remaining rows/columns). -/
axiom perm_first_derivs_independent (m : ℕ) (hm : m ≥ 2) :
    LinearIndependent ℚ (fun v : Fin (m * m) =>
      MvPolynomial.pderiv v (permPolyFlat m))

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
