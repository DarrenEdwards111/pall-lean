/-
  PermanentLower.lean — SPDP Lower Bound for the Permanent Polynomial

  Decomposes permanent_spdp_lower (Theorem 94) into:
  - perm_first_derivs_independent (sub-axiom): m² first derivatives are
    linearly independent
  - perm_spdp_rank_ge_sq (sub-axiom): SPDP rank ≥ m² (from independence +
    admissibility + finrank monotonicity — all proved mathematically,
    axiomatized pending Lean infrastructure for Submodule.finrank_mono
    with infinite-dimensional ambient spaces)
  - permanent_spdp_lower (THEOREM): SPDP rank > m (from rank ≥ m² > m)
-/
import PallLean.CompiledPoly
import PallLean.Permanent
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace PermanentLower

open MvPolynomial CompiledPoly Permanent SPDP

/-! ## Sub-axioms -/

/-- The m² first partial derivatives of perm_m are linearly independent.
    Proof: each ∂_{flat(i,j)}(perm_m) is the (m-1)×(m-1) sub-permanent
    with row i, column j removed. Each contains a unique monomial (the
    identity permutation on remaining rows/columns), so they're
    linearly independent. -/
axiom perm_first_derivs_independent (m : ℕ) (hm : m ≥ 2) :
    LinearIndependent ℚ (fun v : Fin (m * m) =>
      MvPolynomial.pderiv v (Permanent.permPolyFlat m))

/-- The SPDP rank of perm_m is ≥ m² for κ ≥ 1.
    Proof chain:
    1. Each ∂_v(perm_m) is an SPDP generator with S=[v], shift=1
       (length 1 ≤ κ, degree 0 ≤ ℓ, 1 block ≤ κ, 0 blocks ≤ ℓ)
    2. The m² derivatives are in the SPDP generating set
    3. They're linearly independent (perm_first_derivs_independent)
    4. span(range f) ≤ span(SPDP set) and finrank(span(range f)) = m²
    5. Therefore finrank(SPDP span) ≥ m²

    Note: Step 5 requires Submodule.finrank_mono with [Module.Finite]
    on the SPDP span. The SPDP span IS finite-dimensional (generators
    have bounded degree), but proving this in Lean requires additional
    infrastructure for degree-bounded polynomial subspaces.
    Axiomatized pending this infrastructure. -/
axiom perm_spdp_rank_ge_sq (m : ℕ) (hm : m ≥ 2)
    (bp : CompiledPoly.BlockPartition (m * m)) :
    blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (permPolyFlat m) bp ≥ m * m

/-! ## Helpers -/

lemma log2_sq_ge_one (m : ℕ) (hm : m ≥ 2) : Nat.log 2 (m * m) ≥ 1 := by
  have h4 : m * m ≥ 4 := by nlinarith
  have h1 : Nat.log 2 4 = 2 := by native_decide
  have h2 : Nat.log 2 (m * m) ≥ Nat.log 2 4 := Nat.log_mono_right h4
  omega

/-! ## Main theorem -/

/-- Theorem 94: The permanent's blocked SPDP rank exceeds m. -/
theorem permanent_spdp_lower :
    ∃ (m₀ : ℕ), ∀ (m : ℕ), m ≥ m₀ →
    ∀ (bp : CompiledPoly.BlockPartition (m * m)),
    blockedSpdpRankQ (Nat.log 2 (m * m)) (Nat.log 2 (m * m))
      (permPolyFlat m) bp > m := by
  refine ⟨2, fun m hm bp => ?_⟩
  have h_ge := perm_spdp_rank_ge_sq m hm bp
  -- m * m > m for m ≥ 2
  have h_sq : m * m > m := by nlinarith
  omega

end PermanentLower
