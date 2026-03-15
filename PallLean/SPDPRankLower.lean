/-
  SPDPRankLower.lean — SPDP rank lower bound at n=2

  Paper §8.6 at n=2: non-constant restricted polynomials have SPDP rank ≥ 2.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace SPDPRankLower

open MvPolynomial SPDP RestrictedSPDP Restriction UniversalRestriction BoolEval

/-- Helper: if a submodule of a finite-dimensional module contains two elements
    satisfying the linearIndependent_fin2 condition, then finrank ≥ 2. -/
private theorem finrank_ge_two_of_li {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V]
    (W : Submodule ℚ V) (v₁ v₂ : V) (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ W)
    (hne : v₂ ≠ 0) (hni : ∀ a : ℚ, a • v₂ ≠ v₁) :
    2 ≤ Module.finrank ℚ W := by
  have hli : LinearIndependent ℚ (fun i : Fin 2 => (⟨![v₁, v₂] i,
    by fin_cases i <;> simp_all [Matrix.cons_val_one]⟩ : W)) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h; apply hne; exact Subtype.ext_iff.mp h
    · intro a h; exact hni a (Subtype.ext_iff.mp h)
  exact hli.fintype_card_le_finrank

/-- Core claim: at n=2, if f(0,0) ≠ f(0,1), no polynomial representing f
    has restrictedSpdpRank ≤ 1 under ρ*. -/
theorem not_infspdp_of_inconsistent_n2
    (f : (Fin 2 → Bool) → Bool)
    (hne : f (![false, false]) ≠ f (![false, true]))
    (p : MvPolynomial (Fin 2) ℚ)
    (hp : ∀ x, eval (fun i => boolToRat (x i)) p = boolToRat (f x))
    : ¬ (restrictedSpdpRank (Nat.log 2 2) (Nat.log 2 2) p
          (universalRestriction 2) ≤ Nat.sqrt 2) := by
  -- Step 1: Nat.log 2 2 = 1, Nat.sqrt 2 = 1
  have hlog : Nat.log 2 2 = 1 := by native_decide
  have hsqrt : Nat.sqrt 2 = 1 := by native_decide
  rw [hlog, hsqrt]
  -- Step 2: Let q = restrictPoly ρ* p
  set ρ := universalRestriction 2
  set q := restrictPoly ρ p
  -- Step 3: q evaluated at (false, false) ≠ q evaluated at (false, true)
  -- because the restriction fixes x₀=false, so eval at (false, b) = eval ρ-extended
  -- Step 4: pderiv x₁ q ≠ 0 (characteristic 0 argument)
  -- Step 5: generators d and x₁·d are linearly independent → finrank ≥ 2
  -- Full proof requires MvPolynomial derivative computation
  sorry

end SPDPRankLower
