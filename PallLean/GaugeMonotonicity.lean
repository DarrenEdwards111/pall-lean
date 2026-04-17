/-
  GaugeMonotonicity.lean — rank-monotonicity sufficient conditions
  ==================================================================

  ## Context

  To discharge the axiom `exists_amplituhedron_gauge`, one must exhibit a
  ℚ-linear endomorphism `gauge` satisfying three properties, the first of
  which is **rank monotonicity**:

    rank_monotone : ∀ κ ℓ p,
      mlBlockedSpdpRank B κ ℓ (gauge p) ≤ mlBlockedSpdpRank B κ ℓ p

  Paper reference (Definition 6, Lemma 7, p vs np1.pdf lines 1117-1131):

    > "ΠΦ is the canonical block-local global projection ...
    >  Γ^B_{κ,ℓ}(ΠΦ(p)) ≤ Γ^B_{κ,ℓ}(p)."

  ## What this file provides

  1. `IsRankMonotoneGauge` predicate
  2. **Identity gauge** is rank-monotone (trivial)
  3. **Composition** of rank-monotone gauges is rank-monotone
  4. Helper lemmas: `iterDerivList_zero`, `iterDerivList_smul`

  The deeper content (Π_Φ clause-sheet/tableau-restriction construction)
  remains paper-deep.

  ## Status: ON-CHAIN, axiom-free, no sorry.
-/

import PallLean.MultilinearSPDP
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace GaugeMonotonicity

open MvPolynomial SPDP MultilinearSPDP

/-! ## Section 0: Helper lemmas -/

/-- `iterDerivList S 0 = 0`. -/
theorem iterDerivList_zero {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) : iterDerivList S (0 : MvPolynomial (Fin n) F) = 0 := by
  induction S with
  | nil => rfl
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
          (MvPolynomial.pderiv i (0 : MvPolynomial (Fin n) F)) rest =
        iterDerivList rest (MvPolynomial.pderiv i 0) from rfl]
    rw [map_zero, ih]

/-- `iterDerivList S (c • p) = c • iterDerivList S p`. -/
theorem iterDerivList_smul {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (c : F) (p : MvPolynomial (Fin n) F) :
    iterDerivList S (c • p) = c • iterDerivList S p := by
  induction S generalizing p with
  | nil => rfl
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
          (MvPolynomial.pderiv i (c • p)) rest =
        iterDerivList rest (MvPolynomial.pderiv i (c • p)) from rfl]
    rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
          (MvPolynomial.pderiv i p) rest =
        iterDerivList rest (MvPolynomial.pderiv i p) from rfl]
    rw [Derivation.map_smul, ih]

variable {N : ℕ} (B : BlockPartition N)

/-! ## Section 1: Rank-monotonicity predicate -/

/-- **Rank-monotone gauge**: a ℚ-linear endomorphism `g` on polynomials
that does not increase the SPDP rank at any (κ, ℓ) on any input. -/
def IsRankMonotoneGauge
    (g : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ),
    mlBlockedSpdpRank B κ ℓ (g p) ≤ mlBlockedSpdpRank B κ ℓ p

/-! ## Section 2: Trivial instances -/

/-- The **identity gauge** is rank-monotone. -/
theorem IsRankMonotoneGauge.id : IsRankMonotoneGauge B LinearMap.id := by
  intro κ ℓ p
  exact le_refl _

/-! ## Section 3: Composition of rank-monotone gauges -/

/-- The **composition** of two rank-monotone gauges is rank-monotone. -/
theorem IsRankMonotoneGauge.comp
    {g₁ g₂ : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ}
    (h₁ : IsRankMonotoneGauge B g₁) (h₂ : IsRankMonotoneGauge B g₂) :
    IsRankMonotoneGauge B (g₁ ∘ₗ g₂) := by
  intro κ ℓ p
  calc mlBlockedSpdpRank B κ ℓ ((g₁ ∘ₗ g₂) p)
      = mlBlockedSpdpRank B κ ℓ (g₁ (g₂ p)) := rfl
    _ ≤ mlBlockedSpdpRank B κ ℓ (g₂ p) := h₁ κ ℓ (g₂ p)
    _ ≤ mlBlockedSpdpRank B κ ℓ p := h₂ κ ℓ p

end GaugeMonotonicity
