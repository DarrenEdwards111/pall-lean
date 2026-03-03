/-
  SpdpDeepSorries.lean

  Formal statement objects for the 5 deep sorries from Pall (§3-12).
  Provides abstract interfaces that can be refined to concrete SPDP defs.
  Based on Darren's specification.
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic

open scoped BigOperators

namespace SpdpDeepSorries

/-! ## Minimal abstract interfaces (placeholders to refine) -/

/-- Abstract "polynomial-like" type with SPDP operations.
    Replace with actual MvPolynomial + SPDP definitions. -/
class PolyLike (P : Type*) extends CommSemiring P where
  /-- Blocked SPDP rank Γ^B_{κ,ℓ}(p) -/
  GammaB : ℕ → ℕ → P → ℕ

/-- A statement object is just a Prop. -/
abbrev Statement := Prop

/-! ## 1) Lemma 3.1 (κ-padding rank) — statement object -/

def kappa_padding_rank_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (Y V : P) : Statement :=
  (PolyLike.GammaB κ ℓ (Y * V)) ≤
    (Finset.range (κ + 1)).sum (fun r => (Nat.choose κ r) * PolyLike.GammaB r ℓ V)

/-! ## 2) Theorem 5.16 (Width⇒Rank) — statement object -/

def width_to_rank_bound_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (p : P) (G w : ℕ) : Statement :=
  PolyLike.GammaB κ ℓ p ≤ (G * w) ^ 3

/-! ## 3) Theorem 9.3 (Identity minor lower bound) — statement object -/

def identity_minor_lower_bound_stmt {P : Type*} [PolyLike P]
    (κ ℓ L : ℕ) (Qx : P) : Statement :=
  Nat.choose L κ ≤ PolyLike.GammaB κ ℓ Qx

/-! ## 4) Theorem 12.2 (Extraction rank monotone) -/

section RankMonotone

variable {F : Type*} [Field F]
variable {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
  [Module F V₁] [Module F V₂] [Module F V₃]

/-- rank(g ∘ f) ≤ rank(f) — core composition monotonicity. -/
theorem rank_comp_le_right (f : V₁ →ₗ[F] V₂) (g : V₂ →ₗ[F] V₃) :
    Module.finrank F (LinearMap.range (g.comp f)) ≤
    Module.finrank F (LinearMap.range f) := by
  apply Submodule.finrank_mono
  exact LinearMap.range_comp_le_range f g

/-- rank(g ∘ f) ≤ rank(g) — symmetric companion. -/
theorem rank_comp_le_left (f : V₁ →ₗ[F] V₂) (g : V₂ →ₗ[F] V₃) :
    Module.finrank F (LinearMap.range (g.comp f)) ≤
    Module.finrank F (LinearMap.range g) := by
  apply Submodule.finrank_mono
  exact LinearMap.range_comp_le_range₂ f g

end RankMonotone

/-- Extraction rank monotone as Γ^B statement. -/
def extraction_rank_monotone_stmt {P : Type*} [PolyLike P]
    (κ ℓ : ℕ) (Qx pMN : P) : Statement :=
  PolyLike.GammaB κ ℓ Qx ≤ PolyLike.GammaB κ ℓ pMN

/-! ## 5) Binomial bound — statement object -/

def binomial_lower_bound_stmt (n : ℕ) : Statement :=
  Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4)

end SpdpDeepSorries
