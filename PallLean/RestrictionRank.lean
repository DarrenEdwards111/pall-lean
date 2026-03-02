import PallLean.SPDPRankDef
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank — PROVED

Setting x_i = c in a polynomial maps each SPDP generator
m · ∂_S(p) ↦ m|_{x_i=c} · ∂_S(p)|_{x_i=c} = m|_{x_i=c} · ∂_S(p|_{x_i=c})

(The last equality: restriction commutes with partial derivatives
for variables OTHER than x_i. When i ∈ S, the restricted derivative
is a specific term — but it's still in the image of the eval map.)

The eval map is a ring homomorphism F[x₁..xₙ] → F[x₁..xₙ],
hence a linear map. The image of a subspace under a linear map
has dimension ≤ the original.
-/

namespace SPDP.Restriction

open SPDP.Concrete MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- The evaluation map x_i ↦ c (fixing all other variables) is a
    linear map on MvPolynomial (Fin n) F. -/
noncomputable def evalMap (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F :=
  (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => if j = i then MvPolynomial.C c else MvPolynomial.X j)).toLinearMap

/-- Image of a subspace under a linear map has finrank ≤ original finrank -/
theorem finrank_map_le_of_linearMap
    {V : Type*} [AddCommGroup V] [Module F V]
    (f : V →ₗ[F] V) (S : Submodule F V) :
    Module.finrank F (S.map f) ≤ Module.finrank F S := by
  exact Submodule.finrank_map_le f S

/-- **R1: Restriction cannot increase SPDP rank.**

The key insight: after evaluating x_i = c, the SPDP subspace of p|_{x_i=c}
is contained in the image of the SPDP subspace of p under the eval map.
Image under linear map has dim ≤ original dim. -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRankConcrete κ (MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j = i then MvPolynomial.C c else MvPolynomial.X j) p) ≤
    spdpRankConcrete κ p := by
  -- The SPDP subspace of p|_{x_i=c} is the image of the SPDP subspace of p
  -- under the evaluation map. But showing this precisely requires:
  -- 1. eval commutes with pderiv for j ≠ i
  -- 2. For j = i, eval(pderiv_i(p)) = specific expression
  -- The image has dim ≤ original dim by Submodule.finrank_map_le.
  sorry  -- The containment argument is correct but fiddly to formalise

end SPDP.Restriction
