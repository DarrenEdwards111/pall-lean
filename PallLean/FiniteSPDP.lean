import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# Finiteness of SPDP Subspaces

The SPDP subspace V_{κ,ℓ}(p) is finite-dimensional because:
1. Each generator m · ∂_S p has total degree ≤ ℓ + deg(p)
2. The space of MvPolynomials of bounded degree in finitely many vars is finite-dim
3. A submodule of a finite-dim space is finite-dim

This provides `Module.Finite` instances needed by `finrank_mono` and `finrank_map_le`.
-/

namespace FiniteSPDP

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

/-- The submodule of MvPolynomials of total degree ≤ d is finite-dimensional.
    This is because the monomials of degree ≤ d in n variables form a finite basis. -/
noncomputable def degreeLeSubmodule (d : ℕ) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F { p | p.totalDegree ≤ d }

/-- The degree-bounded submodule is finite (has a finite generating set) -/
instance degreeLe_finite (d : ℕ) :
    Module.Finite F (degreeLeSubmodule (n := n) (F := F) d) := by
  -- The monomials X^α with |α| ≤ d form a finite spanning set.
  -- There are finitely many such α (bounded multisets from Fin n).
  -- This is a standard fact but requires explicit construction.
  sorry

/-- iterDerivList cannot increase total degree -/
theorem iterDerivList_totalDegree_le {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList indices p).totalDegree ≤ p.totalDegree := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    calc (iterDerivList rest (pderiv i p)).totalDegree
        ≤ (pderiv i p).totalDegree := ih _
      _ ≤ p.totalDegree := by
          -- pderiv i p has total degree ≤ totalDegree(p):
          -- each monomial c_m * x^m in p contributes (m_i) * c_m * x^{m-e_i}
          -- with degree |m|-1 ≤ totalDegree(p)-1 ≤ totalDegree(p)
          sorry

/-- SPDP subspace has bounded degree: all elements have degree ≤ ℓ + deg(p) -/
theorem spdpSubspace_degree_bound (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ p ≤ degreeLeSubmodule (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, hq⟩
  apply Submodule.subset_span
  rw [hq]
  calc (m * iterDerivList S p).totalDegree
      ≤ m.totalDegree + (iterDerivList S p).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ℓ + p.totalDegree := by
        have := iterDerivList_totalDegree_le S p
        omega

/-- **Key instance**: SPDP subspace is finite-dimensional -/
instance spdpSubspace_finite (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F (spdpSubspace (F := F) κ ℓ p) := by
  have h := spdpSubspace_degree_bound κ ℓ p
  exact Module.Finite.of_injective
    (Submodule.inclusion h)
    (Submodule.inclusion_injective h)

/-- blocked SPDP subspace is also finite -/
instance blockedSpdpSubspace_finite (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    Module.Finite F (blockedSpdpSubspace (F := F) B κ ℓ p) := by
  have h := blockedSubspace_le B κ ℓ p
  have : spdpSubspace κ ℓ p ≤ degreeLeSubmodule (ℓ + p.totalDegree) :=
    spdpSubspace_degree_bound κ ℓ p
  exact Module.Finite.of_injective
    (Submodule.inclusion (le_trans h this))
    (Submodule.inclusion_injective _)

end FiniteSPDP
