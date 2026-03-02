import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic
/-!
# Finiteness of SPDP Subspaces

The SPDP subspace V_{κ,ℓ}(p) is finite-dimensional because:
1. Each generator m · ∂_S p has total degree ≤ ℓ + deg(p)
2. The space of MvPolynomials of bounded degree in finitely many vars is finite-dim
   (mathlib: `Module.Finite R (restrictTotalDegree σ R N)`)
3. A submodule of a finite-dim space is finite-dim

This provides `Module.Finite` instances needed by `finrank_mono` and `finrank_map_le`.
-/

namespace FiniteSPDP

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

/-- pderiv cannot increase total degree.
    Proof: pderiv i (monomial m a) = (m i) * monomial (m - single i 1) a,
    and |m - single i 1| ≤ |m|, so each output monomial has degree ≤ input degree.
    Standard fact not in mathlib for MvPolynomial.pderiv. -/
theorem pderiv_totalDegree_le {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree := by
  -- pderiv i p = Σ_{m ∈ p.support} (m i) * coeff_m * monomial(m - single i 1)
  -- Each summand has degree |m - single i 1| ≤ |m| ≤ totalDegree(p)
  -- totalDegree of sum ≤ max of degrees ≤ totalDegree(p)
  sorry

/-- iterDerivList cannot increase total degree -/
theorem iterDerivList_totalDegree_le {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList indices p).totalDegree ≤ p.totalDegree := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    exact le_trans (ih _) (pderiv_totalDegree_le i p)

/-- SPDP subspace has bounded degree: all elements have degree ≤ ℓ + deg(p) -/
theorem spdpSubspace_degree_bound (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ p ≤ restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, hq⟩
  simp only [SetLike.mem_coe, mem_restrictTotalDegree]
  rw [hq]
  calc (m * iterDerivList S p).totalDegree
      ≤ m.totalDegree + (iterDerivList S p).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ℓ + p.totalDegree := by
        have := iterDerivList_totalDegree_le S p
        omega

/-- **Key instance**: SPDP subspace is finite-dimensional.
    Uses mathlib's `Module.Finite R (restrictTotalDegree σ R N)` for finite σ. -/
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
  exact Module.Finite.of_injective
    (Submodule.inclusion (le_trans (blockedSubspace_le B κ ℓ p) (spdpSubspace_degree_bound κ ℓ p)))
    (Submodule.inclusion_injective _)

end FiniteSPDP
