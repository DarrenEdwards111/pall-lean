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

/-- Tsub for Finsupp decreases the sum: (m - n).sum id ≤ m.sum id -/
private theorem finsupp_tsub_sum_le {σ : Type*} [DecidableEq σ]
    (m n : σ →₀ ℕ) :
    (m - n).sum (fun _ e => e) ≤ m.sum (fun _ e => e) := by
  -- (m - n) i ≤ m i for all i (natural subtraction)
  -- Use Finsupp.sum_le_sum_index with m - n ≤ m
  have h : m - n ≤ m := fun i => Nat.sub_le (m i) (n i)
  exact Finsupp.sum_le_sum_index h
    (fun _ _ => monotone_id)
    (fun _ _ => rfl)

theorem pderiv_totalDegree_le {F : Type*} [CommRing F]
    (i : Fin n) (p : MvPolynomial (Fin n) F) :
    (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, pderiv_monomial]
  apply le_trans (totalDegree_finset_sum _ _)
  apply Finset.sup_le
  intro m hm
  apply le_trans (totalDegree_monomial_le _ _)
  apply le_trans (finsupp_tsub_sum_le m (Finsupp.single i 1))
  exact Finset.le_sup (f := fun s => Finsupp.sum s fun _ e => e) hm

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
