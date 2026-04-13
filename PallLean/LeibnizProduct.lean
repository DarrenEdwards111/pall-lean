import PallLean.ProductDeriv
import PallLean.IterDerivHelpers
import Mathlib.Tactic

/-!
# Lemma 1: Single-step Leibniz for finite products

For a Finset product `∏_{i ∈ s} f i`, the derivative w.r.t. variable v is:

  ∂_v (∏_{i ∈ s} f i) = Σ_{k ∈ s} (∂_v (f k)) × ∏_{j ∈ s, j ≠ k} f j

This is the standard Leibniz product rule generalized to finite products.
-/

namespace LeibnizProduct

open MvPolynomial SPDP

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- Leibniz rule for the derivative of a Finset product:
  ∂_v (∏_{i ∈ s} f i) = Σ_{k ∈ s} (∂_v (f k)) × ∏_{j ∈ s \ {k}} f j -/
theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial σ F) (v : σ) :
    pderiv v (s.prod f) =
      s.sum (fun k => pderiv v (f k) * (s.erase k).prod f) := by
  induction s using Finset.induction_on with
  | empty => simp [pderiv_one]
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, pderiv_mul, ih]
    rw [Finset.sum_insert hat]
    congr 1
    · -- The a-term: ∂_v(f a) * (insert a t \ {a}).prod f = ∂_v(f a) * t.prod f
      congr 1
      rw [Finset.erase_insert hat]
    · -- The remaining terms: f a * Σ_{k∈t} ... + Σ_{k∈t} ∂_v(f k) * ...
      -- Need: f a * (Σ_{k∈t} ∂_v(f k) * (t.erase k).prod f)
      --      = Σ_{k∈t} ∂_v(f k) * ((insert a t).erase k).prod f
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_assoc, mul_comm (f a) _, mul_assoc]
      congr 1
      -- (insert a t).erase k = insert a (t.erase k) since k ≠ a and a ∉ t
      have hka : k ≠ a := fun h => hat (h ▸ hk)
      rw [Finset.erase_insert_of_ne hka.symm, Finset.prod_insert]
      exact fun h => hat (Finset.mem_of_mem_erase h)

end LeibnizProduct
