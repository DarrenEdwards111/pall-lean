import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import PallLean.SPDPDefs
/-!
# Product Derivative for Independent Factors

Key lemma for identity minor construction (Theorem 9.3):
For a product of factors each linear in a distinct variable z_C,
the iterated derivative ∂_{z_S} pulls out the factors for C ∈ S.

∂_{z_C}(1 - z_C · V_C) = -V_C  (when z_C appears only in this factor)

∂_{z_S}(∏_C (1 - z_C · V_C)) = (-1)^|S| · ∏_{C∈S} V_C · ∏_{C∉S} (1 - z_C · V_C)

This is the Leibniz rule for multilinear products in disjoint variables.
-/

namespace ProductDeriv

open MvPolynomial SPDP

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- pderiv of (1 - X_i * p) with respect to i, when p doesn't involve i -/
theorem pderiv_one_sub_mul {i : σ} {p : MvPolynomial σ F}
    (hp : i ∉ p.vars) :
    pderiv i (1 - X i * p) = -p := by
  classical
  have h1 : pderiv i (1 : MvPolynomial σ F) = 0 := pderiv_one
  have h2 : pderiv i (X i * p) = 1 * p + X i * 0 := by
    rw [pderiv_mul]
    congr 1
    · rw [pderiv_X]; simp [Pi.single_eq_same]
    · rw [pderiv_eq_zero_of_notMem_vars hp]
  simp only [map_sub, h1, h2, one_mul, mul_zero, add_zero, zero_sub]

/-- pderiv of (1 - X_j * p) with respect to i ≠ j, when i ∉ p.vars -/
theorem pderiv_one_sub_mul_ne {i j : σ} {p : MvPolynomial σ F}
    (hij : i ≠ j) (hp : i ∉ p.vars) :
    pderiv i (1 - X j * p) = 0 := by
  rw [map_sub, pderiv_one, pderiv_mul, pderiv_X_of_ne hij.symm, zero_mul, zero_add,
      pderiv_eq_zero_of_notMem_vars hp, mul_zero, zero_sub, neg_zero]

/-- For a product of two factors where pderiv i kills the second factor,
    pderiv i (f * g) = (pderiv i f) * g -/
theorem pderiv_mul_right_const {i : σ} {f g : MvPolynomial σ F}
    (hg : pderiv i g = 0) :
    pderiv i (f * g) = pderiv i f * g := by
  rw [pderiv_mul, hg, mul_zero, add_zero]

/-- For a product of two factors where pderiv i kills the first factor,
    pderiv i (f * g) = f * (pderiv i g) -/
theorem pderiv_mul_left_const {i : σ} {f g : MvPolynomial σ F}
    (hf : pderiv i f = 0) :
    pderiv i (f * g) = f * pderiv i g := by
  rw [pderiv_mul, hf, zero_mul, zero_add]

/-- pderiv of a product over a finset, where the variable appears in exactly one factor.

    ∂_i (∏_{j ∈ s} f j) = (∂_i (f k)) * ∏_{j ∈ s, j ≠ k} f j

    when ∂_i (f j) = 0 for all j ≠ k. -/
theorem pderiv_prod_single {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → MvPolynomial σ F} {i : σ} {k : ι} (hk : k ∈ s)
    (hother : ∀ j ∈ s, j ≠ k → pderiv i (f j) = 0) :
    pderiv i (s.prod f) = pderiv i (f k) * (s.erase k).prod f := by
  -- Auxiliary: pderiv i of a product where every factor has zero derivative
  have hprod_zero : ∀ t : Finset ι, (∀ j ∈ t, pderiv i (f j) = 0) →
      pderiv i (t.prod f) = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => intros; rw [Finset.prod_empty]; exact pderiv_one
    | insert a t' hat ih =>
      intro ht
      rw [Finset.prod_insert hat, pderiv_mul,
          ht a (Finset.mem_insert_self a t'),
          ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))]
      simp
  -- pderiv of the erased-k product is 0 since every remaining factor satisfies hother
  have h0 : pderiv i ((s.erase k).prod f) = 0 :=
    hprod_zero _ (fun j hj =>
      hother j (Finset.mem_of_mem_erase hj) ((Finset.mem_erase.mp hj).1))
  -- Decompose s.prod f = f k * (s.erase k).prod f via mul_prod_erase, then Leibniz rule
  rw [← Finset.mul_prod_erase _ _ hk, pderiv_mul, h0, mul_zero, add_zero]

-- The full iterated Leibniz product lemma is infrastructure for profile compression.
-- For the SPDP rank bound, we use this indirectly.

end ProductDeriv
