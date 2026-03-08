/-
  LeibnizProduct.lean — Leibniz rule for MvPolynomial.pderiv on Finset.prod

  Key result:
  - pderiv_finset_prod: ∂_i(∏_{c∈S} f_c) = Σ_{c∈S} (∂_i f_c) · ∏_{c'∈S\{c}} f_{c'}
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace LeibnizProduct

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

/-- Leibniz rule: ∂_i(∏_{c∈S} f_c) = Σ_{c∈S} (∂_i f_c) · ∏_{c'∈S\{c}} f_{c'}
    Proof by induction on the finset using pderiv_mul (Derivation.leibniz). -/
theorem pderiv_finset_prod {ι : Type*} [DecidableEq ι]
    (i : σ) (f : ι → MvPolynomial σ F) (S : Finset ι) :
    pderiv i (S.prod f) =
    S.sum (fun c => pderiv i (f c) * (S.erase c).prod f) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S' hna ih =>
    rw [Finset.prod_insert hna]
    -- pderiv i (f a * ∏ S') = pderiv i (f a) * ∏ S' + f a * pderiv i (∏ S')
    rw [pderiv_mul]
    rw [ih]
    rw [Finset.sum_insert hna]
    congr 1
    · -- a-term: erase a from (insert a S') = S'
      congr 1; rw [Finset.erase_insert hna]
    · -- remaining: f a * Σ_{c∈S'} ∂(f c) * ∏(S'\c) = Σ_{c∈S'} ∂(f c) * ∏((a∪S')\c)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [← mul_assoc, mul_comm (f a) _, mul_assoc]
      congr 1
      have hac : a ≠ c := fun h => hna (h ▸ hc)
      rw [show (Insert.insert a S').erase c = Insert.insert a (S'.erase c) from
        Finset.erase_insert_of_ne hac]
      rw [Finset.prod_insert (fun h => hna (Finset.mem_of_mem_erase h))]

end LeibnizProduct
