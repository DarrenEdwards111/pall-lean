import PallLean.SPDPDefs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# IterDerivHelpers

Small helper lemmas for `SPDP.iterDerivList` intended to remove the
`foldl` / list plumbing from the final Leibniz-profile argument.

These are deliberately modest and should be reusable in the last sorry
without committing to one giant iterated-product theorem all at once.
-/

namespace IterDerivHelpers

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [CommRing F]

@[simp] theorem iterDerivList_nil (p : MvPolynomial (Fin n) F) :
    iterDerivList ([] : List (Fin n)) p = p := by
  rfl

@[simp] theorem iterDerivList_cons (i : Fin n) (S : List (Fin n))
    (p : MvPolynomial (Fin n) F) :
    iterDerivList (i :: S) p = iterDerivList S (pderiv i p) := by
  unfold iterDerivList
  simp [List.foldl]

@[simp] theorem iterDerivList_single (i : Fin n) (p : MvPolynomial (Fin n) F) :
    iterDerivList [i] p = pderiv i p := by
  simp

theorem iterDerivList_append (S T : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (S ++ T) p = iterDerivList T (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp
  | cons i rest ih =>
      simp [iterDerivList_cons, ih]

/-- If every derivative in `S` kills `f`, then `f` factors out of an iterated derivative of `f * g`. -/
theorem iterDerivList_mul_left_const
    (S : List (Fin n))
    (f g : MvPolynomial (Fin n) F)
    (hf : ∀ i ∈ S, pderiv i f = 0) :
    iterDerivList S (f * g) = f * iterDerivList S g := by
  induction S generalizing g with
  | nil => simp
  | cons i rest ih =>
      have hfi : pderiv i f = 0 := hf i (by simp)
      have hfrest : ∀ j ∈ rest, pderiv j f = 0 := by
        intro j hj
        exact hf j (by simp [hj])
      simp only [iterDerivList_cons]
      rw [pderiv_mul, hfi, zero_mul, zero_add, ih _ hfrest]

/-- Dually, if every derivative in `S` kills `g`, then `g` factors out on the right. -/
theorem iterDerivList_mul_right_const
    (S : List (Fin n))
    (f g : MvPolynomial (Fin n) F)
    (hg : ∀ i ∈ S, pderiv i g = 0) :
    iterDerivList S (f * g) = iterDerivList S f * g := by
  induction S generalizing f with
  | nil => simp
  | cons i rest ih =>
      have hgi : pderiv i g = 0 := hg i (by simp)
      have hgrest : ∀ j ∈ rest, pderiv j g = 0 := by
        intro j hj
        exact hg j (by simp [hj])
      simp only [iterDerivList_cons]
      rw [pderiv_mul, hgi, mul_zero, add_zero, ih _ hgrest]

/-- If the first derivative yields zero, then any further iterated derivatives also yield zero. -/
theorem iterDerivList_of_head_zero (i : Fin n) (S : List (Fin n))
    (p : MvPolynomial (Fin n) F)
    (h0 : pderiv i p = 0) :
    iterDerivList (i :: S) p = 0 := by
  rw [iterDerivList_cons, h0]
  exact foldl_pderiv_zero S

/-- Iterated derivative distributes over negation. -/
theorem iterDerivList_neg
    (S : List (Fin n))
    (p : MvPolynomial (Fin n) F) :
    iterDerivList S (-p) = -(iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp
  | cons i rest ih =>
      simp only [iterDerivList_cons, map_neg]
      exact ih _

/-- Iterated derivative distributes over addition. -/
theorem iterDerivList_add
    (S : List (Fin n))
    (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p + q) = iterDerivList S p + iterDerivList S q := by
  induction S generalizing p q with
  | nil => simp
  | cons i rest ih =>
      simp only [iterDerivList_cons, map_add]
      exact ih _ _

/-- Iterated derivative distributes over subtraction. -/
theorem iterDerivList_sub
    (S : List (Fin n))
    (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p - q) = iterDerivList S p - iterDerivList S q := by
  rw [sub_eq_add_neg, iterDerivList_add S p (-q), iterDerivList_neg, sub_eq_add_neg]

/-- Combined: constant factor on the left passes through negation.
    `iterDerivList S (-(f * g)) = -(f * iterDerivList S g)` when `f` is killed by all derivs. -/
theorem iterDerivList_neg_mul_left_const
    (S : List (Fin n))
    (f g : MvPolynomial (Fin n) F)
    (hf : ∀ i ∈ S, pderiv i f = 0) :
    iterDerivList S (-(f * g)) = -(f * iterDerivList S g) := by
  rw [iterDerivList_neg, iterDerivList_mul_left_const S f g hf]

end IterDerivHelpers
