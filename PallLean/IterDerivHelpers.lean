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

/-- Partial derivatives of `MvPolynomial` commute: `pderiv i (pderiv j f) = pderiv j (pderiv i f)`.
    Proved by the monomial induction: for monomials it's a direct computation; for sums it
    follows from linearity. -/
theorem pderiv_comm (i j : Fin n) (f : MvPolynomial (Fin n) F) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    -- LHS: pderiv i (monomial (s - single j 1) (a * s j))
    --    = monomial ((s - single j 1) - single i 1) ((a * s j) * (s - single j 1) i)
    -- RHS: pderiv j (monomial (s - single i 1) (a * s i))
    --    = monomial ((s - single i 1) - single j 1) ((a * s i) * (s - single i 1) j)
    -- These are equal because:
    -- 1. (s - single j 1) - single i 1 = (s - single i 1) - single j 1
    -- 2. (a * s j) * (s - single j 1) i = (a * s i) * (s - single i 1) j
    -- After pderiv_monomial twice, we need to show:
    -- monomial ((s - single j 1) - single i 1) ((a * ↑(s j)) * ↑((s - single j 1) i))
    -- = monomial ((s - single i 1) - single j 1) ((a * ↑(s i)) * ↑((s - single i 1) j))
    change MvPolynomial.monomial _ _ = MvPolynomial.monomial _ _
    -- We use the fact that pderiv i (pderiv j (monomial s a)) computes to
    -- monomial ((s - single j 1) - single i 1) ((a * s j) * (s - single j 1) i)
    -- and similarly with i,j swapped.
    -- Both the exponent and coefficient are symmetric in i,j at the ℕ level.
    have key : ∀ (x y : Fin n),
        (s - Finsupp.single x 1 - Finsupp.single y 1 : Fin n →₀ ℕ)
        = (s - Finsupp.single y 1 - Finsupp.single x 1 : Fin n →₀ ℕ) := by
      intro x y
      ext k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h1 h2
      · subst h1; subst h2; omega
      · omega
      · omega
      · rfl
    rw [key j i]
    congr 1
    -- Coefficient: (a * s j) * (s - single j 1) i = (a * s i) * (s - single i 1) j
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hij : j = i
    · subst hij; ring
    · have hij' : ¬(i = j) := Ne.symm hij
      simp only [hij, hij', ↓reduceIte, Nat.sub_zero]
      ring
  | add p q hp hq =>
    simp only [map_add, hp, hq]

/-- If `v ∉ f.vars`, then `v ∉ (pderiv w f).vars`.
    Equivalently: `pderiv v (pderiv w f) = 0` when `pderiv v f = 0`.
    This follows from pderiv commutativity. -/
theorem pderiv_eq_zero_of_pderiv_eq_zero
    (v w : Fin n) (f : MvPolynomial (Fin n) F)
    (hf : pderiv v f = 0) :
    pderiv v (pderiv w f) = 0 := by
  rw [pderiv_comm v w f, hf, map_zero]

/-- If `v ∈ S` and `pderiv v p = 0`, then `iterDerivList S p = 0`.
    The proof uses pderiv commutativity to "move" the killing variable to the front. -/
theorem iterDerivList_eq_zero_of_mem_and_pderiv_zero
    (S : List (Fin n)) (v : Fin n) (p : MvPolynomial (Fin n) F)
    (hv : v ∈ S) (hp : pderiv v p = 0) :
    iterDerivList S p = 0 := by
  induction S generalizing p with
  | nil => simp at hv
  | cons a rest ih =>
    simp only [iterDerivList_cons]
    rcases List.mem_cons.mp hv with ha | hrest
    · -- v = a, so pderiv a p = pderiv v p = 0
      subst ha
      rw [hp]
      exact foldl_pderiv_zero rest
    · -- v ∈ rest
      exact ih (pderiv a p) hrest (pderiv_eq_zero_of_pderiv_eq_zero v a p hp)

/-- If `v ∈ S` and `v ∉ p.vars`, then `iterDerivList S p = 0`.
    Combines `pderiv_eq_zero_of_notMem_vars` with the general killing lemma. -/
theorem iterDerivList_eq_zero_of_mem_notMem_vars
    (S : List (Fin n)) (v : Fin n) (p : MvPolynomial (Fin n) F)
    (hv : v ∈ S) (hvp : v ∉ p.vars) :
    iterDerivList S p = 0 :=
  iterDerivList_eq_zero_of_mem_and_pderiv_zero S v p hv
    (MvPolynomial.pderiv_eq_zero_of_notMem_vars hvp)

/-- Swapping two adjacent elements in the derivative list does not change the result.
    This follows directly from `pderiv_comm`. -/
theorem iterDerivList_swap (i j : Fin n) (S : List (Fin n))
    (p : MvPolynomial (Fin n) F) :
    iterDerivList (i :: j :: S) p = iterDerivList (j :: i :: S) p := by
  simp only [iterDerivList_cons]
  congr 1
  exact pderiv_comm j i p

/-- `iterDerivList` is invariant under permutation of the derivative list.
    This is a consequence of the commutativity of partial derivatives. -/
theorem iterDerivList_perm {S T : List (Fin n)}
    (h : S.Perm T) (p : MvPolynomial (Fin n) F) :
    iterDerivList S p = iterDerivList T p := by
  induction h generalizing p with
  | nil => rfl
  | cons x _ ih => simp only [iterDerivList_cons]; exact ih (pderiv x p)
  | swap x y rest =>
    simp only [iterDerivList_cons]
    congr 1
    exact pderiv_comm x y p
  | trans _ _ ih1 ih2 => exact (ih1 p).trans (ih2 p)

end IterDerivHelpers
