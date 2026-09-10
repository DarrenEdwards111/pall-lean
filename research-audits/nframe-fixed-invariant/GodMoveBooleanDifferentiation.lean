import GodMoveCircuitNormalization
import GodMoveMonomialMinor

/-!
# Boolean finite differences give exact derivatives of the normalized target

Ordinary differentiation does not descend to the Boolean quotient `X_i²=X_i`.
The difference between the two Boolean faces does: restrict to `X_i=1` and
`X_i=0`, normalize, and subtract. This operation is unchanged when its source
is normalized and is exactly the ordinary derivative of the normalized source.
Iterating the operation therefore gives the target's actual derivative rows.

The product rule includes an extra product of differences. These identities
repair the algebraic differentiation interface; they do not bound the dimension
of all derivative rows, the size of their joint representation, or the cost of
normal-form expansion. In particular they do not overcome the existing
small-circuit characteristic-rank obstruction.
-/

namespace GodMoveBooleanDifferentiation

open MvPolynomial MultilinearSPDP SPDP
open GodMoveBooleanInterpolation GodMoveCircuitNormalization
open scoped BigOperators

/-- Restriction to one Boolean face is a ring homomorphism on raw polynomials. -/
noncomputable def face {n : ℕ} (i : Fin n) (b : Bool) : Poly n →+* Poly n :=
  eval₂Hom C (fun j => if j = i then C (bit b) else X j)

@[simp] theorem face_C {n : ℕ} (i : Fin n) (b : Bool) (c : ℚ) :
    face i b (C c) = C c := by simp [face]

@[simp] theorem face_X {n : ℕ} (i j : Fin n) (b : Bool) :
    face i b (X j) = if j = i then C (bit b) else X j := by simp [face]

theorem eval_face {n : ℕ} (i : Fin n) (b : Bool) (p : Poly n)
    (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (face i b p) =
      MvPolynomial.eval (booleanPoint (Function.update a i b)) p := by
  have hh : (MvPolynomial.eval (booleanPoint a)).comp (face i b) =
      MvPolynomial.eval (booleanPoint (Function.update a i b)) := by
    ext c
    · simp
    · by_cases hc : c = i <;> simp [face, booleanPoint, hc]
  exact RingHom.congr_fun hh p

theorem normalize_sub {n : ℕ} (p q : Poly n) :
    normalize (p - q) = normalize p - normalize q :=
  (normalizeLinearMap n).map_sub p q

theorem normalize_of_isMultilinear {n : ℕ} (p : Poly n) (hp : IsMultilinear p) :
    normalize p = p := by
  apply multilinear_eq_of_boolean_eval _ _ (normalize_isMultilinear p) hp
  exact eval_normalize p

theorem normalize_idempotent {n : ℕ} (p : Poly n) :
    normalize (normalize p) = normalize p :=
  normalize_of_isMultilinear _ (normalize_isMultilinear p)

/-- Boolean restriction respects equality in the coefficient-normalized algebra. -/
theorem normalize_face_normalize {n : ℕ} (i : Fin n) (b : Bool) (p : Poly n) :
    normalize (face i b (normalize p)) = normalize (face i b p) := by
  apply multilinear_eq_of_boolean_eval _ _ (normalize_isMultilinear _)
    (normalize_isMultilinear _)
  intro a
  rw [eval_normalize, eval_normalize, eval_face, eval_face, eval_normalize]

/-- Finite difference in the Boolean quotient, represented by a multilinear polynomial. -/
noncomputable def booleanDifference {n : ℕ} (i : Fin n) (p : Poly n) : Poly n :=
  normalize (face i true p) - normalize (face i false p)

theorem booleanDifference_eq_normalize_sub {n : ℕ} (i : Fin n) (p : Poly n) :
    booleanDifference i p = normalize (face i true p - face i false p) :=
  (normalize_sub _ _).symm

theorem booleanDifference_isMultilinear {n : ℕ} (i : Fin n) (p : Poly n) :
    IsMultilinear (booleanDifference i p) := by
  rw [booleanDifference_eq_normalize_sub]
  exact normalize_isMultilinear _

theorem booleanDifference_normalize {n : ℕ} (i : Fin n) (p : Poly n) :
    booleanDifference i (normalize p) = booleanDifference i p := by
  simp only [booleanDifference, normalize_face_normalize]

theorem eval_booleanDifference {n : ℕ} (i : Fin n) (p : Poly n) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (booleanDifference i p) =
      MvPolynomial.eval (booleanPoint (Function.update a i true)) p -
        MvPolynomial.eval (booleanPoint (Function.update a i false)) p := by
  simp only [booleanDifference, map_sub, eval_normalize, eval_face]

private theorem face_product_of_not_mem {n : ℕ} (i : Fin n) (b : Bool)
    (s : Finset (Fin n)) (hi : i ∉ s) :
    face i b (∏ j ∈ s, (X j : Poly n)) = ∏ j ∈ s, (X j : Poly n) := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [hji]

private theorem pderiv_product_of_not_mem {n : ℕ} (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∉ s) :
    pderiv i (∏ j ∈ s, (X j : Poly n)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      have hji : j ≠ i := fun h => hi (h ▸ Finset.mem_insert_self j s)
      have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert hj, pderiv_mul, pderiv_X_of_ne hji,
        ih his]
      simp

private theorem derivative_product_eq_face_difference {n : ℕ} (i : Fin n)
    (s : Finset (Fin n)) :
    pderiv i (∏ j ∈ s, (X j : Poly n)) =
      face i true (∏ j ∈ s, (X j : Poly n)) -
        face i false (∏ j ∈ s, (X j : Poly n)) := by
  by_cases hi : i ∈ s
  · rw [GodMoveMonomialMinor.pderiv_prod_X s i hi,
      ← Finset.mul_prod_erase s (fun j => (X j : Poly n)) hi]
    simp only [map_mul, face_X,
      face_product_of_not_mem i true (s.erase i) (Finset.notMem_erase i s),
      face_product_of_not_mem i false (s.erase i) (Finset.notMem_erase i s)]
    simp [bit]
  · rw [pderiv_product_of_not_mem i s hi,
      face_product_of_not_mem i true s hi, face_product_of_not_mem i false s hi,
      sub_self]

private theorem normalize_monomial_eq_product {n : ℕ} (α : Fin n →₀ ℕ) (c : ℚ) :
    normalize (monomial α c) = C c * ∏ j ∈ α.support, (X j : Poly n) := by
  rw [normalize_monomial, SymmetricPower.tagMonomial, monomial_sum_index]
  rfl

/-- For a normalized polynomial the finite difference is its ordinary derivative. -/
theorem pderiv_normalize_eq_face_difference {n : ℕ} (i : Fin n) (p : Poly n) :
    pderiv i (normalize p) =
      face i true (normalize p) - face i false (normalize p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [normalize_monomial_eq_product, pderiv_mul, pderiv_C, zero_mul, zero_add,
        derivative_product_eq_face_difference, map_mul, map_mul, face_C, face_C, mul_sub]
  | add p q hp hq =>
      rw [normalize_add, map_add, hp, hq, map_add, map_add]
      ring

/-- The exact repaired differentiation bridge, without an assumed transport law. -/
theorem booleanDifference_eq_pderiv_normalize {n : ℕ} (i : Fin n) (p : Poly n) :
    booleanDifference i p = pderiv i (normalize p) := by
  rw [← booleanDifference_normalize i p, booleanDifference_eq_normalize_sub,
    ← pderiv_normalize_eq_face_difference]
  exact normalize_of_isMultilinear _
    (isMultilinear_pderiv _ (normalize_isMultilinear p) i)

/-- Iterated finite differences, with the same order convention as `iterDerivList`. -/
noncomputable def iterBooleanDifference {n : ℕ} (S : List (Fin n)) (p : Poly n) : Poly n :=
  S.foldl (fun q i => booleanDifference i q) (normalize p)

theorem iterBooleanDifference_eq_iterDerivList {n : ℕ}
    (S : List (Fin n)) (p : Poly n) :
    iterBooleanDifference S p = iterDerivList S (normalize p) := by
  have aux (q : Poly n) (hq : IsMultilinear q) :
      S.foldl (fun r i => booleanDifference i r) q = iterDerivList S q := by
    induction S generalizing q with
    | nil => rfl
    | cons i is ih =>
        change is.foldl (fun r j => booleanDifference j r) (booleanDifference i q) =
          iterDerivList is (pderiv i q)
        rw [booleanDifference_eq_pderiv_normalize i q, normalize_of_isMultilinear q hq]
        exact ih _ (isMultilinear_pderiv q hq i)
  exact aux _ (normalize_isMultilinear p)

/-- Shifting and applying the repository's actual coefficient projection now
gives exactly the target row, since differentiation was repaired first. -/
theorem iterBooleanDifference_row_eq {n : ℕ}
    (S : List (Fin n)) (p shift : Poly n) :
    mlProj (shift * iterBooleanDifference S p) =
      mlProj (shift * iterDerivList S (normalize p)) := by
  rw [iterBooleanDifference_eq_iterDerivList]

/-- Quotient product rule. The extra product of differences is necessary for
the Boolean quotient; the outside normalization is part of the identity. -/
theorem booleanDifference_mul {n : ℕ} (i : Fin n) (p q : Poly n) :
    booleanDifference i (p * q) =
      normalize (face i false p * booleanDifference i q +
        face i false q * booleanDifference i p +
        booleanDifference i p * booleanDifference i q) := by
  apply multilinear_eq_of_boolean_eval _ _ (booleanDifference_isMultilinear _ _)
    (normalize_isMultilinear _)
  intro a
  simp only [eval_booleanDifference, eval_normalize, map_add, map_mul, eval_face]
  ring

/-- Raw finite difference uses only two substitutions and one subtraction.
Its mathematical polynomial denotation is not an expanded-coefficient cost claim. -/
noncomputable def finiteDifference {n : ℕ} (i : Fin n) (p : Poly n) : Poly n :=
  face i true p - face i false p

theorem normalize_finiteDifference {n : ℕ} (i : Fin n) (p : Poly n) :
    normalize (finiteDifference i p) = booleanDifference i p :=
  normalize_sub _ _

/-- The raw iteration postpones Boolean normalization until the final result. -/
noncomputable def iterFiniteDifference {n : ℕ} (S : List (Fin n)) (p : Poly n) : Poly n :=
  S.foldl (fun q i => finiteDifference i q) p

/-- Exact derivative recovery after one final normalization, including the empty list. -/
theorem normalize_iterFiniteDifference {n : ℕ} (S : List (Fin n)) (p : Poly n) :
    normalize (iterFiniteDifference S p) = iterDerivList S (normalize p) := by
  induction S generalizing p with
  | nil => rfl
  | cons i is ih =>
      change normalize (iterFiniteDifference is (finiteDifference i p)) =
        iterDerivList is (pderiv i (normalize p))
      rw [ih, normalize_finiteDifference, booleanDifference_eq_pderiv_normalize]

/-- This preserves the actual row convention: normalize the derivative before
multiplying by the shift and applying `mlProj`, not after the whole row. -/
theorem finiteDifference_row_eq {n : ℕ}
    (S : List (Fin n)) (p shift : Poly n) :
    mlProj (shift * normalize (iterFiniteDifference S p)) =
      mlProj (shift * iterDerivList S (normalize p)) := by
  rw [normalize_iterFiniteDifference]

end GodMoveBooleanDifferentiation

#print axioms GodMoveBooleanDifferentiation.eval_face
#print axioms GodMoveBooleanDifferentiation.normalize_face_normalize
#print axioms GodMoveBooleanDifferentiation.booleanDifference_normalize
#print axioms GodMoveBooleanDifferentiation.pderiv_normalize_eq_face_difference
#print axioms GodMoveBooleanDifferentiation.booleanDifference_eq_pderiv_normalize
#print axioms GodMoveBooleanDifferentiation.iterBooleanDifference_eq_iterDerivList
#print axioms GodMoveBooleanDifferentiation.iterBooleanDifference_row_eq
#print axioms GodMoveBooleanDifferentiation.booleanDifference_mul
#print axioms GodMoveBooleanDifferentiation.normalize_iterFiniteDifference
#print axioms GodMoveBooleanDifferentiation.finiteDifference_row_eq
