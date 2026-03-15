/-
  Multilinearize.lean — Multilinear interpolation for Boolean functions

  Key theorem: every polynomial has a multilinear equivalent on Boolean inputs.
  Used to prove depth4_simulation at n = 4.
-/
import PallLean.BoolEval
import PallLean.PaperAxioms

namespace Multilinearize

open MvPolynomial BoolEval PaperAxioms

/-- Indicator polynomial for Boolean input a:
    evaluates to 1 at x = a and 0 at any other Boolean input. -/
noncomputable def boolIndicator {n : ℕ} (a : Fin n → Bool) :
    MvPolynomial (Fin n) ℚ :=
  ∏ i : Fin n, if a i then X i else (1 - X i)

/-- Helper: boolToRat b gives 0 or 1. -/
lemma boolToRat_cases (b : Bool) : boolToRat b = 0 ∨ boolToRat b = 1 := by
  cases b <;> simp [boolToRat]

/-- The indicator evaluates to 1 at x = a and 0 otherwise. -/
theorem eval_boolIndicator {n : ℕ} (a x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToRat (x i)) (boolIndicator a) =
    if a = x then 1 else 0 := by
  unfold boolIndicator
  simp only [map_prod]
  split
  · -- a = x: each factor evaluates to 1
    case isTrue h =>
    subst h
    apply Finset.prod_eq_one
    intro i _
    simp only [apply_ite (eval _), eval_X, map_sub, map_one]
    cases a i <;> simp [boolToRat]
  · -- a ≠ x: some factor evaluates to 0, killing the product
    case isFalse h =>
    have ⟨i, hi⟩ : ∃ i, a i ≠ x i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases ha : a i <;> cases hx : x i <;>
      simp_all [boolToRat, eval_X, map_sub, map_one]

/-- Multilinear interpolation: construct a multilinear polynomial
    with the same Boolean function as p.
    q = ∑_a evalBool(p, a) · indicator(a) -/
noncomputable def multilinearInterp {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ :=
  ∑ a : Fin n → Bool, C (evalBool p a) * boolIndicator a

/-- The interpolation preserves Boolean evaluation. -/
theorem multilinearInterp_evalBool {n : ℕ} (p : MvPolynomial (Fin n) ℚ)
    (x : Fin n → Bool) :
    evalBool (multilinearInterp p) x = evalBool p x := by
  unfold evalBool multilinearInterp
  simp only [map_sum, map_mul, eval_C, eval_boolIndicator]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ, evalBool]

/-- degreeOf i for each factor of boolIndicator ≤ 1 -/
private lemma degreeOf_indicator_factor (a : Fin n → Bool) (i j : Fin n) :
    MvPolynomial.degreeOf i (if a j then X j else (1 : MvPolynomial (Fin n) ℚ) - X j) ≤
      if i = j then 1 else 0 := by
  cases haj : a j <;> simp only [haj, ite_false, ite_true, Bool.false_eq_true, ↓reduceIte]
  · -- a j = false: factor = 1 - X j
    calc degreeOf i ((1 : MvPolynomial (Fin n) ℚ) - X j)
          ≤ max (degreeOf i 1) (degreeOf i (X j)) := degreeOf_sub_le i 1 (X j)
        _ = max 0 (if i = j then 1 else 0) := by rw [degreeOf_one, degreeOf_X]
        _ ≤ _ := by split_ifs <;> omega
  · -- a j = true: factor = X j
    rw [degreeOf_X]

/-- degreeOf i (boolIndicator a) ≤ 1 -/
private lemma degreeOf_boolIndicator_le (a : Fin n → Bool) (i : Fin n) :
    MvPolynomial.degreeOf i (boolIndicator a) ≤ 1 := by
  unfold boolIndicator
  calc degreeOf i (∏ j : Fin n, _) ≤ ∑ j : Fin n, degreeOf i
        (if a j then X j else 1 - X j) := degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, if i = j then 1 else 0 :=
        Finset.sum_le_sum (fun j _ => degreeOf_indicator_factor a i j)
    _ = 1 := by simp [Finset.sum_ite_eq']

/-- Each boolIndicator is multilinear (exponents ≤ 1).
    Key: it's a product of linear factors in distinct variables. -/
theorem boolIndicator_isMultilinear {n : ℕ} (a : Fin n → Bool) :
    IsMultilinear (boolIndicator a) := by
  intro m hm i
  exact le_trans (monomial_le_degreeOf i hm) (degreeOf_boolIndicator_le a i)

/-- The multilinear interpolation is multilinear. -/
theorem multilinearInterp_isMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    IsMultilinear (multilinearInterp p) := by
  intro m hm i
  have hle : degreeOf i (multilinearInterp p) ≤ 1 := by
    unfold multilinearInterp
    calc degreeOf i (∑ a : Fin n → Bool, C (evalBool p a) * boolIndicator a)
        ≤ (Finset.univ.sup fun a => degreeOf i (C (evalBool p a) * boolIndicator a)) :=
          degreeOf_sum_le i _ _
      _ ≤ 1 := Finset.sup_le (fun a _ =>
          calc degreeOf i (C (evalBool p a) * boolIndicator a)
              ≤ degreeOf i (C (evalBool p a)) + degreeOf i (boolIndicator a) :=
                degreeOf_mul_le i _ _
            _ ≤ 0 + 1 := Nat.add_le_add (by simp [degreeOf_C]) (degreeOf_boolIndicator_le a i)
            _ = 1 := by simp)
  exact le_trans (monomial_le_degreeOf i hm) hle

/-- totalDegree of each factor ≤ 1 -/
private lemma totalDegree_indicator_factor_le (a : Fin n → Bool) (j : Fin n) :
    (if a j then X j else (1 : MvPolynomial (Fin n) ℚ) - X j).totalDegree ≤ 1 := by
  cases haj : a j <;> simp only [haj, Bool.false_eq_true, ↓reduceIte]
  · calc ((1 : MvPolynomial (Fin n) ℚ) - X j).totalDegree
        ≤ max (1 : MvPolynomial (Fin n) ℚ).totalDegree (X j).totalDegree :=
          totalDegree_sub _ _
      _ = max 0 1 := by rw [totalDegree_one, totalDegree_X]
      _ = 1 := by omega
  · rw [totalDegree_X]

/-- totalDegree of boolIndicator ≤ n -/
private lemma totalDegree_boolIndicator_le (a : Fin n → Bool) :
    (boolIndicator a).totalDegree ≤ n := by
  unfold boolIndicator
  calc totalDegree (∏ i : Fin n, if a i then X i else 1 - X i)
      ≤ ∑ i : Fin n, totalDegree (if a i then X i else 1 - X i) :=
        totalDegree_finset_prod _ _
    _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum (fun j _ => totalDegree_indicator_factor_le a j)
    _ = n := by simp

/-- The multilinear interpolation has degree ≤ n. -/
theorem multilinearInterp_totalDegree {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    (multilinearInterp p).totalDegree ≤ n := by
  unfold multilinearInterp
  calc totalDegree (∑ a : Fin n → Bool, C (evalBool p a) * boolIndicator a)
      ≤ (Finset.univ.sup fun a => totalDegree (C (evalBool p a) * boolIndicator a)) :=
        totalDegree_finset_sum _ _
    _ ≤ n := Finset.sup_le (fun a _ =>
        calc totalDegree (C (evalBool p a) * boolIndicator a)
            ≤ totalDegree (C (evalBool p a)) + totalDegree (boolIndicator a) :=
              totalDegree_mul _ _
          _ ≤ 0 + n := Nat.add_le_add (by simp [totalDegree_C]) (totalDegree_boolIndicator_le a)
          _ = n := by simp)

/-- Axiom 1 at n = 4: every polynomial has a multilinear equivalent
    with degree ≤ 4 = (Nat.log 2 4)². -/
theorem depth4_simulation_at_4 (p : MvPolynomial (Fin 4) ℚ) :
    ∃ (q : MvPolynomial (Fin 4) ℚ),
      (∀ x, evalBool q x = evalBool p x) ∧
      q.totalDegree ≤ (Nat.log 2 4) ^ 2 ∧
      IsMultilinear q := by
  refine ⟨multilinearInterp p, multilinearInterp_evalBool p, ?_, multilinearInterp_isMultilinear p⟩
  calc (multilinearInterp p).totalDegree ≤ 4 := multilinearInterp_totalDegree p
    _ = (Nat.log 2 4) ^ 2 := by native_decide

/-- General-n multilinearization: every polynomial has a multilinear
    equivalent with degree ≤ n. -/
theorem multilinearize_exists {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    ∃ (q : MvPolynomial (Fin n) ℚ),
      (∀ x, evalBool q x = evalBool p x) ∧
      q.totalDegree ≤ n ∧
      PaperAxioms.IsMultilinear q :=
  ⟨multilinearInterp p,
   multilinearInterp_evalBool p,
   multilinearInterp_totalDegree p,
   multilinearInterp_isMultilinear p⟩

end Multilinearize
