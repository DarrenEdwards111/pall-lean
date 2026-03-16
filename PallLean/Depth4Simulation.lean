/-
  Depth4Simulation.lean — Multilinear Interpolation (Paper §2.3 backbone)

  Every Boolean function f : {0,1}^n → Bool is computed by a multilinear
  polynomial of degree ≤ n (Lagrange interpolation). This is the polynomial
  representation used in the SPDP analysis.
-/
import PallLean.BoolEval
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Basic

namespace Depth4Simulation

open MvPolynomial BoolEval

/-- Boolean indicator: δ_a(x) = ∏_i (if a_i then x_i else 1-x_i). -/
noncomputable def boolIndicator {n : ℕ} (a : Fin n → Bool) :
    MvPolynomial (Fin n) ℚ :=
  ∏ i : Fin n, if a i then X i else (1 - X i)

/-- Multilinear interpolation: p_f = Σ_{a : f(a)=true} δ_a. -/
noncomputable def multilinearInterp {n : ℕ} (f : (Fin n → Bool) → Bool) :
    MvPolynomial (Fin n) ℚ :=
  ∑ a ∈ Finset.univ.filter (fun a => f a), boolIndicator a

/-- Evaluation of δ_a at Boolean point b: 1 if a = b, 0 otherwise. -/
theorem eval_boolIndicator {n : ℕ} (a b : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToRat (b i)) (boolIndicator a) =
    if a = b then 1 else 0 := by
  unfold boolIndicator
  rw [map_prod]
  by_cases hab : a = b
  · subst hab; simp only [ite_true]
    apply Finset.prod_eq_one; intro i _
    cases hai : a i <;> simp [hai, boolToRat, map_sub, eval_X]
  · simp only [hab, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h; push_neg at h; exact hab (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hai : a i <;> cases hbi : b i <;> simp_all [boolToRat, map_sub, eval_X]

/-- Multilinear interpolation correctly represents f. -/
theorem multilinearInterp_correct {n : ℕ} (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    MvPolynomial.eval (fun i => boolToRat (x i)) (multilinearInterp f) =
    boolToRat (f x) := by
  unfold multilinearInterp
  rw [map_sum]; simp only [eval_boolIndicator]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold boolToRat; split_ifs <;> simp_all

/-- The indicator δ_a has totalDegree ≤ n. -/
theorem boolIndicator_degree {n : ℕ} (a : Fin n → Bool) :
    (boolIndicator a).totalDegree ≤ n := by
  unfold boolIndicator
  calc (∏ i : Fin n, if a i then X i else 1 - X i).totalDegree
      ≤ ∑ i : Fin n, (if a i then (X i : MvPolynomial (Fin n) ℚ)
          else 1 - X i).totalDegree := totalDegree_finset_prod _ _
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => by
        split_ifs with h
        · rw [totalDegree_X (R := ℚ)]
        · exact le_trans (totalDegree_sub ..) (by rw [totalDegree_one, totalDegree_X (R := ℚ)]; omega)
    _ = n := by simp [Finset.card_univ, Fintype.card_fin]

/-- Degree of a sum ≤ max of degrees (proved by induction). -/
private theorem totalDegree_finset_sum_le {σ R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → MvPolynomial σ R)
    (d : ℕ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d := by
  induction s using Finset.induction with
  | empty => simp [totalDegree_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (totalDegree_add ..) (max_le
      (hf _ (Finset.mem_insert_self ..))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The multilinear interpolation has totalDegree ≤ n. -/
theorem multilinearInterp_degree {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (multilinearInterp f).totalDegree ≤ n := by
  unfold multilinearInterp
  exact totalDegree_finset_sum_le _ _ n fun a _ => boolIndicator_degree a

/-- Every Boolean function has a polynomial representation of degree ≤ n. -/
theorem depth4_simulation {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ p : MvPolynomial (Fin n) ℚ,
      (∀ x, MvPolynomial.eval (fun i => boolToRat (x i)) p = boolToRat (f x)) ∧
      p.totalDegree ≤ n :=
  ⟨multilinearInterp f, multilinearInterp_correct f, multilinearInterp_degree f⟩

lemma totalDegree_boolIndicator_le {n : ℕ} (a : Fin n → Bool) :
    (boolIndicator a).totalDegree ≤ n := by
  unfold boolIndicator
  calc totalDegree (∏ i : Fin n, if a i then X i else 1 - X i : MvPolynomial (Fin n) ℚ)
      ≤ ∑ i : Fin n, totalDegree (if a i then X i else 1 - X i : MvPolynomial (Fin n) ℚ) :=
        totalDegree_finset_prod _ _
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun i _ => by
        split
        · simp [totalDegree_X]
        · exact le_trans (totalDegree_sub 1 (X i)) (by simp [totalDegree_X]))
    _ = n := by simp

lemma totalDegree_multilinearInterp_le {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (multilinearInterp f).totalDegree ≤ n := by
  unfold multilinearInterp
  induction (Finset.univ.filter (fun a => f a)) using Finset.induction with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (totalDegree_add _ _) (max_le (totalDegree_boolIndicator_le a) ih)

end Depth4Simulation
