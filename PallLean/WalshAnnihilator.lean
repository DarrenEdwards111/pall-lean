/-
  WalshAnnihilator.lean — Walsh character annihilator construction

  Proves annihilator_exists: for D+1 ≤ n, there exists w orthogonal
  to all degree-≤-D polynomial evaluations with a positive entry.
-/
import PallLean.BoolEval
import PallLean.Restriction
import PallLean.PaperAxioms
import PallLean.PneqNP_General
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card

namespace WalshAnnihilator

open BoolEval Restriction MvPolynomial PaperAxioms PneqNP_General Finset BigOperators

/-! ## Walsh weight -/

/-- Walsh weight as product over Fin n. -/
noncomputable def walshW (n D : ℕ) (hD : D + 1 ≤ n)
    (x : Fin n → Bool) : ℚ :=
  ∏ i : Fin n, if i.val < D + 1 then (1 - 2 * boolToRat (x i)) else 1

theorem walshW_pos (n D : ℕ) (hD : D + 1 ≤ n) :
    walshW n D hD (fun _ => false) > 0 := by
  unfold walshW boolToRat
  simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero]
  exact Finset.prod_pos (fun i _ => by split_ifs <;> norm_num)

/-! ## Key lemma: zero factor kills product sum -/

theorem sum_bool_prod_eq_zero {n : ℕ} (g : Fin n → Bool → ℚ)
    (k : Fin n) (hk : ∑ b : Bool, g k b = 0) :
    ∑ x : (Fin n → Bool), ∏ i : Fin n, g i (x i) = 0 := by
  rw [show (∑ x : (Fin n → Bool), ∏ i : Fin n, g i (x i)) =
    ∏ i : Fin n, ∑ b : Bool, g i b from (Fintype.prod_sum (fun i b => g i b)).symm]
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

/-! ## Pigeonhole for free variable -/

theorem exists_free_var {n D : ℕ} (α : Fin n →₀ ℕ)
    (hα : α.support.card ≤ D) (hD : D + 1 ≤ n) :
    ∃ k : Fin n, k.val < D + 1 ∧ k ∉ α.support := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective
      (fun j : Fin (D + 1) => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hD⟩ : Fin n)) :=
    fun a b hab => Fin.ext (by have := congr_arg Fin.val hab; simpa using this)
  have himg : ∀ j : Fin (D + 1),
      (⟨j.val, Nat.lt_of_lt_of_le j.isLt hD⟩ : Fin n) ∈ α.support :=
    fun j => h ⟨j.val, Nat.lt_of_lt_of_le j.isLt hD⟩ j.isLt
  have : D + 1 ≤ α.support.card := by
    calc D + 1 = Fintype.card (Fin (D + 1)) := by simp
      _ = (Finset.univ.image
            (fun j : Fin (D + 1) => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hD⟩ : Fin n))).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ α.support.card :=
          Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
            obtain ⟨j, rfl⟩ := hx; exact himg j)
  omega

/-! ## Support card vs degree -/

theorem support_card_le_degree {n : ℕ} (α : Fin n →₀ ℕ) :
    α.support.card ≤ (α.sum fun _ v => v) := by
  calc α.support.card
      = ∑ _i ∈ α.support, 1 := by simp
    _ ≤ ∑ i ∈ α.support, α i := Finset.sum_le_sum (fun i hi => by
        rw [Finsupp.mem_support_iff] at hi; omega)
    _ = α.sum fun _ v => v := rfl

/-! ## Per-monomial orthogonality via factorization -/

/-- Combined factor: boolToRat(b)^{α i} × Walsh factor. -/
def mwFactor (D : ℕ) (α : Fin n →₀ ℕ) (i : Fin n) (b : Bool) : ℚ :=
  boolToRat b ^ α i * if i.val < D + 1 then (1 - 2 * boolToRat b) else 1

/-- The product of mwFactors equals the monomial eval × Walsh weight. -/
theorem prod_mwFactor_eq {n D : ℕ} (hD : D + 1 ≤ n) (α : Fin n →₀ ℕ)
    (x : Fin n → Bool) :
    (∏ i : Fin n, mwFactor D α i (x i)) =
    (∏ i : Fin n, boolToRat (x i) ^ α i) *
    walshW n D hD x := by
  unfold mwFactor walshW
  rw [← Finset.prod_mul_distrib]

/-- Monomial eval (full product form) times Walsh weight. -/
theorem monomial_walsh_sum_zero {n D : ℕ} (hD : D + 1 ≤ n) (α : Fin n →₀ ℕ)
    (hdeg : (α.sum fun _ v => v) ≤ D) :
    ∑ x : (Fin n → Bool),
      (∏ i : Fin n, boolToRat (x i) ^ α i) *
      walshW n D hD x = 0 := by
  -- Rewrite as product of combined factors
  simp_rw [← prod_mwFactor_eq hD α]
  -- Find free variable via pigeonhole
  have hsup : α.support.card ≤ D := le_trans (support_card_le_degree α) hdeg
  obtain ⟨k, hk_active, hk_free⟩ := exists_free_var α hsup hD
  -- Apply zero-factor lemma
  apply sum_bool_prod_eq_zero _ k
  -- Show factor sum at k is 0
  have hα_k : α k = 0 := Finsupp.notMem_support_iff.mp hk_free
  simp only [mwFactor, hα_k, pow_zero, one_mul, hk_active, ↓reduceIte]
  simp [Fintype.sum_bool, boolToRat]

/-! ## Full polynomial orthogonality -/

theorem poly_walsh_sum_zero {n D : ℕ} (hD : D + 1 ≤ n)
    (q : MvPolynomial (Fin n) ℚ) (hdeg : q.totalDegree ≤ D) :
    ∑ x : (Fin n → Bool),
      evalBool q x * walshW n D hD x = 0 := by
  -- Expand evalBool using eval_eq'
  simp only [evalBool, MvPolynomial.eval_eq']
  -- Distribute: Σ_x (Σ_α c_α * ∏ boolToRat^{α i}) * w = Σ_α c_α * Σ_x ∏ ... * w
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro α hα
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  -- Each monomial's sum is 0
  have hdeg_α : (α.sum fun _ v => v) ≤ D :=
    le_trans (le_totalDegree hα) hdeg
  rw [monomial_walsh_sum_zero hD α hdeg_α]
  ring

/-! ## Build annihilator data -/

noncomputable def mkAnnihilatorData (n D : ℕ) (hD : D + 1 ≤ n) :
    { ad : AnnihilatorData n // ad.d = D } :=
  ⟨{ ρ := idRestriction n
     d := D
     w := walshW n D hD
     hw_pos := by
       refine ⟨fun _ => false, ?_⟩
       show walshW n D hD (extendAssignment (idRestriction n) (fun _ => false)) > 0
       have : extendAssignment (idRestriction n) (fun _ : Fin n => false) = fun _ => false := by
         funext i; simp [extendAssignment, idRestriction]
       rw [this]
       exact walshW_pos n D hD
     hw_orth := by
       intro q hq
       have hext : ∀ x : Fin n → Bool,
           extendAssignment (idRestriction n) x = x := by
         intro x; funext i; simp [extendAssignment, idRestriction]
       simp_rw [hext]
       exact poly_walsh_sum_zero hD q hq
   }, rfl⟩

end WalshAnnihilator
