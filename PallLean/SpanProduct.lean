/-
  SpanProduct.lean — Products of span elements lie in span of product set

  If each choice_i ∈ span(W_i), then ∏ choice_i ∈ span(∏ W_i).
  This is the "tensor product of finite-dimensional spaces" fact.
-/
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Span.Basic

namespace SpanProduct

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]

attribute [local instance] Classical.dec

/-! ## Core lemma: span(A) * span(B) ⊆ span(A * B) -/

/-- Product of two span elements lies in span of pairwise products. -/
theorem mul_mem_span_mul {R M : Type*} [CommSemiring R] [CommSemiring M] [Algebra R M]
    (A B : Set M) (a b : M)
    (ha : a ∈ Submodule.span R A) (hb : b ∈ Submodule.span R B) :
    a * b ∈ Submodule.span R { x * y | (x ∈ A) (y ∈ B) } := by
  -- Induction on ha: a ∈ span(A)
  induction ha using Submodule.span_induction with
  | mem x hx =>
    -- x ∈ A, b ∈ span(B). Induction on hb.
    induction hb using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    | zero => simp
    | add y z hy hz ihy ihz =>
      rw [mul_add]; exact Submodule.add_mem _ ihy ihz
    | smul r y hy ihy =>
      rw [mul_smul_comm]; exact Submodule.smul_mem _ r ihy
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [add_mul]; exact Submodule.add_mem _ ihx ihy
  | smul r x hx ihx =>
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ihx

/-! ## Finset version: product of choices from W_i -/

/-- The Cartesian product of Finsets as a Finset of polynomial products.
    For m factors: {∏_i w_i | w_i ∈ W_i}. -/
noncomputable def finsetProd {n : ℕ} :
    (m : ℕ) → (Fin m → Finset (MvPolynomial (Fin n) F)) →
    Finset (MvPolynomial (Fin n) F)
  | 0, _ => {1}
  | m + 1, W =>
    (W ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩).product
      (finsetProd m (fun i => W (Fin.castSucc i)))
    |>.image (fun ⟨a, b⟩ => a * b)

theorem finsetProd_card_le {n : ℕ} :
    (m : ℕ) → (W : Fin m → Finset (MvPolynomial (Fin n) F)) →
    (finsetProd m W).card ≤ Finset.univ.prod (fun i => (W i).card)
  | 0, _ => by simp [finsetProd]
  | m + 1, W => by
    simp only [finsetProd]
    calc (((W ⟨m, _⟩).product (finsetProd m fun i => W (Fin.castSucc i))).image
          (fun ⟨a, b⟩ => a * b)).card
        ≤ ((W ⟨m, _⟩).product (finsetProd m fun i => W (Fin.castSucc i))).card :=
          Finset.card_image_le
      _ = (W ⟨m, _⟩).card * (finsetProd m fun i => W (Fin.castSucc i)).card :=
          Finset.card_product _ _
      _ ≤ (W ⟨m, _⟩).card * Finset.univ.prod (fun i => (W (Fin.castSucc i)).card) := by
          apply Nat.mul_le_mul_left
          exact finsetProd_card_le m _
      _ = Finset.univ.prod (fun i => (W i).card) := by
          rw [Fin.prod_univ_castSucc]; exact Nat.mul_comm _ _

/-- Main theorem: product of span elements ∈ span of finsetProd. -/
theorem prod_mem_span_finsetProd {n : ℕ} :
    (m : ℕ) → (W : Fin m → Finset (MvPolynomial (Fin n) F)) →
    (choices : Fin m → MvPolynomial (Fin n) F) →
    (∀ i, choices i ∈ Submodule.span F ((W i : Set (MvPolynomial (Fin n) F)))) →
    Finset.univ.prod choices ∈
      Submodule.span F ((finsetProd m W : Set (MvPolynomial (Fin n) F)))
  | 0, _, _, _ => by
    simp only [finsetProd, Finset.prod_empty, Finset.coe_singleton]
    exact Submodule.subset_span rfl
  | m + 1, W, choices, hchoices => by
    -- Split: ∏_{Fin(m+1)} = choices_last * ∏_{Fin m} choices_init
    rw [Fin.prod_univ_castSucc]
    -- choices_last ∈ span(W_last), prod_init ∈ span(finsetProd m W_init)
    have hlast := hchoices ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩
    have hinit := prod_mem_span_finsetProd m
      (fun i => W (Fin.castSucc i))
      (fun i => choices (Fin.castSucc i))
      (fun i => hchoices (Fin.castSucc i))
    -- Fin.prod_univ_castSucc gives (∏ castSucc) * last, but we need last * (∏ castSucc)
    -- Actually it gives the reverse: (∏ init) * last
    -- mul_mem_span_mul gives span membership for a*b
    -- We need to match the product order from Fin.prod_univ_castSucc
    have hprod := mul_mem_span_mul
      (finsetProd m (fun i => W (Fin.castSucc i)) : Set (MvPolynomial (Fin n) F))
      (W (Fin.last m) : Set (MvPolynomial (Fin n) F))
      (Finset.univ.prod (fun i => choices (Fin.castSucc i)))
      (choices (Fin.last m))
      hinit hlast
    refine Submodule.span_mono ?_ hprod
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hq
    show a * b ∈ (finsetProd (m + 1) W : Set _)
    simp only [finsetProd, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, mul_comm b a⟩

end SpanProduct
