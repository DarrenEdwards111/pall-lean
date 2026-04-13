import PallLean.ProductDeriv
import PallLean.IterDerivHelpers
import PallLean.LowDegAnnihilation
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

/-!
## Lemma 2: Iterated Leibniz for finite products

The iterated derivative `iterDerivList S (∏_{i ∈ s} f i)` lies in the
`F`-span of all products of the form `∏_{i ∈ s} iterDerivList (hᵢ) (f i)`,
where each `hᵢ` is a sublist of `S` drawn from its elements.

Proof is by induction on S:
- Base: `S = []` gives the single term `∏ f i`.
- Step: apply single-step Leibniz (Lemma 1), distribute `iterDerivList rest`
  over the resulting sum by linearity, then invoke the induction hypothesis
  on each summand.
-/

section IteratedLeibniz

variable {n : ℕ} {F : Type*} [CommRing F]

/-- Helper: `iterDerivList` distributes over `Finset.sum`. -/
theorem iterDerivList_finset_sum {ι : Type*} (S : List (Fin n))
    (t : Finset ι) (f : ι → MvPolynomial (Fin n) F) :
    iterDerivList S (∑ i ∈ t, f i) =
      ∑ i ∈ t, iterDerivList S (f i) := by
  unfold iterDerivList
  exact LowDeg.foldl_pderiv_finset_sum S t f

/-- The set of "distributed derivative products": all products of local derivatives
    where each factor `f i` is differentiated by some sublist of derivatives
    drawn from the elements of `S`. -/
def distribDerivProds {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) F) (S : List (Fin n)) :
    Set (MvPolynomial (Fin n) F) :=
  { g | ∃ (h : ι → List (Fin n)),
    (∀ i, ∀ v ∈ h i, v ∈ S) ∧
    g = s.prod (fun i => iterDerivList (h i) (f i)) }

/-- Core lemma: `iterDerivList S (s.prod f)` is in the span of distributed derivative products.

This is the iterated Leibniz rule for finite products: differentiating a product `∏_{i ∈ s} f i`
by a list of derivatives `S` yields a sum where each summand is a product with the derivatives
distributed among the factors. -/
theorem iterDerivList_finset_prod_mem_span {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) F) (S : List (Fin n)) :
    iterDerivList S (s.prod f) ∈
      Submodule.span F (distribDerivProds s f S) := by
  -- We induct on S, generalizing f so that the IH applies to any factor-family.
  induction S generalizing f with
  | nil =>
    -- iterDerivList [] (s.prod f) = s.prod f, which is in the set with h i = [] for all i.
    rw [IterDerivHelpers.iterDerivList_nil]
    apply Submodule.subset_span
    refine ⟨fun _ => [], fun _ _ hv => absurd hv List.not_mem_nil, ?_⟩
    -- s.prod (fun i => iterDerivList [] (f i)) = s.prod f
    apply Finset.prod_congr rfl; intro i _; simp [IterDerivHelpers.iterDerivList_nil]
  | cons v rest ih =>
    -- iterDerivList (v :: rest) (s.prod f) = iterDerivList rest (pderiv v (s.prod f))
    rw [IterDerivHelpers.iterDerivList_cons]
    -- Apply single-step Leibniz (Lemma 1):
    -- pderiv v (s.prod f) = ∑_{k ∈ s} (pderiv v (f k)) * (s.erase k).prod f
    rw [pderiv_finset_prod s f v]
    -- Distribute iterDerivList rest over the sum
    rw [iterDerivList_finset_sum]
    -- Now we need: ∑_{k ∈ s} iterDerivList rest ((pderiv v (f k)) * (s.erase k).prod f)
    -- is in span(distribDerivProds s f (v :: rest))
    apply Submodule.sum_mem
    intro k hk
    -- For each k ∈ s, the summand is iterDerivList rest of a product over s
    -- where factor k has been replaced by (pderiv v (f k)).
    -- Define f' := Function.update f k (pderiv v (f k))
    -- Then (pderiv v (f k)) * (s.erase k).prod f = s.prod f'
    -- By IH (generalized over f), iterDerivList rest (s.prod f') ∈ span(distribDerivProds s f' rest).
    -- We then show distribDerivProds s f' rest ⊆ distribDerivProds s f (v :: rest).
    set f' : ι → MvPolynomial (Fin n) F :=
      Function.update f k (pderiv v (f k)) with hf'_def
    -- Rewrite the summand as iterDerivList rest (s.prod f')
    have hsummand : pderiv v (f k) * (s.erase k).prod f = s.prod f' := by
      rw [← Finset.mul_prod_erase _ _ hk]
      congr 1
      · exact (Function.update_self k (pderiv v (f k)) f).symm
      · apply Finset.prod_congr rfl
        intro j hj
        exact (Function.update_of_ne (Finset.mem_erase.mp hj).1 _ f).symm
    rw [hsummand]
    -- Apply the IH to f'
    have ih_f' := ih f'
    -- Show distribDerivProds s f' rest ⊆ distribDerivProds s f (v :: rest)
    suffices h_sub : distribDerivProds s f' rest ⊆ distribDerivProds s f (v :: rest) by
      exact Submodule.span_mono h_sub ih_f'
    -- Prove the set inclusion
    intro g ⟨h_assign, h_elts, h_eq⟩
    -- g = s.prod (fun i => iterDerivList (h_assign i) (f' i))
    -- f' i = if i = k then pderiv v (f k) else f i
    -- Define h' i = if i = k then v :: h_assign i else h_assign i
    refine ⟨fun i => if i = k then v :: h_assign i else h_assign i, ?_, ?_⟩
    · -- All elements of h' i are in v :: rest
      intro i w hw
      simp only at hw
      split_ifs at hw with hik
      · -- i = k: w ∈ v :: h_assign k
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem v (h_elts i w hw')
      · -- i ≠ k: w ∈ h_assign i, so w ∈ rest ⊆ v :: rest
        exact List.mem_cons_of_mem v (h_elts i w hw)
    · -- g = s.prod (fun i => iterDerivList (h' i) (f i))
      rw [h_eq]
      apply Finset.prod_congr rfl
      intro i _hi
      -- The goal is: iterDerivList ((if i = k then ...) i) (f' i) = iterDerivList (...) (f i)
      -- We need to unfold the if and the Function.update.
      simp only
      split_ifs with hik
      · -- i = k: need iterDerivList (v :: h_assign k) (f k)
        --       = iterDerivList (h_assign k) (pderiv v (f k))
        --       = iterDerivList (h_assign k) (f' k)
        subst hik
        rw [IterDerivHelpers.iterDerivList_cons]
        congr 1
        exact Function.update_self i (pderiv v (f i)) f
      · -- i ≠ k: iterDerivList (h_assign i) (f' i) = iterDerivList (h_assign i) (f i)
        congr 1
        exact Function.update_of_ne hik _ f

end IteratedLeibniz

end LeibnizProduct
