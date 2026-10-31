import Mathlib

/-!
# Multilinear span: every function on the cube is a multilinear polynomial (PROVED)

The dimension argument's surjection — "every function `{0,1}ⁿ → 𝔽` is realised by a (multilinear) polynomial" —
is the heaviest remaining step.  Model a multilinear polynomial by its coefficient vector `c : Finset (Fin n) → 𝔽`
(coefficient of the monomial `∏_{i∈S} xᵢ`), and its evaluation

  `eval c x = Σ_S c S · ∏_{i∈S} (xᵢ as 0/1)`.

  `eval_pt` — at the indicator point of `T`, `eval c = Σ_{S ⊆ T} c S` (the zeta transform over the subset
        lattice).
  `eval_injective` — distinct coefficient vectors give distinct functions (multilinear **independence**), by
        strong induction over the subset lattice: `c T` is recovered from `eval c` at `pt T` minus the
        already-determined `Σ_{S ⊊ T} c S` (Möbius triangularity).
  `eval_surjective` — hence `eval` is **bijective** (injective + equal `card = |𝔽|^{2ⁿ}`), so **every** function
        on the cube is a multilinear polynomial.

This is the span/surjectivity that feeds `card_le_of_surjective` in `ComputationalDepthDimension`: composed with
the boosting reduction it yields the dimension bound on `|G|`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Multilinear

variable {n : ℕ} {F : Type*} [CommRing F]

/-- The indicator point of `T`: the Boolean vector that is `true` exactly on `T`. -/
def pt (T : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ T)

/-- The monomial function `∏_{i∈S} xᵢ` (each coordinate read as `0/1` in `𝔽`). -/
def monomialFn (S : Finset (Fin n)) (x : Fin n → Bool) : F := ∏ i ∈ S, (if x i then 1 else 0)

/-- Evaluate the multilinear polynomial with coefficient vector `c` at a Boolean point. -/
def eval (c : Finset (Fin n) → F) (x : Fin n → Bool) : F := ∑ S, c S * monomialFn S x

/-- A monomial at an indicator point is the subset-inclusion indicator: `∏_{i∈S} (pt T)ᵢ = [S ⊆ T]`. -/
theorem monomialFn_pt (S T : Finset (Fin n)) :
    monomialFn (F := F) S (pt T) = if S ⊆ T then 1 else 0 := by
  unfold monomialFn pt
  simp only [decide_eq_true_eq]
  rw [Finset.prod_boole]
  congr 1

/-- **Zeta transform.**  Evaluating at the indicator point of `T` sums the coefficients of all subsets of `T`. -/
theorem eval_pt (c : Finset (Fin n) → F) (T : Finset (Fin n)) :
    eval c (pt T) = ∑ S ∈ T.powerset, c S := by
  unfold eval
  have hterm : ∀ S, c S * monomialFn (F := F) S (pt T) = if S ⊆ T then c S else 0 := by
    intro S; rw [monomialFn_pt]; split <;> simp
  simp only [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp [Finset.mem_powerset]

/-- **Multilinear independence.**  The evaluation map is injective: distinct coefficient vectors compute distinct
functions on the cube.  Proved by strong induction over the subset lattice — `c T` is recovered from the
zeta-transform value at `pt T` once all proper subsets agree (Möbius triangularity). -/
theorem eval_injective : Function.Injective (eval (n := n) (F := F)) := by
  intro c c' h
  funext T
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    have hsum : ∑ S ∈ T.powerset, c S = ∑ S ∈ T.powerset, c' S := by
      have hval := congrFun h (pt T)
      rwa [eval_pt, eval_pt] at hval
    have hmem : T ∈ T.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl T)
    rw [← Finset.add_sum_erase _ c hmem, ← Finset.add_sum_erase _ c' hmem] at hsum
    have herase : ∑ S ∈ T.powerset.erase T, c S = ∑ S ∈ T.powerset.erase T, c' S := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [Finset.mem_erase, Finset.mem_powerset] at hS
      exact ih S (Finset.ssubset_iff_subset_ne.mpr ⟨hS.2, hS.1⟩)
    rw [herase] at hsum
    exact add_right_cancel hsum

/-- **Multilinear span.**  The evaluation map is surjective (indeed bijective): **every** function `{0,1}ⁿ → 𝔽` is
a multilinear polynomial.  Injective plus equal cardinality `|𝔽|^{2ⁿ}` forces bijectivity. -/
theorem eval_surjective [Fintype F] [DecidableEq F] :
    Function.Surjective (eval (n := n) (F := F)) := by
  have hcard : Fintype.card (Finset (Fin n) → F) = Fintype.card ((Fin n → Bool) → F) := by
    simp [Fintype.card_finset, Fintype.card_bool]
  exact ((Fintype.bijective_iff_injective_and_card eval).mpr ⟨eval_injective, hcard⟩).surjective

end PallLean.Paper93.DeepMath.PathB.Multilinear

#print axioms PallLean.Paper93.DeepMath.PathB.Multilinear.eval_injective
#print axioms PallLean.Paper93.DeepMath.PathB.Multilinear.eval_surjective
