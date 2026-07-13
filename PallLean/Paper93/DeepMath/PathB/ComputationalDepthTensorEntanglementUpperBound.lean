import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTensorEntanglementLowerBound

/-!
# Schmidt-rank upper bound: the bond bounds are tight, and only exponential in the block length

The residual-span dimension (cross-cut rank) at a cut `S` is at most `2^{|S|}`, because every residual depends
only on the `S`-coordinates and hence factors through the restriction map `(ι → Bool) → ({i ∈ S} → Bool)`.

`finrank_residualSpan_le_two_pow_card` — `rank ≤ 2^{|S|}`.

This makes the entanglement lower bounds **tight** (`eqFun`/`hardF` reach `≈ 2^{|S|}`), and — crucially — shows what
they do and do not say about input size `n = |ι|`:

* `eqFun`: `|S| = k`, `n = 2k`, so the bond is `2^k = 2^{n/2}` — **super-polynomial in `n`** (but it collapses
  under reordering; see `SCOPE_TENSOR_COST_CONNECTION`);
* `hardF`/`orMux`/`edFun`: `|S| = b`, but `n ≥ 2^b` (the `2^b` data cells), so the bond is `2^b ≤ n` — **only
  linear in `n`**.  Exponential in the block length `b = O(log n)`, not in the input size.

So among the four families, only `eqFun` (unpadded) has a genuinely super-polynomial-in-`n` bond, and the addressing
families are — at their fixed cut — linear-bond.  See `SCOPE_TN_HARDNESS_ATTACK` for what this means for the
tensor-network-hardness question.

## Honest scope

A tightness/upper-bound companion to the entanglement lower bounds.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TensorEntanglement

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Schmidt-rank upper bound.**  The residual-span dimension at a cut `S` is at most `2^{|S|}` — every residual
depends only on the `S`-coordinates, so factors through the restriction to `S`. -/
theorem finrank_residualSpan_le_two_pow_card (S : Finset ι) (f : (ι → Bool) → K) :
    Module.finrank K (Submodule.span K (Set.range (residualOf S f))) ≤ 2 ^ S.card := by
  classical
  haveI : FiniteDimensional K ((ι → Bool) → K) := inferInstance
  let restr : (ι → Bool) → ({i : ι // i ∈ S} → Bool) := fun x i => x i.val
  let pull : (({i : ι // i ∈ S} → Bool) → K) →ₗ[K] ((ι → Bool) → K) := LinearMap.funLeft K K restr
  have hmem : ∀ α, residualOf S f α ∈ LinearMap.range pull := by
    intro α
    refine ⟨fun σ => f (fun i => if h : i ∈ S then σ ⟨i, h⟩ else α i), ?_⟩
    funext x
    refine congrArg f ?_
    funext i
    by_cases h : i ∈ S <;> simp [restr, h]
  have hsub : Submodule.span K (Set.range (residualOf S f)) ≤ LinearMap.range pull := by
    rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact hmem α
  have hdim : Module.finrank K (({i : ι // i ∈ S} → Bool) → K) = 2 ^ S.card := by
    rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have h1 : Module.finrank K (LinearMap.range pull) ≤ 2 ^ S.card :=
    hdim ▸ LinearMap.finrank_range_le pull
  exact le_trans (Submodule.finrank_mono hsub) h1

end PallLean.Paper93.DeepMath.PathB.TensorEntanglement

#print axioms PallLean.Paper93.DeepMath.PathB.TensorEntanglement.finrank_residualSpan_le_two_pow_card
