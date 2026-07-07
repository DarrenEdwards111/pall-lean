import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDirectSum

/-!
# N-Frame: ruling out the cancellation route for `qform` (base case)

Can two disjoint copies of `g = qform A` be computed with `< 2·C(g)` gates by exploiting `F₂`
cancellation — linear mixing of the two copies' variables so cross-terms cancel?  For the base
case (`qform` itself) the answer is NO, and the reason is an invariant cancellation cannot touch.

## Why cancellation cannot help (paper)

`F₂` cancellation IS a linear change of variables.  The detection matrix `M = A + Aᵀ` of a
quadratic form is a FUNCTION invariant — `bilinSym A (e_a)(e_b) = M_{ab}` (`bilinSym_units`),
fixed by `qform`, unchanged by ANY circuit-internal linear mixing.  Two facts then bind every
circuit, cancellation or not:

  (1) `rank_{F₂}(M)` is invariant under invertible linear change of variables (change of basis
      preserves rank) — so cancellation cannot lower it.
  (2) `rank_{F₂}(M)` is ADDITIVE under direct sum: for two disjoint copies `M = M₁ ⊕ M₂` is
      block-diagonal and `rank(M₁ ⊕ M₂) = rank(M₁) + rank(M₂)`.

By Mirwald–Schnorr (the multiplicative complexity of a quadratic form over `F₂` is `≥
rank(M)/2`), the AND-gate count for the direct sum is `≥ (rank M₁ + rank M₂)/2` = the sum of the
per-copy bounds.  So no linear mixing of the two copies saves products: the cancellation route is
ruled out for `qform`.

## The additive-rank witness, concretely (Lean)

  `direct_sum_distinct` — **PROVED**: given two induced matchings on disjoint blocks
        (block-internal identity detection, zero cross-detection — i.e. a block-diagonal `M`), the
        COMBINED family over `Fin (r₁ + r₂)` is pairwise distinguished by `qform A`.  So the direct
        sum carries an `(r₁+r₂)`-fold identity submatrix of `M` — `rank(M₁ ⊕ M₂) ≥ r₁ + r₂` — and
        this bound is a FUNCTION property, holding for EVERY circuit regardless of cancellation.

This makes (2) concrete on the drag's own index type: the detectable rank ADDS, and since it is a
function invariant it is immune to circuit-level cancellation.  Combined with the drag's
`coneExcess ≥ cut-rank`, the base-case direct sum for `qform` is cancellation-proof.

## Honest scope — base case resolved; the super-linear lift is untouched

For `qform` the rank bound is (up to constants) TIGHT — `coneExcess(qform) = Θ(N) = Θ(rank)` —
so the additive, cancellation-invariant rank forces `coneExcess(qform^{(2)}) = 2·Θ(N)`: the
base-case direct sum HOLDS and cancellation is ruled out.  This does NOT lift to the recursive
`f_N`, whose `coneExcess` is SUPER-linear and hence exceeds its rank; there the rank bound is not
tight, so cancellation in COMBINING sub-results is not ruled out by rank.  So: the cancellation
route is closed for the base case (`qform`), and the ONLY remaining gap is the super-linear lift —
`coneExcess(f_{2N}) ≥ 2·coneExcess(f_N)` where the doubled quantity exceeds the rank.  The
Mirwald–Schnorr rank bound is cited, not re-formalized; the additive-rank witness is proved here.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCancellation

open PallLean.Paper93.DeepMath.PathB.NFrameQuadForm
open PallLean.Paper93.DeepMath.PathB.NFrameEpsBias
open PallLean.Paper93.DeepMath.PathB.NFrameInducedMatch
open PallLean.Paper93.DeepMath.PathB.NFrameDirectSum

variable {N : ℕ}

/-- **THE ADDITIVE-RANK WITNESS (proved)**: two induced matchings on disjoint blocks
(block-diagonal `M`) combine to a pairwise-distinguished family over `Fin (r₁ + r₂)` — so the
direct sum carries an `(r₁+r₂)`-identity submatrix of `M`, `rank(M₁ ⊕ M₂) ≥ r₁ + r₂`.  A FUNCTION
property, holding for EVERY circuit: cancellation (linear mixing) cannot reduce it. -/
theorem direct_sum_distinct {r₁ r₂ : ℕ} (A : Fin N → Fin N → ZMod 2)
    (s₁ t₁ : Fin r₁ → Fin N) (s₂ t₂ : Fin r₂ → Fin N)
    (hid₁ : ∀ k l, bilinSym A (unitDir (t₁ k)) (unitDir (s₁ l)) = if k = l then 1 else 0)
    (hid₂ : ∀ k l, bilinSym A (unitDir (t₂ k)) (unitDir (s₂ l)) = if k = l then 1 else 0)
    (hcross₁₂ : ∀ k l, bilinSym A (unitDir (t₁ k)) (unitDir (s₂ l)) = 0)
    (hcross₂₁ : ∀ k l, bilinSym A (unitDir (t₂ k)) (unitDir (s₁ l)) = 0)
    (T T' : Finset (Fin (r₁ + r₂))) (hne : T ≠ T') :
    ∃ x : Fin N → ZMod 2,
      qform A (x + rowSum (fun l => Sum.elim s₁ s₂ (finSumFinEquiv.symm l)) T)
        ≠ qform A (x + rowSum (fun l => Sum.elim s₁ s₂ (finSumFinEquiv.symm l)) T') := by
  have hid : ∀ k l : Fin (r₁ + r₂),
      bilinSym A (unitDir (Sum.elim t₁ t₂ (finSumFinEquiv.symm k)))
                 (unitDir (Sum.elim s₁ s₂ (finSumFinEquiv.symm l)))
        = if k = l then 1 else 0 := by
    intro k l
    rw [combined_detection_identity A s₁ t₁ s₂ t₂ hid₁ hid₂ hcross₁₂ hcross₂₁]
    by_cases h : k = l <;> simp [h, EmbeddingLike.apply_eq_iff_eq]
  exact induced_matching_distinct A
    (fun l => Sum.elim s₁ s₂ (finSumFinEquiv.symm l))
    (fun k => Sum.elim t₁ t₂ (finSumFinEquiv.symm k)) hid T T' hne

end PallLean.Paper93.DeepMath.PathB.NFrameCancellation

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCancellation.direct_sum_distinct
