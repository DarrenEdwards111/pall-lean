import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultilinear
import Mathlib

/-!
# Representation unification: `{-1,+1}` monomials in the `{0,1}` basis (PROVED bridge)

The folding identity and the monomial product law live on the `{-1,+1}ⁿ` cube (each `xᵢ² = 1`), while the
multilinear span (`ComputationalDepthMultilinear.eval_surjective`) is proved on the `{0,1}ⁿ` cube.  To run the
boosting surjection on one representation we relate the two monomial bases.

  `walshFn_eq_sum_mono0` — the **change-of-basis bridge**: a `{-1,+1}` monomial is a triangular combination of
        `{0,1}` monomials,
            `∏_{i∈S} (-1)^{bᵢ}  =  Σ_{T ⊆ S} (-2)^{|T|} · ∏_{i∈T} (bᵢ as 0/1)`,
        obtained by expanding `∏_{i∈S}(1 - 2·xᵢ)`.

The change of basis is **triangular** in the subset lattice with diagonal entry `(-2)^{|S|}` (the `T = S` term),
hence invertible exactly when `2` is a unit (`char 𝔽 ≠ 2`, the odd-prime field of Smolensky's `{-1,+1}` route).
Composed with `eval_surjective` (the `{0,1}` monomials span every function), invertibility transfers the span to
the `{-1,+1}` monomials — unifying the representations.  This file proves the bridge; the invertibility/transfer
(needing `2 ≠ 0`) is the remaining step.
-/

namespace PallLean.Paper93.DeepMath.PathB.RepUnify

variable {n : ℕ} {F : Type*} [CommRing F]

set_option linter.unnecessarySeqFocus false in
/-- **Change-of-basis bridge.**  A `{-1,+1}` monomial `∏_{i∈S} (-1)^{bᵢ}` expands, via `(-1)^{bᵢ} = 1 - 2·bᵢ`, as
the triangular combination `Σ_{T⊆S} (-2)^{|T|} · ∏_{i∈T} bᵢ` of `{0,1}` monomials (the `Multilinear.monomialFn`).
The top term (`T = S`) has coefficient `(-2)^{|S|}`, so the change of basis is invertible iff `2` is a unit. -/
theorem walshFn_eq_sum_mono0 (b : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i ∈ S, (if b i then (-1 : F) else 1))
      = ∑ T ∈ S.powerset, (-2) ^ T.card * Multilinear.monomialFn T b := by
  have hterm : ∀ i, (if b i then (-1 : F) else 1) = (-2) * (if b i then (1 : F) else 0) + 1 := by
    intro i; cases b i <;> simp <;> ring
  simp_rw [hterm]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
    Multilinear.monomialFn]

end PallLean.Paper93.DeepMath.PathB.RepUnify

#print axioms PallLean.Paper93.DeepMath.PathB.RepUnify.walshFn_eq_sum_mono0
