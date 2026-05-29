import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Forster isotropic position via potential minimization (the live `∃T` grind)

This file is the *actual attempt* at the sole remaining analytic obligation of the
Forster route (see `FORSTER_ISOTROPIC_KERNEL_HANDOFF.md` and
`ComputationalDepthForsterScaffold.lean`): given vectors `v₁,…,v_m ∈ ℝ^d`, nonzero
and **spanning**, produce an invertible `T` putting their normalized images into
*radially isotropic / tight-frame* position, i.e.
`∑ᵢ ûᵢ ûᵢᵀ = (m/d)·I` with `ûᵢ = T vᵢ / ‖T vᵢ‖`.

The classical proof minimizes the log-potential `F(S) = ∑ᵢ log ⟪vᵢ, S vᵢ⟫` over the
SPD slice `{det S = 1}` and reads off the tight-frame identity from first-order
optimality, with `T = (S⋆)^{1/2}`.  The grind is staged bottom-up:

* **rung 1 (this commit):** the potential and its *well-definedness substrate* —
  the summands `⟪vᵢ, S vᵢ⟫` are strictly positive (so `log` is honest), plus the
  purely-algebraic *conjugation identity* `vecMulVec (M *ᵥ v) (M *ᵥ w) = M · vᵢvᵢᵀ · Mᵀ`
  that the `T = √S` substitution (rung 4) is built from.  These are real, fully
  proved, no `sorry`.
* rung 2 (next): coercivity from spanning ⇒ a minimizer on a compact sublevel set.
* rung 3 (the crux): variational first-order optimality
  `∑ᵢ (vᵢvᵢᵀ)/⟪vᵢ,S⋆vᵢ⟫ = (m/d)·(S⋆)⁻¹`.
* rung 4: substitute `T = √S⋆` ⇒ the tight-frame identity (uses rung 1's identity).

Nothing here is faked or socketed: each rung is a real lemma; the unproved rungs
are simply absent, not assumed.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterIsotropic

open scoped BigOperators Matrix

variable {d m : ℕ}

/-- **Rung 1a.** For a positive-definite `S` and a nonzero vector `v`, the quadratic
form `vᵀ S v` is strictly positive.  This is what makes the log-potential's
summands `log ⟪vᵢ, S vᵢ⟫` well defined (finite) and the minimization honest. -/
lemma quadForm_pos {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin d → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ (S *ᵥ v) := by
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hS).2 hv
  simpa using h

/-- The log-potential `F(S) = ∑ᵢ log ⟪vᵢ, S vᵢ⟫` whose minimizer over the `det = 1`
SPD slice gives the isotropic (tight-frame) position. -/
noncomputable def potential (v : Fin m → (Fin d → ℝ)) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, Real.log (v i ⬝ᵥ (S *ᵥ v i))

/-- **Rung 1b (algebraic core of the `T = √S` substitution).**  Conjugating the
rank-one outer product `v wᵀ` by a matrix `M` on the left of `v` and on the right
of `w` is the same as conjugating the outer product:
`(M v)(M w)ᵀ = M · (v wᵀ) · Mᵀ`.  Summed over the rank-one terms with `M = √S⋆`,
this turns the first-order optimality identity into the tight-frame identity. -/
lemma vecMulVec_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ) :
    Matrix.vecMulVec (M *ᵥ v) (M *ᵥ w) = M * Matrix.vecMulVec v w * Mᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply,
    dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

#print axioms quadForm_pos
#print axioms vecMulVec_mulVec

end PallLean.Paper93.DeepMath.PathB.ForsterIsotropic
