import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

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

/-- Bilinear scaling of the outer product: `(a•x)(a•y)ᵀ = a²·(x yᵀ)`. -/
lemma vecMulVec_smul (a : ℝ) (x y : Fin d → ℝ) :
    Matrix.vecMulVec (a • x) (a • y) = (a * a) • Matrix.vecMulVec x y := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- **Rung 4a (substitution: first-order optimality ⇒ tight frame).**  Abstracted
over a *symmetric square root* `T` of `S` (`Tᵀ = T`, `T·T = S`, `T` invertible —
which exists for any SPD `S`): if `S` satisfies the first-order optimality identity
`∑ᵢ (1/⟪vᵢ,Svᵢ⟫)·vᵢvᵢᵀ = (m/d)·S⁻¹`, then the normalized images
`ûᵢ = (1/√⟪vᵢ,Svᵢ⟫)·(T vᵢ)` are in tight-frame position `∑ᵢ ûᵢûᵢᵀ = (m/d)·I`.

This is the back half of Forster's isotropic-position theorem: combined with rung 3
(existence of an optimal `S`) and rung 4b (`T = √S⋆`), it discharges the kernel.
Pure matrix algebra — no `sorry`, no carried socket. -/
theorem tightFrame_of_firstOrder
    {S T : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (hTsymm : Tᵀ = T) (hTT : T * T = S) (hTunit : IsUnit T.det)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0)
    (hLag : ∑ i, (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • Matrix.vecMulVec (v i) (v i)
              = ((m : ℝ) / d) • S⁻¹) :
    ∑ i, Matrix.vecMulVec
        ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
        ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
      = ((m : ℝ) / d) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hcpos : ∀ i, 0 < v i ⬝ᵥ (S *ᵥ v i) := fun i => quadForm_pos hS (hv i)
  have key : ∀ i,
      Matrix.vecMulVec
        ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
        ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
        = (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • (T * Matrix.vecMulVec (v i) (v i) * Tᵀ) := by
    intro i
    rw [vecMulVec_smul, vecMulVec_mulVec]
    congr 1
    rw [← mul_inv, Real.mul_self_sqrt (hcpos i).le]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  have pull :
      (∑ i, (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • (T * Matrix.vecMulVec (v i) (v i) * Tᵀ))
        = T * (∑ i, (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • Matrix.vecMulVec (v i) (v i)) * Tᵀ := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  rw [pull, hLag, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [hTsymm]
  have hSinv : S⁻¹ = T⁻¹ * T⁻¹ := by rw [← hTT, Matrix.mul_inv_rev]
  rw [hSinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv T hTunit, Matrix.one_mul,
    Matrix.nonsing_inv_mul T hTunit]

/-! ### Rung 3 (the variational crux): first-order optimality

The minimizer `S⋆` of the scale-invariant potential
`G(S) = F(S) - (m/d)·log det S` over SPD matrices satisfies `∇G(S⋆) = 0`, i.e. the
Lagrange identity `∑ᵢ vᵢvᵢᵀ/⟪vᵢ,S⋆vᵢ⟫ = (m/d)·S⋆⁻¹` that rung 4a consumes.  By the
variational method this comes from the directional derivative of `G` along every
line `t ↦ S⋆ + tΔ` vanishing at `t = 0`.

The **F-side** of that directional derivative is fully proved below
(`hasDerivAt_potential`): it needs only scalar calculus, since each summand
`log⟪vᵢ,(S+tΔ)vᵢ⟫` is `log` of an *affine* function of `t`.

The remaining ingredient is the **`log det` side**: `d/dt log det(S+tΔ)|₀ = tr(S⁻¹Δ)`
(Jacobi's formula).  Mathlib has the charpoly↔trace/det dictionary
(`Matrix.trace_eq_neg_charpoly_coeff`, `Matrix.det_eq_sign_charpoly_coeff`) but
**not** the derivative of `det` along a line.  That single fact — `HasDerivAt`
of `t ↦ det (S + t•Δ)` with derivative `det S · tr(S⁻¹Δ)` — is the genuine missing
Mathlib infrastructure for this rung (and a worthwhile standalone contribution).
It is deliberately **not** assumed here; rung 3 is left open at exactly that point
rather than socketed. -/

open Matrix in
/-- **Rung 3a (F-side, summand).** Along `t ↦ S + tΔ`, the potential summand
`log⟪vᵢ,Svᵢ⟫` has derivative `⟪vᵢ,Δvᵢ⟫ / ⟪vᵢ,Svᵢ⟫` at `t = 0` — `log` of an affine
function. -/
lemma hasDerivAt_logQuadForm {S Δ : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (v ⬝ᵥ ((S + t • Δ) *ᵥ v)))
      ((v ⬝ᵥ (Δ *ᵥ v)) / (v ⬝ᵥ (S *ᵥ v))) 0 := by
  have hinner : HasDerivAt (fun t : ℝ => v ⬝ᵥ ((S + t • Δ) *ᵥ v)) (v ⬝ᵥ (Δ *ᵥ v)) 0 := by
    have haffine : (fun t : ℝ => v ⬝ᵥ ((S + t • Δ) *ᵥ v))
        = (fun t : ℝ => (v ⬝ᵥ (S *ᵥ v)) + t * (v ⬝ᵥ (Δ *ᵥ v))) := by
      funext t
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [haffine]
    simpa using
      (((hasDerivAt_id (0 : ℝ)).mul_const (v ⬝ᵥ (Δ *ᵥ v))).const_add (v ⬝ᵥ (S *ᵥ v)))
  have hne : v ⬝ᵥ ((S + (0 : ℝ) • Δ) *ᵥ v) ≠ 0 := by
    rw [zero_smul, add_zero]; exact ne_of_gt (quadForm_pos hS hv)
  simpa using hinner.log hne

/-- **Rung 3a (F-side, full potential).** The directional derivative of the
log-potential `F(S) = ∑ᵢ log⟪vᵢ,Svᵢ⟫` along `t ↦ S + tΔ` at `t = 0` is
`∑ᵢ ⟪vᵢ,Δvᵢ⟫/⟪vᵢ,Svᵢ⟫`.  Fully proved (clean axioms, no sorry); this is the
non-`det` half of rung 3's first-order condition. -/
lemma hasDerivAt_potential {S Δ : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0) :
    HasDerivAt (fun t : ℝ => potential v (S + t • Δ))
      (∑ i, (v i ⬝ᵥ (Δ *ᵥ v i)) / (v i ⬝ᵥ (S *ᵥ v i))) 0 := by
  unfold potential
  exact HasDerivAt.fun_sum (fun i _ => hasDerivAt_logQuadForm hS (hv i))

#print axioms quadForm_pos
#print axioms vecMulVec_mulVec
#print axioms tightFrame_of_firstOrder
#print axioms hasDerivAt_potential

end PallLean.Paper93.DeepMath.PathB.ForsterIsotropic
