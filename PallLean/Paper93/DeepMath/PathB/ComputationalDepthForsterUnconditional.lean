import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterWiring

/-!
# Unconditional Forster: removing the general-position hypothesis

`forster_bound_of_genPos` (in `ComputationalDepthForsterWiring.lean`) proves the
Forster sign-rank lower bound for realizations *in general position*.  This file
removes that hypothesis by the classical **perturbation-to-general-position**
argument: any dimension-`d` realization can be nudged
`u_i ↦ u_i + t·z_i` along a reference moment curve `z` (a Vandermonde
configuration, itself in general position) so that:

* for all but finitely many `t`, the perturbed configuration is in general
  position (this file: `finite_singular_params`, `det_reference_ne_zero`);
* for `t` near `0` the sign pattern of the realization is preserved
  (a small, open condition);

and then `forster_bound_of_genPos` applies to the perturbed realization, which
has the *same* sign matrix `M`, dimension `d`, and bound.  No barrier: this is
bounded, classical genericity.

This file builds the genericity foundations; the sign-stability step and final
assembly are layered on top.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterUnconditional

open scoped BigOperators Matrix RealInnerProductSpace
open Forster ForsterIsotropic ForsterWiring Matrix Polynomial

variable {m' d n : ℕ}

/-- **Reference configuration is in general position.**  The moment curve
`z(j) = (j⁰, j¹, …, j^{d-1})` (here `z(j) i = (↑j)^i`) has every `d`-subset
linearly independent: the corresponding square matrix is a (transposed)
Vandermonde matrix on distinct nodes, hence has nonzero determinant. -/
theorem det_reference_ne_zero (e : Fin d → Fin (m' + 1)) (he : Function.Injective e) :
    (Matrix.of (fun (i k : Fin d) => (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det ≠ 0 := by
  have hinj : Function.Injective (fun k : Fin d => (((e k : ℕ) : ℝ))) := by
    intro a b hab
    apply he
    apply Fin.val_injective
    have hab' : ((e a : ℕ) : ℝ) = ((e b : ℕ) : ℝ) := hab
    exact_mod_cast hab'
  have hmat : (Matrix.of (fun (i k : Fin d) => (((e k : ℕ) : ℝ)) ^ (i : ℕ)))
      = (Matrix.vandermonde (fun k : Fin d => ((e k : ℕ) : ℝ)))ᵀ := by
    ext i k
    simp [Matrix.vandermonde, Matrix.transpose_apply]
  rw [hmat, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj

/-- **Per-subset genericity.**  For fixed vectors `u` and a reference `z` whose
`e`-submatrix is invertible, the set of perturbation parameters `t` for which the
perturbed `e`-submatrix becomes singular is finite.

Proof: writing `US`, `ZS` for the submatrices, `det(US + t·ZS) = t^d · Q(t⁻¹)`
for `t ≠ 0`, where `Q(s) := det(s·US + ZS)` is a polynomial with
`Q(0) = det ZS ≠ 0`, hence `Q ≠ 0` and has finitely many roots. -/
theorem finite_singular_params (u z : Fin (m' + 1) → (Fin d → ℝ))
    (e : Fin d → Fin (m' + 1))
    (hz : (Matrix.of (fun i k => z (e k) i)).det ≠ 0) :
    Set.Finite {t : ℝ | (Matrix.of (fun i k => u (e k) i + t * z (e k) i)).det = 0} := by
  set US : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i k => u (e k) i) with hUS
  set ZS : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i k => z (e k) i) with hZS
  -- the perturbed submatrix is `US + t • ZS`
  have hpert : ∀ t : ℝ, (Matrix.of (fun i k => u (e k) i + t * z (e k) i))
      = US + t • ZS := by
    intro t; ext i k
    simp only [hUS, hZS, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  -- the polynomial `Q(s) = det(s • US + ZS)`
  set Q : Polynomial ℝ :=
    (Matrix.of (fun i k => Polynomial.C (z (e k) i) + Polynomial.X * Polynomial.C (u (e k) i))).det
    with hQ
  have hQeval : ∀ s : ℝ, Q.eval s = (ZS + s • US).det := by
    intro s
    rw [hQ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Matrix.add_apply, Matrix.smul_apply, hUS, hZS, Matrix.of_apply, smul_eq_mul]
  have hQ0 : Q.eval 0 = ZS.det := by rw [hQeval]; simp
  have hQne : Q ≠ 0 := by
    intro h
    rw [h] at hQ0
    simp only [Polynomial.eval_zero] at hQ0
    exact hz hQ0.symm
  have hfin : Set.Finite {s : ℝ | Q.IsRoot s} := Polynomial.finite_setOf_isRoot hQne
  -- the singular `t` inject into `{0} ∪ (·⁻¹) '' (roots of Q)`
  apply Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) (hfin.image (·⁻¹)))
  intro t ht
  simp only [Set.mem_setOf_eq, hpert] at ht
  by_cases htz : t = 0
  · exact Or.inl htz
  · refine Or.inr ⟨t⁻¹, ?_, ?_⟩
    · -- `t⁻¹ ∈ {s | Q.IsRoot s}`
      have hscale : US + t • ZS = t • (t⁻¹ • US + ZS) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ htz, one_smul]
      rw [hscale, Matrix.det_smul, Fintype.card_fin] at ht
      have hQtInv : Q.eval t⁻¹ = (t⁻¹ • US + ZS).det := by
        rw [hQeval, add_comm ZS (t⁻¹ • US)]
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hQtInv]
      rcases mul_eq_zero.mp ht with hpow | hdet
      · exact absurd hpow (pow_ne_zero d htz)
      · exact hdet
    · exact inv_inv t

/-- **Genericity of general position.**  For fixed vectors `w`, the perturbation
`w_j ↦ w_j + t·(moment curve)_j` fails to be in general position for only
finitely many `t`: the bad set is the finite union, over the finitely many
injective `d`-tuples `e`, of the per-subset singular sets. -/
theorem finite_nonGenPos (w : Fin (m' + 1) → (Fin d → ℝ)) :
    Set.Finite {t : ℝ | ∃ e : Fin d → Fin (m' + 1), Function.Injective e ∧
      (Matrix.of (fun i k => w (e k) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det = 0} := by
  have hsub : {t : ℝ | ∃ e : Fin d → Fin (m' + 1), Function.Injective e ∧
        (Matrix.of (fun i k => w (e k) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det = 0}
      ⊆ ⋃ e ∈ {e : Fin d → Fin (m' + 1) | Function.Injective e},
          {t : ℝ | (Matrix.of (fun i k =>
            w (e k) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det = 0} := by
    rintro t ⟨e, he, hdet⟩
    exact Set.mem_biUnion he hdet
  refine Set.Finite.subset (Set.Finite.biUnion (Set.toFinite _) ?_) hsub
  intro e he
  exact finite_singular_params w (fun j i => (((j : ℕ) : ℝ)) ^ (i : ℕ)) e
    (det_reference_ne_zero e he)

/-- **Sign-stability of the perturbation.**  For `t` near `0`, the perturbed
realization `u_i ↦ u_i + t·z_i` keeps every sign inequality
`0 < sgn(M i j)·⟪u_i, w_j⟫` strict.  Each is an affine, continuous function of
`t`, strictly positive at `t = 0` (the original `sign_ok`), and there are
finitely many `(i,j)`. -/
theorem eventually_sign_ok {M : Fin (m' + 1) → Fin n → Bool} (R : UnitRealization M d)
    (zE : Fin (m' + 1) → EuclideanSpace ℝ (Fin d)) :
    ∀ᶠ t : ℝ in nhds 0,
      ∀ i j, 0 < sgn (M i j) * ⟪R.u i + t • zE i, R.w j⟫ := by
  have hpt : ∀ i j, ∀ᶠ t : ℝ in nhds 0,
      0 < sgn (M i j) * ⟪R.u i + t • zE i, R.w j⟫ := by
    intro i j
    have hcont : ContinuousAt
        (fun t : ℝ => sgn (M i j) * ⟪R.u i + t • zE i, R.w j⟫) 0 := by
      fun_prop
    have hpos0 : 0 < sgn (M i j) * ⟪R.u i + (0 : ℝ) • zE i, R.w j⟫ := by
      simp only [zero_smul, add_zero]; exact R.sign_ok i j
    exact hcont.eventually (eventually_gt_nhds hpos0)
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact hpt i j
