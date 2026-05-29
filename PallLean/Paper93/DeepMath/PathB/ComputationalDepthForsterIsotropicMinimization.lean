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

/-- A permutation of `Fin d` that fixes every index except possibly one fixes that
index too, hence is the identity (a permutation cannot move exactly one point). -/
private lemma perm_eq_one_of_fixes_compl {σ : Equiv.Perm (Fin d)} {i : Fin d}
    (h : ∀ j, j ≠ i → σ j = j) : σ = 1 := by
  ext k
  by_cases hk : k = i
  · by_cases hσk : σ k = k
    · simp [hσk, Equiv.Perm.one_apply]
    · have hki' : σ k ≠ i := by rw [← hk]; exact hσk
      exact absurd (σ.injective (h (σ k) hki')) hσk
  · simp [h k hk, Equiv.Perm.one_apply]

open Matrix in
/-- **Rung 3b — Jacobi's formula at the identity.**  `d/dt det(1 + tM)|₀ = tr M`.
This is the matrix-calculus fact Mathlib lacks.  Proof: in the Leibniz expansion
`det(1+tM) = ∑_σ sgn σ ∏ᵢ (1+tM)(σ i) i`, differentiate the product of affine
factors; every non-identity permutation moves at least two indices, so its
contribution has a vanishing zero-order factor at `t=0`, leaving only the identity
term `∑ᵢ Mᵢᵢ = tr M`. -/
lemma hasDerivAt_det_one_add_smul (M : Matrix (Fin d) (Fin d) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  classical
  have key : HasDerivAt (fun t : ℝ => (1 + t • M).det)
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + (0 : ℝ) • M) (σ j) j) • M (σ i) i)) 0 := by
    have hfun : (fun t : ℝ => (1 + t • M).det)
        = (fun t : ℝ => ∑ σ : Equiv.Perm (Fin d),
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (1 + t • M) (σ i) i) := by
      funext t; rw [Matrix.det_apply']
    rw [hfun]
    apply HasDerivAt.fun_sum
    intro σ _
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_finset_prod
    intro i _
    have hentry : (fun t : ℝ => (1 + t • M) (σ i) i)
        = fun t : ℝ => (1 : Matrix (Fin d) (Fin d) ℝ) (σ i) i + t * M (σ i) i := by
      funext t; rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hentry]
    simpa using
      (((hasDerivAt_id (0 : ℝ)).mul_const (M (σ i) i)).const_add
        ((1 : Matrix (Fin d) (Fin d) ℝ) (σ i) i))
  have hval : (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + (0 : ℝ) • M) (σ j) j) • M (σ i) i))
        = M.trace := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin d))]
    · -- identity term equals the trace
      have hinner : (∑ i, (∏ j ∈ Finset.univ.erase i,
              (1 + (0 : ℝ) • M) ((1 : Equiv.Perm (Fin d)) j) j) •
            M ((1 : Equiv.Perm (Fin d)) i) i) = ∑ i, M i i := by
        apply Finset.sum_congr rfl
        intro i _
        have hp : (∏ j ∈ Finset.univ.erase i,
            (1 + (0 : ℝ) • M) ((1 : Equiv.Perm (Fin d)) j) j) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          simp
        rw [hp, one_smul, Equiv.Perm.one_apply]
      rw [Equiv.Perm.sign_one]
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [hinner]
      simp [Matrix.trace, Matrix.diag]
    · intro σ _ hσ
      have hinner0 : (∑ i, (∏ j ∈ Finset.univ.erase i,
          (1 + (0 : ℝ) • M) (σ j) j) • M (σ i) i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hp0 : (∏ j ∈ Finset.univ.erase i, (1 + (0 : ℝ) • M) (σ j) j) = 0 := by
          obtain ⟨j₀, hj₀i, hj₀⟩ : ∃ j₀, j₀ ≠ i ∧ σ j₀ ≠ j₀ := by
            by_contra hcon
            push_neg at hcon
            exact hσ (perm_eq_one_of_fixes_compl hcon)
          apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj₀i, Finset.mem_univ _⟩)
          simp [hj₀]
        rw [hp0, zero_smul]
      rw [hinner0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rwa [hval] at key

open Matrix in
/-- **Rung 3b′ — Jacobi along a line at an SPD point.**
`d/dt log det(S + tΔ)|₀ = tr(S⁻¹Δ)`, for `S` positive definite.  Reduces to rung 3b
via `S + tΔ = S·(1 + t·S⁻¹Δ)` and the `log` chain rule. -/
lemma hasDerivAt_logdet {S Δ : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    HasDerivAt (fun t : ℝ => Real.log (S + t • Δ).det) (S⁻¹ * Δ).trace 0 := by
  have hSdet : IsUnit S.det := hS.det_pos.ne'.isUnit
  have hfac : (fun t : ℝ => (S + t • Δ).det)
      = (fun t : ℝ => S.det * (1 + t • (S⁻¹ * Δ)).det) := by
    funext t
    rw [← Matrix.det_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, mul_smul_comm, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]
  have hinner : HasDerivAt (fun t : ℝ => (S + t • Δ).det) (S.det * (S⁻¹ * Δ).trace) 0 := by
    rw [hfac]
    exact (hasDerivAt_det_one_add_smul (S⁻¹ * Δ)).const_mul S.det
  have hne : (S + (0 : ℝ) • Δ).det ≠ 0 := by
    rw [zero_smul, add_zero]; exact hSdet.ne_zero
  have hlog := hinner.log hne
  simp only [zero_smul, add_zero] at hlog
  rwa [mul_div_cancel_left₀ _ hSdet.ne_zero] at hlog

/-- **Rung 3d core (extraction).** A symmetric real matrix with `tr(A·A) = 0` is
zero: `tr(A·A) = ∑ᵢₖ Aᵢₖ²` is a sum of squares.  This converts the vanishing of
the directional derivative in *every* symmetric direction (taking `Δ = A`, the
gradient matrix) into the Lagrange matrix equation. -/
lemma eq_zero_of_symm_trace_sq {A : Matrix (Fin d) (Fin d) ℝ} (hsymm : Aᵀ = A)
    (h : (A * A).trace = 0) : A = 0 := by
  have hsum : (A * A).trace = ∑ i, ∑ k, A i k * A i k := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hik : A k i = A i k := by
      have hc := congrFun (congrFun hsymm i) k
      rwa [Matrix.transpose_apply] at hc
    rw [hik]
  rw [hsum] at h
  have hnn : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ ∑ k, A i k * A i k :=
    fun i _ => Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  ext i k
  rw [Matrix.zero_apply]
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_self_nonneg (A i k))).mp (hzero i (Finset.mem_univ i))
  exact mul_self_eq_zero.mp (h2 k (Finset.mem_univ k))

/-- The scale-invariant potential `G(S) = F(S) - (m/d)·log det S`, whose
*unconstrained* minimizer over SPD matrices satisfies the Lagrange identity
(minimizing `F` on `{det = 1}` ⟺ minimizing `G` freely). -/
noncomputable def potentialG (v : Fin m → (Fin d → ℝ)) (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  potential v S - ((m : ℝ) / d) * Real.log S.det

open Matrix in
/-- Directional derivative of `G` along `t ↦ S + tΔ` at `t = 0`, combining rung 3a
and rung 3b′. -/
lemma hasDerivAt_potentialG {S Δ : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0) :
    HasDerivAt (fun t : ℝ => potentialG v (S + t • Δ))
      ((∑ i, (v i ⬝ᵥ (Δ *ᵥ v i)) / (v i ⬝ᵥ (S *ᵥ v i)))
        - ((m : ℝ) / d) * (S⁻¹ * Δ).trace) 0 := by
  unfold potentialG
  exact (hasDerivAt_potential hS hv).sub ((hasDerivAt_logdet hS).const_mul ((m : ℝ) / d))

open Matrix in
/-- The quadratic form as a trace pairing: `v ⬝ᵥ (Δ *ᵥ v) = tr(Δ · v vᵀ)`. -/
lemma dotProduct_mulVec_eq_trace (Δ : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Δ *ᵥ v) = (Δ * Matrix.vecMulVec v v).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

open Matrix in
/-- **Rung 3 (variational first-order optimality).**  If the SPD matrix `S` is a
local minimizer of the scale-invariant potential `G = potentialG v`, then it
satisfies the Lagrange identity `∑ᵢ vᵢvᵢᵀ/⟪vᵢ,Svᵢ⟫ = (m/d)·S⁻¹` consumed by rung
4a.  Proof: the directional derivative of `G` vanishes in every symmetric direction
(`IsLocalMin`), equals `tr(Δ·A)` for the gradient matrix `A`, and `A` is symmetric;
taking `Δ = A` gives `tr(A·A) = 0`, hence `A = 0`. -/
theorem firstOrder_of_isLocalMin {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0)
    (hmin : IsLocalMin (potentialG v) S) :
    ∑ i, (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • Matrix.vecMulVec (v i) (v i) = ((m : ℝ) / d) • S⁻¹ := by
  rw [← sub_eq_zero]
  set A : Matrix (Fin d) (Fin d) ℝ :=
    (∑ i, (v i ⬝ᵥ (S *ᵥ v i))⁻¹ • Matrix.vecMulVec (v i) (v i)) - ((m : ℝ) / d) • S⁻¹ with hA
  -- `S⁻¹` and hence `A` are symmetric
  have hSinv_symm : (S⁻¹)ᵀ = S⁻¹ := by
    have h : (S⁻¹)ᴴ = S⁻¹ := (hS.inv).isHermitian
    calc (S⁻¹)ᵀ = (S⁻¹)ᴴ := by
            ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
      _ = S⁻¹ := h
  have hAsymm : Aᵀ = A := by
    rw [hA, Matrix.transpose_sub, Matrix.transpose_smul, hSinv_symm]
    congr 1
    rw [Matrix.transpose_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  -- the directional derivative equals `tr(Δ · A)`
  have hDtrace : ∀ Δ : Matrix (Fin d) (Fin d) ℝ,
      ((∑ i, (v i ⬝ᵥ (Δ *ᵥ v i)) / (v i ⬝ᵥ (S *ᵥ v i)))
        - ((m : ℝ) / d) * (S⁻¹ * Δ).trace) = (Δ * A).trace := by
    intro Δ
    rw [hA, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sum, Matrix.trace_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, ← dotProduct_mulVec_eq_trace,
        div_eq_inv_mul]
    · rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, trace_mul_comm S⁻¹ Δ]
  -- vanishing in every symmetric direction
  have hvanish : ∀ Δ : Matrix (Fin d) (Fin d) ℝ, Δᵀ = Δ → (Δ * A).trace = 0 := by
    intro Δ _
    rw [← hDtrace Δ]
    have hloc : IsLocalMin (fun t : ℝ => potentialG v (S + t • Δ)) 0 := by
      have hg : Filter.Tendsto (fun t : ℝ => S + t • Δ) (nhds (0 : ℝ)) (nhds S) := by
        have hc : Continuous (fun t : ℝ => S + t • Δ) := by fun_prop
        simpa using hc.tendsto 0
      exact (hg.eventually hmin).mono (fun t ht => by simpa using ht)
    exact hloc.hasDerivAt_eq_zero (hasDerivAt_potentialG hS hv)
  exact eq_zero_of_symm_trace_sq hAsymm (hvanish A hAsymm)

/-! ### Rung 2 (existence of a minimizer): foundation

The remaining lift: produce the `IsLocalMin (potentialG v) S⋆` hypothesis that rung 3
consumes, by minimizing `G` over SPD matrices.  The honest hard core is *coercivity*
(`G → +∞` as `S` degenerates), which rests on a generalized-Hadamard / Cauchy–Binet
estimate `∏ᵢ⟪vᵢ,Svᵢ⟫ ≥ c·det(S)^{m/d}` from the spanning hypothesis — a substantial
standalone inequality **not in Mathlib** — together with compactness of sublevel sets
in SPD-matrix space.  That is genuinely the largest single analytic piece of the whole
`∃T` grind.

Landed here: the *continuity* foundation (the easy half of the extreme-value-theorem
route), fully proved. -/

open Matrix in
/-- `potentialG v` is continuous at every positive-definite matrix (its summands are
`log` of strictly-positive continuous functions; `log det` likewise). -/
lemma continuousAt_potentialG {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0) :
    ContinuousAt (potentialG v) S := by
  have hquad : ∀ i, ContinuousAt
      (fun T : Matrix (Fin d) (Fin d) ℝ => v i ⬝ᵥ (T *ᵥ v i)) S :=
    fun i => (continuous_const.dotProduct
      (continuous_id.matrix_mulVec continuous_const)).continuousAt
  have hdet : ContinuousAt (fun T : Matrix (Fin d) (Fin d) ℝ => T.det) S :=
    (Continuous.matrix_det continuous_id).continuousAt
  unfold potentialG
  refine ContinuousAt.sub ?_ ?_
  · exact tendsto_finset_sum _ (fun i _ => (hquad i).log (quadForm_pos hS (hv i)).ne')
  · exact (hdet.log hS.det_pos.ne').const_mul _

open Matrix in
/-- **AM–GM / trace-Hadamard kernel (rung 2 coercivity foundation).** For a
positive-semidefinite real `d×d` matrix with `d > 0`, `det M ≤ (tr M / d)^d`.
This is the eigenvalue arithmetic-mean–geometric-mean bound (`det = ∏ λᵢ`,
`tr = ∑ λᵢ`, AM–GM), and the kernel from which Hadamard's `det M ≤ ∏ᵢ Mᵢᵢ` follows
by conjugating to unit diagonal — the inequality that powers the spanning-based
coercivity of the Forster potential. -/
lemma det_le_trace_div_pow (hd : 0 < d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) : M.det ≤ (M.trace / d) ^ d := by
  classical
  have hdℝ : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  set lam : Fin d → ℝ := hM.1.eigenvalues with hlam
  have hev : ∀ i, 0 ≤ lam i := fun i => hM.eigenvalues_nonneg i
  have hdet : M.det = ∏ i, lam i := by simpa [hlam] using hM.1.det_eq_prod_eigenvalues
  have htr : M.trace = ∑ i, lam i := by simpa [hlam] using hM.1.trace_eq_sum_eigenvalues
  rw [hdet, htr]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0 : ℝ) ≤ (d : ℝ)⁻¹ :=
    fun i _ => by positivity
  have hw' : ∑ _i : Fin d, (d : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (d : ℝ)⁻¹) lam hw hw'
    (fun i _ => hev i)
  rw [Real.finset_prod_rpow _ _ (fun i _ => hev i)] at hgm
  have hrhs : ∑ i : Fin d, (d : ℝ)⁻¹ * lam i = (∑ i, lam i) / d := by
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rw [hrhs] at hgm
  have hprodnn : 0 ≤ ∏ i, lam i := Finset.prod_nonneg (fun i _ => hev i)
  calc ∏ i, lam i = ((∏ i, lam i) ^ (d : ℝ)⁻¹) ^ d := by
          rw [← Real.rpow_natCast ((∏ i, lam i) ^ (d : ℝ)⁻¹) d, ← Real.rpow_mul hprodnn,
            inv_mul_cancel₀ hdℝ, Real.rpow_one]
    _ ≤ ((∑ i, lam i) / d) ^ d := pow_le_pow_left₀ (Real.rpow_nonneg hprodnn _) hgm d

open Matrix in
/-- **Hadamard's determinant inequality** (PD case): `det M ≤ ∏ᵢ Mᵢᵢ`.  Conjugate
to unit diagonal `N = D M D` with `D = diag(Mᵢᵢ^{-1/2})`: then `Nᵢᵢ = 1`, `tr N = d`,
`det N = (∏ᵢ Mᵢᵢ)⁻¹ · det M`, and the trace-Hadamard kernel gives `det N ≤ 1`. -/
lemma det_le_prod_diag (hd : 0 < d) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    M.det ≤ ∏ i, M i i := by
  classical
  have hMii : ∀ i, 0 < M i i := by
    intro i
    have hx : (Pi.single i (1 : ℝ) : Fin d → ℝ) ≠ 0 := by
      intro h
      have hi := congrFun h i
      simp only [Pi.single_eq_same, Pi.zero_apply] at hi
      exact one_ne_zero hi
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
    simpa [Matrix.mulVec_single, single_dotProduct, dotProduct_single] using hpos
  have hprodpos : 0 < ∏ i, M i i := Finset.prod_pos (fun i _ => hMii i)
  set dg : Fin d → ℝ := fun i => (Real.sqrt (M i i))⁻¹ with hdg
  have hsqrtpos : ∀ i, 0 < Real.sqrt (M i i) := fun i => Real.sqrt_pos.mpr (hMii i)
  -- N = (diagonal dg) * M * (diagonal dg), positive semidefinite
  have hDH : (Matrix.diagonal dg)ᴴ = Matrix.diagonal dg := by
    simp
  have hN : (Matrix.diagonal dg * M * Matrix.diagonal dg).PosSemidef := by
    have := hM.posSemidef.conjTranspose_mul_mul_same (Matrix.diagonal dg)
    rwa [hDH] at this
  -- diagonal entries of N are 1
  have hNdiag : ∀ i, (Matrix.diagonal dg * M * Matrix.diagonal dg) i i = 1 := by
    intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hdg]
    rw [mul_right_comm, ← mul_inv, Real.mul_self_sqrt (hMii i).le, inv_mul_cancel₀ (hMii i).ne']
  -- trace N = d
  have hNtrace : (Matrix.diagonal dg * M * Matrix.diagonal dg).trace = (d : ℝ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hNdiag]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- ∏ dg · ∏ dg = (∏ Mᵢᵢ)⁻¹
  have hkey : (∏ i, dg i) * (∏ i, dg i) = (∏ i, M i i)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hdg]
    rw [← mul_inv, Real.mul_self_sqrt (hMii i).le]
  -- det N = (∏ Mᵢᵢ)⁻¹ · det M
  have hNdet : (Matrix.diagonal dg * M * Matrix.diagonal dg).det = (∏ i, M i i)⁻¹ * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      show (∏ i, dg i) * M.det * (∏ i, dg i) = (∏ i, dg i) * (∏ i, dg i) * M.det by ring, hkey]
  -- trace-Hadamard kernel: det N ≤ (tr N / d)^d = 1
  have hker := det_le_trace_div_pow hd hN
  rw [hNtrace, hNdet, div_self (Nat.cast_ne_zero.mpr hd.ne'), one_pow] at hker
  -- (∏ Mᵢᵢ)⁻¹ · det M ≤ 1 ⇒ det M ≤ ∏ Mᵢᵢ
  have hfin := mul_le_mul_of_nonneg_left hker hprodpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ hprodpos.ne', one_mul, mul_one] at hfin

open Matrix in
/-- **Basis-subset lower bound** (Hadamard applied to `BᴴSB`).  For invertible `B`
and positive-definite `S`, `(det B)²·det S ≤ ∏ₖ (Bᴴ S B)ₖₖ`.  For a real basis
matrix `B`, `Bᴴ = Bᵀ` and `(BᵀSB)ₖₖ = ⟪columnₖ B, S·columnₖ B⟫`, so this is the
`∏ₖ ⟪vₖ,Svₖ⟫ ≥ det(B)²·det S` lower bound used in the coercivity argument. -/
lemma det_sq_mul_det_le_prod_diag (hd : 0 < d) {B S : Matrix (Fin d) (Fin d) ℝ}
    (hB : IsUnit B.det) (hS : S.PosDef) :
    B.det ^ 2 * S.det ≤ ∏ k, (Bᴴ * S * B) k k := by
  have hinj : Function.Injective B.mulVec := by
    intro x y h
    have h2 : B⁻¹ *ᵥ (B *ᵥ x) = B⁻¹ *ᵥ (B *ᵥ y) := by rw [h]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB,
      Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hBSB : (Bᴴ * S * B).PosDef := hS.conjTranspose_mul_mul_same hinj
  have hH := det_le_prod_diag hd hBSB
  have hdet : (Bᴴ * S * B).det = B.det ^ 2 * S.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial]
    ring
  rwa [hdet] at hH

open Matrix in
open scoped MatrixOrder in
/-- **Rung 4b — symmetric square root.** Every positive-definite real matrix has a
symmetric, invertible square root (`CFC.sqrt`), supplying the `T` that rung 4a
consumes. -/
lemma exists_symm_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    ∃ T : Matrix (Fin d) (Fin d) ℝ, Tᵀ = T ∧ T * T = S ∧ IsUnit T.det := by
  have hTpd : (CFC.sqrt S).PosDef := hS.isStrictlyPositive.sqrt.posDef
  have hmul : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef)
  refine ⟨CFC.sqrt S, ?_, hmul, hTpd.det_pos.ne'.isUnit⟩
  have h : (CFC.sqrt S)ᴴ = CFC.sqrt S := hTpd.isHermitian
  calc (CFC.sqrt S)ᵀ = (CFC.sqrt S)ᴴ := by
        ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    _ = CFC.sqrt S := h

open Matrix in
/-- **`∃T` assembled, modulo minimizer existence.**  If `G = potentialG v` attains a
local minimum at an SPD `S`, then the isotropic transform exists: there is an
invertible `T` putting the normalised images `ûᵢ = (1/√⟪vᵢ,Svᵢ⟫)·(T vᵢ)` into
tight-frame position `∑ᵢ ûᵢûᵢᵀ = (m/d)·I`.  This composes rung 3 (`firstOrder`),
rung 4b (`√S`), and rung 4a (`tightFrame`).  The *only* remaining gap to an
unconditional `∃T` is discharging the `IsLocalMin` hypothesis — i.e. coercivity
(under general position) + sublevel-set compactness, the honest analytic wall. -/
theorem exists_isotropic_of_isLocalMin {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (hv : ∀ i, v i ≠ 0) (hmin : IsLocalMin (potentialG v) S) :
    ∃ T : Matrix (Fin d) (Fin d) ℝ, IsUnit T.det ∧
      ∑ i, Matrix.vecMulVec ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
                            ((Real.sqrt (v i ⬝ᵥ (S *ᵥ v i)))⁻¹ • (T *ᵥ v i))
        = ((m : ℝ) / d) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  obtain ⟨T, hTsymm, hTT, hTunit⟩ := exists_symm_sqrt hS
  exact ⟨T, hTunit,
    tightFrame_of_firstOrder hS hTsymm hTT hTunit hv (firstOrder_of_isLocalMin hS hv hmin)⟩

open Matrix in
/-- **Rung 2 compactness foundation: `PosSemidef` is closed.**  The set of
positive-semidefinite matrices is the intersection of the closed Hermitian locus
`{M | Mᴴ = M}` with the closed half-spaces `{M | 0 ≤ ⟪x, Mx⟫}` over all `x`. -/
lemma isClosed_posSemidef :
    IsClosed {M : Matrix (Fin d) (Fin d) ℝ | M.PosSemidef} := by
  have hset : {M : Matrix (Fin d) (Fin d) ℝ | M.PosSemidef}
      = {M | Mᴴ = M} ∩ ⋂ x : Fin d → ℝ, {M | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]
  refine IsClosed.inter (isClosed_eq (Continuous.matrix_conjTranspose continuous_id)
    continuous_id) (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

open Matrix in
/-- **Rung 2 compactness: a trace-bounded PSD slice is compact.**  `{M : PosSemidef,
tr M ≤ R}` is compact — closed (PSD closed ∩ trace ≤ R) and contained in the
entrywise box `[-R,R]^{d×d}` (compact by Tychonoff): diagonal entries lie in `[0,R]`,
and off-diagonal entries satisfy `Mᵢⱼ² ≤ Mᵢᵢ·Mⱼⱼ ≤ R²` from the `2×2` principal
minor being PSD.  The compact domain on which the extreme value theorem runs once
coercivity confines the minimizer. -/
lemma isCompact_posSemidef_trace_le (R : ℝ) :
    IsCompact {M : Matrix (Fin d) (Fin d) ℝ | M.PosSemidef ∧ M.trace ≤ R} := by
  have hboxcompact : IsCompact {M : Matrix (Fin d) (Fin d) ℝ | ∀ i j, M i j ∈ Set.Icc (-R) R} := by
    have hbox : {M : Matrix (Fin d) (Fin d) ℝ | ∀ i j, M i j ∈ Set.Icc (-R) R}
        = Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (-R) R)) := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [hbox]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hclosed : IsClosed {M : Matrix (Fin d) (Fin d) ℝ | M.PosSemidef ∧ M.trace ≤ R} :=
    IsClosed.inter isClosed_posSemidef
      (isClosed_le (Continuous.matrix_trace continuous_id) continuous_const)
  refine hboxcompact.of_isClosed_subset hclosed ?_
  rintro M ⟨hPSD, htr⟩ i j
  rw [Set.mem_Icc]
  have htreq : M.trace = ∑ k, M k k := by rw [Matrix.trace]; rfl
  have hdiagnn : ∀ k, 0 ≤ M k k := fun k => hPSD.diag_nonneg
  have hdiagle : ∀ k, M k k ≤ R := fun k =>
    calc M k k ≤ ∑ l, M l l :=
          Finset.single_le_sum (fun l _ => hdiagnn l) (Finset.mem_univ k)
      _ = M.trace := htreq.symm
      _ ≤ R := htr
  have hRnn : 0 ≤ R := le_trans (hdiagnn i) (hdiagle i)
  have hdet : 0 ≤ (M.submatrix ![i, j] ![i, j]).det := (hPSD.submatrix ![i, j]).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hsymm : M j i = M i j := by
    have h2 := congrFun (congrFun hPSD.1 i) j
    rwa [Matrix.conjTranspose_apply, star_trivial] at h2
  rw [hsymm] at hdet
  have hsq : M i j * M i j ≤ R * R :=
    le_trans (by linarith) (mul_le_mul (hdiagle i) (hdiagle j) (hdiagnn j) hRnn)
  constructor
  · nlinarith [hsq, sq_nonneg (M i j + R)]
  · nlinarith [hsq, sq_nonneg (M i j - R)]

open Matrix in
/-- Quadratic form of a rank-one outer product: `y ⬝ᵥ (vvᵀ *ᵥ y) = (v ⬝ᵥ y)²`. -/
lemma dotProduct_vecMulVec_mulVec (a y : Fin d → ℝ) :
    y ⬝ᵥ (Matrix.vecMulVec a a *ᵥ y) = (a ⬝ᵥ y) * (a ⬝ᵥ y) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

open Matrix in
/-- **Rung 2 sphere-`δ`: spanning ⇒ `∑ᵢ vᵢvᵢᵀ` is positive definite.**  The quadratic
form `y ⬝ᵥ ((∑ᵢ vᵢvᵢᵀ) *ᵥ y) = ∑ᵢ (vᵢ ⬝ᵥ y)²` vanishes only when `y ⊥ vᵢ` for all `i`,
i.e. `y ⊥ span = ⊤`, forcing `y = 0`.  Its least eigenvalue is the coercivity
constant used in the blow-up bound. -/
lemma posDef_sum_vecMulVec_of_span {v : Fin m → (Fin d → ℝ)}
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    (∑ i, Matrix.vecMulVec (v i) (v i)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- Hermitian
    show (∑ i, Matrix.vecMulVec (v i) (v i))ᴴ = ∑ i, Matrix.vecMulVec (v i) (v i)
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.conjTranspose_vecMulVec]
    simp
  · intro y hy
    have hstar : star y = y := by funext i; exact star_trivial _
    rw [hstar, Matrix.sum_mulVec, dotProduct_sum]
    have hcalc : (∑ i, y ⬝ᵥ (Matrix.vecMulVec (v i) (v i) *ᵥ y))
        = ∑ i, (v i ⬝ᵥ y) * (v i ⬝ᵥ y) := by
      apply Finset.sum_congr rfl
      intro i _
      exact dotProduct_vecMulVec_mulVec (v i) y
    rw [hcalc]
    -- sum of squares > 0 since not all vᵢ ⬝ᵥ y vanish (else y = 0)
    apply Finset.sum_pos' (fun i _ => mul_self_nonneg _)
    by_contra hcon
    push_neg at hcon
    apply hy
    have hvy : ∀ i, v i ⬝ᵥ y = 0 := by
      intro i
      exact mul_self_eq_zero.mp
        (le_antisymm (hcon i (Finset.mem_univ i)) (mul_self_nonneg _))
    have hortho : ∀ w ∈ Submodule.span ℝ (Set.range v), w ⬝ᵥ y = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hvy i
      | zero => simp
      | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]
    have hyspan : y ∈ Submodule.span ℝ (Set.range v) := hspan ▸ Submodule.mem_top
    exact dotProduct_self_eq_zero.mp (hortho y hyspan)

open Matrix in
/-- **Per-subset log bound** (the averaging's input).  For an index tuple `e` whose
selected vectors form an invertible matrix `B` (columns `v(e j)`) and are nonzero,
`log(det(B)²·det S) ≤ ∑ₖ log⟪v(e k), S v(e k)⟫` — the log of Hadamard applied to `BᴴSB`. -/
lemma log_det_le_sum_log_quadForm {S : Matrix (Fin d) (Fin d) ℝ} (hd : 0 < d) (hS : S.PosDef)
    {v : Fin m → (Fin d → ℝ)} (e : Fin d → Fin m) (hne : ∀ k, v (e k) ≠ 0)
    (hB : IsUnit (Matrix.of (fun i j => v (e j) i) : Matrix (Fin d) (Fin d) ℝ).det) :
    Real.log ((Matrix.of (fun i j => v (e j) i) : Matrix (Fin d) (Fin d) ℝ).det ^ 2 * S.det)
      ≤ ∑ k, Real.log (v (e k) ⬝ᵥ (S *ᵥ v (e k))) := by
  set B := (Matrix.of (fun i j => v (e j) i) : Matrix (Fin d) (Fin d) ℝ) with hBdef
  have hentry : ∀ k, (Bᴴ * S * B) k k = v (e k) ⬝ᵥ (S *ᵥ v (e k)) := by
    intro k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, dotProduct,
      Matrix.mulVec, hBdef, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hbound := det_sq_mul_det_le_prod_diag hd hB hS
  rw [show (∏ k, (Bᴴ * S * B) k k) = ∏ k, v (e k) ⬝ᵥ (S *ᵥ v (e k)) from
    Finset.prod_congr rfl (fun k _ => hentry k)] at hbound
  have hposq : ∀ k, 0 < v (e k) ⬝ᵥ (S *ᵥ v (e k)) := fun k => quadForm_pos hS (hne k)
  have hdetpos : 0 < B.det ^ 2 * S.det :=
    mul_pos (by rw [pow_two]; exact mul_self_pos.mpr hB.ne_zero) hS.det_pos
  calc Real.log (B.det ^ 2 * S.det)
      ≤ Real.log (∏ k, v (e k) ⬝ᵥ (S *ᵥ v (e k))) := Real.log_le_log hdetpos hbound
    _ = ∑ k, Real.log (v (e k) ⬝ᵥ (S *ᵥ v (e k))) :=
        Real.log_prod (fun k _ => (hposq k).ne')

open Matrix in
/-- **Rung 2 averaging: `F` is bounded below** (on the `det = 1` slice, under general
position).  Summing the per-subset bound over the `m` cyclic shifts `e_s k = s + k`
— each index hit exactly `d` times (`Equiv.addRight` reindexing, no fiber-counting) —
gives `(1/d)·∑_s log(det B_s²) ≤ ∑ᵢ log⟪vᵢ,Svᵢ⟫`, a constant lower bound independent
of `S`. -/
lemma sum_log_quadForm_lower_bound (hd : 0 < d) (hdm : d ≤ m)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (hdet1 : S.det = 1)
    {v : Fin m → (Fin d → ℝ)} (hne : ∀ i, v i ≠ 0)
    (hgp : ∀ s : Fin m, IsUnit
      ((Matrix.of (fun i k => v (s + Fin.castLE hdm k) i) : Matrix (Fin d) (Fin d) ℝ)).det) :
    (1 / (d : ℝ)) * ∑ s : Fin m,
        Real.log ((Matrix.of (fun i k => v (s + Fin.castLE hdm k) i) :
          Matrix (Fin d) (Fin d) ℝ).det ^ 2)
      ≤ ∑ i, Real.log (v i ⬝ᵥ (S *ᵥ v i)) := by
  haveI : NeZero m := ⟨by omega⟩
  set g : Fin m → ℝ := fun i => Real.log (v i ⬝ᵥ (S *ᵥ v i)) with hg
  -- per-shift bound
  have hshift : ∀ s : Fin m,
      Real.log ((Matrix.of (fun i k => v (s + Fin.castLE hdm k) i) :
        Matrix (Fin d) (Fin d) ℝ).det ^ 2)
        ≤ ∑ k : Fin d, g (s + Fin.castLE hdm k) := by
    intro s
    have := log_det_le_sum_log_quadForm hd hS (v := v) (fun k => s + Fin.castLE hdm k)
      (fun k => hne _) (hgp s)
    rwa [hdet1, mul_one] at this
  -- counting: each index hit d times
  have hcount : (∑ s : Fin m, ∑ k : Fin d, g (s + Fin.castLE hdm k)) = (d : ℝ) * ∑ i, g i := by
    rw [Finset.sum_comm]
    rw [show (∑ k : Fin d, ∑ s : Fin m, g (s + Fin.castLE hdm k))
        = ∑ _k : Fin d, ∑ i : Fin m, g i from
      Finset.sum_congr rfl (fun k _ => Equiv.sum_comp (Equiv.addRight (Fin.castLE hdm k)) g)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- combine
  have hsum : (∑ s : Fin m, Real.log ((Matrix.of (fun i k => v (s + Fin.castLE hdm k) i) :
        Matrix (Fin d) (Fin d) ℝ).det ^ 2)) ≤ (d : ℝ) * ∑ i, g i := by
    calc (∑ s : Fin m, Real.log ((Matrix.of (fun i k => v (s + Fin.castLE hdm k) i) :
            Matrix (Fin d) (Fin d) ℝ).det ^ 2))
        ≤ ∑ s : Fin m, ∑ k : Fin d, g (s + Fin.castLE hdm k) :=
          Finset.sum_le_sum (fun s _ => hshift s)
      _ = (d : ℝ) * ∑ i, g i := hcount
  rw [one_div, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < d)]
  linarith [hsum]

open Matrix in
/-- **Rayleigh lower bound** (rung 2 blow-up input).  A positive-definite `V` has a
uniform coercivity constant: `∃ δ > 0, ∀ y, δ·(y⬝ᵥy) ≤ y⬝ᵥ(V*ᵥy)`.  Proof by sphere
compactness — `δ = min` of the (continuous, positive) quadratic form over the
compact unit sphere `{y | y⬝ᵥy = 1}` — then homogeneity.  No spectral theorem. -/
lemma exists_quadForm_lower_bound (hd : 0 < d) {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin d → ℝ, δ * (y ⬝ᵥ y) ≤ y ⬝ᵥ (V *ᵥ y) := by
  classical
  have hfcont : Continuous (fun y : Fin d → ℝ => y ⬝ᵥ (V *ᵥ y)) :=
    Continuous.dotProduct continuous_id (continuous_const.matrix_mulVec continuous_id)
  have hKclosed : IsClosed {y : Fin d → ℝ | y ⬝ᵥ y = 1} :=
    isClosed_eq (Continuous.dotProduct continuous_id continuous_id) continuous_const
  have hKsub : {y : Fin d → ℝ | y ⬝ᵥ y = 1} ⊆ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1) := by
    intro y hy i _
    rw [Set.mem_Icc]
    have hle : y i * y i ≤ y ⬝ᵥ y :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (y j)) (Finset.mem_univ i)
    rw [hy] at hle
    constructor <;> nlinarith [hle]
  have hKcompact : IsCompact {y : Fin d → ℝ | y ⬝ᵥ y = 1} :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hKclosed hKsub
  have hne : {y : Fin d → ℝ | y ⬝ᵥ y = 1}.Nonempty := by
    refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq]
  obtain ⟨y₀, hy₀K, hy₀min⟩ := hKcompact.exists_isMinOn hne hfcont.continuousOn
  refine ⟨y₀ ⬝ᵥ (V *ᵥ y₀), quadForm_pos hV ?_, ?_⟩
  · intro hzero; rw [hzero] at hy₀K; simp at hy₀K
  · intro y
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · have hpos : 0 < y ⬝ᵥ y := by
        rcases lt_or_eq_of_le (Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i)) :
            (0 : ℝ) ≤ y ⬝ᵥ y) with h | h
        · exact h
        · exact absurd (dotProduct_self_eq_zero.mp h.symm) hy0
      set r := Real.sqrt (y ⬝ᵥ y) with hr
      have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
      have hr2 : r * r = y ⬝ᵥ y := Real.mul_self_sqrt hpos.le
      have hyhatK : (r⁻¹ • y) ⬝ᵥ (r⁻¹ • y) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
        rw [← hr2]; field_simp
      have hfyhat : (r⁻¹ • y) ⬝ᵥ (V *ᵥ (r⁻¹ • y)) = r⁻¹ * r⁻¹ * (y ⬝ᵥ (V *ᵥ y)) := by
        rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc]
      have hmin := isMinOn_iff.mp hy₀min _ hyhatK
      rw [hfyhat] at hmin
      have := mul_le_mul_of_nonneg_right hmin (mul_pos hrpos hrpos).le
      calc (y₀ ⬝ᵥ (V *ᵥ y₀)) * (y ⬝ᵥ y) = (y₀ ⬝ᵥ (V *ᵥ y₀)) * (r * r) := by rw [hr2]
        _ ≤ (r⁻¹ * r⁻¹ * (y ⬝ᵥ (V *ᵥ y))) * (r * r) := this
        _ = y ⬝ᵥ (V *ᵥ y) := by field_simp

#print axioms quadForm_pos
#print axioms vecMulVec_mulVec
#print axioms log_det_le_sum_log_quadForm
#print axioms sum_log_quadForm_lower_bound
#print axioms exists_quadForm_lower_bound
#print axioms det_le_trace_div_pow
#print axioms det_sq_mul_det_le_prod_diag
#print axioms exists_symm_sqrt
#print axioms exists_isotropic_of_isLocalMin
#print axioms isClosed_posSemidef
#print axioms isCompact_posSemidef_trace_le
#print axioms posDef_sum_vecMulVec_of_span
#print axioms tightFrame_of_firstOrder
#print axioms hasDerivAt_potential
#print axioms hasDerivAt_det_one_add_smul
#print axioms hasDerivAt_logdet
#print axioms eq_zero_of_symm_trace_sq
#print axioms hasDerivAt_potentialG
#print axioms firstOrder_of_isLocalMin
#print axioms continuousAt_potentialG

end PallLean.Paper93.DeepMath.PathB.ForsterIsotropic
