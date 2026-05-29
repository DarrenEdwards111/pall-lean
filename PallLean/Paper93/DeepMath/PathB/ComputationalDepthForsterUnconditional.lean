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

The capstone `forster_bound_unconditional` removes the `GenPos` hypothesis
entirely: *any* dimension-`d` unit realization of `M` forces
`√((m'+1)·n)/‖sgnMat M‖ ≤ d`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForsterUnconditional

open scoped BigOperators Matrix RealInnerProductSpace Matrix.Norms.L2Operator
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

/-- **Unconditional Forster sign-rank lower bound.**  *Every* dimension-`d` unit
realization of `M` (no general-position hypothesis) forces
`√((m'+1)·n)/‖sgnMat M‖ ≤ d`.  Proof: perturb `u_i ↦ u_i + t·z_i` along the
moment curve `z`; general position fails for only finitely many `t`
(`finite_nonGenPos`) while the sign pattern is preserved near `0`
(`eventually_sign_ok`); since a punctured real neighbourhood is infinite, some
`t` satisfies both, giving a general-position realization of the same `M` and
`d`, to which `forster_bound_of_genPos` applies. -/
theorem forster_bound_unconditional {M : Fin (m' + 1) → Fin n → Bool} (hd : 0 < d)
    (hdm' : d ≤ m') (R : UnitRealization M d)
    (hmn : 0 < ((m' + 1 : ℕ) : ℝ) * (n : ℝ)) (hμ : 0 < ‖sgnMat M‖) :
    Real.sqrt (((m' + 1 : ℕ) : ℝ) * (n : ℝ)) / ‖sgnMat M‖ ≤ (d : ℝ) := by
  -- moment-curve lift into `EuclideanSpace`
  let zE : Fin (m' + 1) → EuclideanSpace ℝ (Fin d) :=
    fun j => (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (((j : ℕ) : ℝ)) ^ (i : ℕ))
  have hzEcomp : ∀ j i, (zE j) i = (((j : ℕ) : ℝ)) ^ (i : ℕ) := fun _ _ => rfl
  -- `n > 0`
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hmn
    · exact h
  -- choose `t`: signs preserved (open) and general position (cofinite)
  obtain ⟨t, htsign, htgen0⟩ :
      ∃ t : ℝ, (∀ i j, 0 < sgn (M i j) * ⟪R.u i + t • zE i, R.w j⟫)
        ∧ ¬ (∃ e : Fin d → Fin (m' + 1), Function.Injective e ∧
            (Matrix.of (fun i k => (R.u (e k)) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det = 0) := by
    by_contra hcon
    push_neg at hcon
    have hsub : {t : ℝ | ∀ i j, 0 < sgn (M i j) * ⟪R.u i + t • zE i, R.w j⟫}
        ⊆ {t : ℝ | ∃ e : Fin d → Fin (m' + 1), Function.Injective e ∧
            (Matrix.of (fun i k => (R.u (e k)) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det = 0} :=
      fun t ht => hcon t ht
    have hSfin := (finite_nonGenPos (fun j => (R.u j : Fin d → ℝ))).subset hsub
    exact (infinite_of_mem_nhds (0 : ℝ) (eventually_sign_ok R zE)) hSfin
  have htgen : ∀ e : Fin d → Fin (m' + 1), Function.Injective e →
      (Matrix.of (fun i k => (R.u (e k)) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))).det ≠ 0 :=
    fun e he hdet => htgen0 ⟨e, he, hdet⟩
  -- the perturbed vectors are nonzero (their inner product with `w 0` is nonzero)
  have hpEne : ∀ i, R.u i + t • zE i ≠ 0 := by
    intro i hpi
    have hs := htsign i ⟨0, hn⟩
    rw [hpi, inner_zero_left, mul_zero] at hs
    exact lt_irrefl 0 hs
  -- the perturbed, renormalised unit realization
  let R' : UnitRealization M d :=
    { u := fun i => ‖R.u i + t • zE i‖⁻¹ • (R.u i + t • zE i)
      w := R.w
      u_unit := by
        intro i
        rw [norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos (norm_pos_iff.mpr (hpEne i)),
          inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr (hpEne i)))]
      w_unit := R.w_unit
      sign_ok := by
        intro i j
        rw [real_inner_smul_left]
        have h2 : 0 < ‖R.u i + t • zE i‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hpEne i))
        nlinarith [mul_pos h2 (htsign i j)] }
  -- `R'` is in general position
  have hgp' : GenPos R' := by
    intro e he
    have hsplit : (Matrix.of (fun i k => (R'.u (e k)) i))
        = (Matrix.of (fun i k => (R.u (e k)) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ)))
          * Matrix.diagonal (fun k => ‖R.u (e k) + t • zE (e k)‖⁻¹) := by
      ext i k
      rw [Matrix.mul_diagonal]
      show (‖R.u (e k) + t • zE (e k)‖⁻¹ • (R.u (e k) + t • zE (e k))) i
          = ((R.u (e k)) i + t * (((e k : ℕ) : ℝ)) ^ (i : ℕ))
            * ‖R.u (e k) + t • zE (e k)‖⁻¹
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hzEcomp]
      ring
    rw [hsplit, Matrix.det_mul, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact mul_ne_zero (htgen e he)
      (Finset.prod_ne_zero_iff.mpr
        (fun k _ => inv_ne_zero (ne_of_gt (norm_pos_iff.mpr (hpEne (e k))))))
  exact forster_bound_of_genPos hd hdm' R' hgp' hmn hμ

/-- **Hadamard sign-rank lower bound (concrete instantiation).**  A square `±1`
matrix whose columns are orthogonal, `(sgnMat M)ᵀ · (sgnMat M) = N · I` with
`N = m'+1`, has `L²` operator norm exactly `√N`
(`‖A‖² = ‖Aᴴ A‖ = ‖N·I‖ = N`).  Feeding this into the unconditional Forster
bound `√(N·N)/‖sgnMat M‖ ≤ d` and simplifying `N/√N = √N` shows that *every*
realization has dimension `d ≥ √N`: the sign rank of a Hadamard matrix is at
least `√N`. -/
theorem sqrt_le_of_hadamard {m' : ℕ} (M : Fin (m' + 1) → Fin (m' + 1) → Bool)
    (hHad : (sgnMat M)ᵀ * (sgnMat M)
      = ((m' + 1 : ℕ) : ℝ) • (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) ℝ))
    {d : ℕ} (hd : 0 < d) (hdm' : d ≤ m') (R : UnitRealization M d) :
    Real.sqrt ((m' + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
  have hNpos : (0 : ℝ) < ((m' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m'
  -- conjugate transpose = transpose over ℝ
  have hct : (sgnMat M)ᴴ = (sgnMat M)ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  -- ‖sgnMat M‖² = N
  have hnorm2 : ‖sgnMat M‖ * ‖sgnMat M‖ = ((m' + 1 : ℕ) : ℝ) := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hct, hHad, norm_smul, Real.norm_eq_abs,
      abs_of_pos hNpos, norm_one, mul_one]
  have hnorm : ‖sgnMat M‖ = Real.sqrt ((m' + 1 : ℕ) : ℝ) := by
    rw [← hnorm2, Real.sqrt_mul_self (norm_nonneg _)]
  -- the unconditional Forster bound, specialised to this matrix
  have hf := forster_bound_unconditional hd hdm' R (mul_pos hNpos hNpos)
    (by rw [hnorm]; exact Real.sqrt_pos.mpr hNpos)
  rw [Real.sqrt_mul_self hNpos.le, hnorm, Real.div_sqrt] at hf
  exact hf

/-! ### A concrete Hadamard witness: the Walsh matrix on `(ℤ/2)^k`

`χ` is the nontrivial character of `ℤ/2`, and `walsh_orthogonality` is the
character-sum identity `∑ₓ χ⟨x,a⟩·χ⟨x,b⟩ = [a = b]·2^k`, the orthogonality of
the rows of the Walsh–Hadamard matrix.  This certifies that the Hadamard
hypothesis of `sqrt_le_of_hadamard` is non-vacuous at every size `2^k`. -/

/-- The nontrivial additive character `ℤ/2 → ℝ`, `χ z = (-1)^z`. -/
noncomputable def χ : ZMod 2 → ℝ := fun z => if z = 0 then 1 else -1

lemma χ_add (a b : ZMod 2) : χ (a + b) = χ a * χ b := by
  fin_cases a <;> fin_cases b <;> simp [χ] <;> decide

lemma χ_sum {k : ℕ} (g : Fin k → ZMod 2) (s : Finset (Fin k)) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  induction s using Finset.induction with
  | empty => simp [χ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, χ_add, ih]

/-- **Character (row) orthogonality of the Walsh–Hadamard matrix.** -/
lemma walsh_orthogonality {k : ℕ} (a b : Fin k → ZMod 2) :
    (∑ x : Fin k → ZMod 2, χ (∑ i, x i * a i) * χ (∑ i, x i * b i))
      = if a = b then (2 ^ k : ℝ) else 0 := by
  have hco : ∀ ai bi : ZMod 2,
      (∑ xi : ZMod 2, χ (xi * ai) * χ (xi * bi)) = if ai = bi then (2 : ℝ) else 0 := by
    intro ai bi
    have hexp : (∑ xi : ZMod 2, χ (xi * ai) * χ (xi * bi))
        = χ (0 * ai) * χ (0 * bi) + χ (1 * ai) * χ (1 * bi) := Fin.sum_univ_two _
    rw [hexp]
    fin_cases ai <;> fin_cases bi <;> simp [χ] <;> norm_num
  have hstep : (∑ x : Fin k → ZMod 2, χ (∑ i, x i * a i) * χ (∑ i, x i * b i))
      = ∑ x : Fin k → ZMod 2, ∏ i, (χ (x i * a i) * χ (x i * b i)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [χ_sum (fun i => x i * a i) Finset.univ, χ_sum (fun i => x i * b i) Finset.univ,
      ← Finset.prod_mul_distrib]
  rw [hstep, ← Fintype.prod_sum (fun i (w : ZMod 2) => χ (w * a i) * χ (w * b i))]
  simp only [hco]
  by_cases hab : a = b
  · subst hab; simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The reindexing `Fin (m'+1) ≃ (ℤ/2)^k` available whenever `m'+1 = 2^k`
(both sides have `2^k` elements). -/
noncomputable def walshEquiv {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) :
    Fin (m' + 1) ≃ (Fin k → ZMod 2) :=
  (Fintype.equivFinOfCardEq
    (show Fintype.card (Fin k → ZMod 2) = m' + 1 by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; exact hmk.symm)).symm

/-- The Walsh–Hadamard sign matrix on `Fin (m'+1) ≃ (ℤ/2)^k`:
`M a b = [⟨a,b⟩ = 0 in ℤ/2]`, so `sgnMat M a b = (-1)^⟨a,b⟩`. -/
noncomputable def walshMatrix {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) :
    Fin (m' + 1) → Fin (m' + 1) → Bool :=
  fun a b => decide (∑ i, (walshEquiv hmk a) i * (walshEquiv hmk b) i = 0)

/-- **The Walsh matrix is Hadamard.**  Its `±1` form has orthogonal columns:
`(sgnMat M)ᵀ · (sgnMat M) = (m'+1)·I`, by character orthogonality after
reindexing the sum over `Fin (m'+1)` to `(ℤ/2)^k`. -/
lemma walsh_hadamard {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) :
    (sgnMat (walshMatrix hmk))ᵀ * (sgnMat (walshMatrix hmk))
      = ((m' + 1 : ℕ) : ℝ) • (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) ℝ) := by
  have hsgn : ∀ a b, sgnMat (walshMatrix hmk) a b
      = χ (∑ i, (walshEquiv hmk a) i * (walshEquiv hmk b) i) := by
    intro a b
    by_cases h : (∑ i, (walshEquiv hmk a) i * (walshEquiv hmk b) i) = 0
    · simp [sgnMat, walshMatrix, sgn, χ, h]
    · simp [sgnMat, walshMatrix, sgn, χ, h]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_congr rfl (fun c _ => by rw [hsgn c a, hsgn c b])]
  rw [Equiv.sum_comp (walshEquiv hmk)
      (fun x => χ (∑ i, x i * (walshEquiv hmk a) i) * χ (∑ i, x i * (walshEquiv hmk b) i)),
    walsh_orthogonality, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · rw [if_pos (congrArg (walshEquiv hmk) hab), if_pos hab, mul_one, hmk]
    push_cast; ring
  · rw [if_neg (fun h => hab ((walshEquiv hmk).injective h)), if_neg hab, mul_zero]

/-- **Concrete sign-rank lower bound (Walsh–Hadamard).**  For `m'+1 = 2^k`,
*every* dimension-`d` unit realization of the Walsh sign matrix forces
`√(2^k) ≤ d`: the sign rank of the `2^k × 2^k` Walsh–Hadamard matrix is at least
`√(2^k) = 2^{k/2}`.  This is the canonical Forster lower bound, now unconditional
and concrete. -/
theorem walsh_sign_rank {m' k : ℕ} (hmk : m' + 1 = 2 ^ k) {d : ℕ} (hd : 0 < d)
    (hdm' : d ≤ m') (R : UnitRealization (walshMatrix hmk) d) :
    Real.sqrt ((m' + 1 : ℕ) : ℝ) ≤ (d : ℝ) :=
  sqrt_le_of_hadamard (walshMatrix hmk) (walsh_hadamard hmk) hd hdm' R

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUnconditional.forster_bound_unconditional

#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUnconditional.sqrt_le_of_hadamard
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUnconditional.walsh_orthogonality
#print axioms PallLean.Paper93.DeepMath.PathB.ForsterUnconditional.walsh_sign_rank
