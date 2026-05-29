import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankInvariant

/-!
# Forster's sign-rank lower bound — scaffold (increment 1 of a long-haul build)

**STATUS: SCAFFOLD. Arithmetic core PROVEN; three analytic obligations ISOLATED
(named, not faked, not `:= True`).**

Forster (2002): for a `±1` matrix `M`, `signRank M ≥ √(mn) / ‖M‖₂`.  This is the
*only* known route to a super-constant sign-rank lower bound for an explicit
matrix — the ordinary-rank/determinant route provably tops out at small constants
(checker2 ≥ 2), so Forster is the unavoidable gate for an unconditional growing
depth-2 threshold lower bound.

The proof factors as:

1. **(Isotropic existence — KERNEL)** any sign-realization can be linearly
   transformed (preserving inner-product signs) so the row vectors form a *tight
   frame*: `∀ y, ∑_i ⟪û_i, y⟫² = (m/d)‖y‖²`.  Proved by a compactness/minimization
   argument over `GL(d)`.  **Not in Mathlib; the hard analytic kernel.**
2. **(Frame lower bound)** with unit vectors in tight-frame position,
   `m·n/d ≤ ∑_{i,j} |⟪û_i, ŵ_j⟫|`  (uses `|x| ≥ x²` for `|x| ≤ 1` and the frame
   identity).
3. **(Spectral upper bound)** `∑_{i,j} |⟪û_i, ŵ_j⟫| ≤ ‖M‖₂ · √(mn)`  (sign
   condition turns `|·|` into `M·⟪·,·⟫`, then Cauchy–Schwarz with the l2 operator
   norm of `M`).
4. **(Arithmetic core — PROVEN HERE)** `m·n/d ≤ S` and `S ≤ μ·√(mn)` give
   `√(mn)/μ ≤ d`.

This file proves (4) and fixes the statements of (1)–(3) as the remaining work.
-/

namespace PallLean.Paper93.DeepMath.PathB.Forster

open scoped InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
open RealInnerProductSpace

variable {m n : Nat}

/-! ## Configuration: unit vectors realizing the sign pattern -/

/-- A dimension-`d` sign realization of `M` by **unit** vectors, in the form the
Forster reduction consumes: `u i, w j` are unit vectors in `ℝ^d` whose inner
products have the signs prescribed by `M`. -/
structure UnitRealization (M : Fin m -> Fin n -> Bool) (d : Nat) where
  u : Fin m -> EuclideanSpace ℝ (Fin d)
  w : Fin n -> EuclideanSpace ℝ (Fin d)
  u_unit : ∀ i, ‖u i‖ = 1
  w_unit : ∀ j, ‖w j‖ = 1
  sign_ok : ∀ i j, 0 < sgn (M i j) * ⟪u i, w j⟫

/-- The central Forster quantity `S = ∑_{i,j} |⟪u i, w j⟫|`. -/
noncomputable def forsterSum {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) : ℝ :=
  ∑ i, ∑ j, |⟪R.u i, R.w j⟫|

/-- Tight-frame (isotropic) condition on the row vectors: the obligation produced
by the isotropic-position kernel. -/
def IsTightFrame {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d), ∑ i, ⟪R.u i, y⟫ ^ 2 = ((m : ℝ) / d) * ‖y‖ ^ 2

/-! ## (4) Arithmetic core — proven -/

/-- **Arithmetic core of Forster.**  If `m·n/d ≤ S` (frame lower bound) and
`S ≤ μ·√(mn)` (spectral upper bound), then `√(mn)/μ ≤ d`. -/
theorem forster_dim_ge_of_bounds {d : Nat} {μ S : ℝ}
    (hd : 0 < (d : ℝ)) (hμ : 0 < μ) (hmn : 0 < (m : ℝ) * n)
    (hlow : (m : ℝ) * n / d ≤ S)
    (hupp : S ≤ μ * Real.sqrt ((m : ℝ) * n)) :
    Real.sqrt ((m : ℝ) * n) / μ ≤ (d : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr hmn
  have hsq : Real.sqrt ((m : ℝ) * n) * Real.sqrt ((m : ℝ) * n) = (m : ℝ) * n :=
    Real.mul_self_sqrt hmn.le
  rw [div_le_iff₀ hμ]
  rw [div_le_iff₀ hd] at hlow
  have key :
      Real.sqrt ((m : ℝ) * n) * Real.sqrt ((m : ℝ) * n)
        ≤ (d * μ) * Real.sqrt ((m : ℝ) * n) := by
    rw [hsq]
    calc (m : ℝ) * n ≤ S * d := hlow
      _ ≤ (μ * Real.sqrt ((m : ℝ) * n)) * d :=
          mul_le_mul_of_nonneg_right hupp hd.le
      _ = (d * μ) * Real.sqrt ((m : ℝ) * n) := by ring
  exact le_of_mul_le_mul_right key hsqrt_pos

/-! ## Conditional assembly: (2) + (3) ⇒ the bound, modulo the isotropic kernel -/

/-- **Forster bound, conditional on the two analytic bounds.**  Given a tight-frame
unit realization of dimension `d`, the frame lower bound, and the spectral upper
bound with constant `μ = ‖M‖₂`, the dimension satisfies `√(mn)/μ ≤ d`.  The two
bounds are the obligations (2),(3) above; here they are explicit hypotheses to be
discharged next, not assumed away. -/
theorem forster_bound_of_frame_and_spectral
    {M : Fin m -> Fin n -> Bool} {d : Nat} (R : UnitRealization M d) {μ : ℝ}
    (hd : 0 < (d : ℝ)) (hμ : 0 < μ) (hmn : 0 < (m : ℝ) * n)
    (hlow : (m : ℝ) * n / d ≤ forsterSum R)
    (hupp : forsterSum R ≤ μ * Real.sqrt ((m : ℝ) * n)) :
    Real.sqrt ((m : ℝ) * n) / μ ≤ (d : ℝ) :=
  forster_dim_ge_of_bounds hd hμ hmn hlow hupp

/-! ## (3a) Sign step of the spectral bound — proven

The sign condition turns the absolute values in `S` into a *signed* bilinear sum,
the form the spectral norm bounds.  This is the clean, self-contained half of the
spectral upper bound; the remaining half (coordinate decomposition + l2 operator
norm `Matrix.l2_opNorm_mulVec` + double Cauchy–Schwarz) is the heavy substrate. -/

/-- `S = ∑_{i,j} sgn(M i j) · ⟪u i, w j⟫` — the absolute values collapse to signed
inner products because `sgn(M i j) · ⟪u i, w j⟫ > 0`. -/
theorem forsterSum_eq_signed {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) :
    forsterSum R = ∑ i, ∑ j, sgn (M i j) * ⟪R.u i, R.w j⟫ := by
  unfold forsterSum
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hpos := R.sign_ok i j
  by_cases hM : M i j = true
  · rw [hM] at hpos ⊢
    rw [show sgn true = (1 : ℝ) from rfl] at hpos ⊢
    have hp : 0 < ⟪R.u i, R.w j⟫ := by nlinarith
    rw [abs_of_pos hp]; ring
  · rw [Bool.not_eq_true] at hM
    rw [hM] at hpos ⊢
    rw [show sgn false = (-1 : ℝ) from rfl] at hpos ⊢
    have hneg : ⟪R.u i, R.w j⟫ < 0 := by nlinarith
    rw [abs_of_neg hneg]; ring

/-! ## (3b) Spectral upper bound — substrate probe -/

/-- The sign matrix of `M` as a real matrix. -/
noncomputable def sgnMat (M : Fin m -> Fin n -> Bool) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of (fun i j => sgn (M i j))

theorem eucl_inner_eq_sum {k : Nat} (x y : EuclideanSpace ℝ (Fin k)) :
    (⟪x, y⟫ : ℝ) = ∑ c, x c * y c := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

theorem eucl_normSq_eq_sum {k : Nat} (x : EuclideanSpace ℝ (Fin k)) :
    ‖x‖ ^ 2 = ∑ c, (x c) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- **(3) PROVED.**  The spectral upper bound `S ≤ ‖sgnMat M‖₂ · √(mn)`:
coordinate-decompose into `∑_c ⟪Uc, sgnMat ·ᵥ Wc⟫`, bound each term by
`l2_opNorm_mulVec` + Cauchy–Schwarz, then a Cauchy–Schwarz over the `d`
coordinates with the Parseval identities `∑_c ‖Uc c‖² = m`, `∑_c ‖Wc c‖² = n`. -/
theorem spectralUpperBound_proof (M : Fin m -> Fin n -> Bool) {d : Nat}
    (R : UnitRealization M d) :
    forsterSum R ≤ ‖sgnMat M‖ * Real.sqrt ((m : ℝ) * n) := by
  classical
  set A := sgnMat M with hA
  let Uc : Fin d -> EuclideanSpace ℝ (Fin m) :=
    fun c => (WithLp.equiv 2 (Fin m → ℝ)).symm (fun i => R.u i c)
  let Wc : Fin d -> EuclideanSpace ℝ (Fin n) :=
    fun c => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun j => R.w j c)
  let Av : Fin d -> EuclideanSpace ℝ (Fin m) :=
    fun c => (WithLp.equiv 2 (Fin m → ℝ)).symm (A *ᵥ (fun j => R.w j c))
  have hUc : ∀ c i, Uc c i = R.u i c := fun _ _ => rfl
  have hWc : ∀ c j, Wc c j = R.w j c := fun _ _ => rfl
  have hAv : ∀ c i, Av c i = ∑ j, sgn (M i j) * R.w j c := by
    intro c i
    show (A *ᵥ (fun j => R.w j c)) i = _
    simp only [hA, sgnMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  -- coordinate decomposition
  have hcoord : forsterSum R = ∑ c, ⟪Uc c, Av c⟫ := by
    rw [forsterSum_eq_signed]
    have hLHS : ∀ i j, sgn (M i j) * ⟪R.u i, R.w j⟫
        = ∑ c, sgn (M i j) * (R.u i c * R.w j c) := by
      intro i j; rw [eucl_inner_eq_sum, Finset.mul_sum]
    have hRHS : ∀ c, (⟪Uc c, Av c⟫ : ℝ)
        = ∑ i, ∑ j, sgn (M i j) * (R.u i c * R.w j c) := by
      intro c
      rw [eucl_inner_eq_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hUc, hAv, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hLHS i j)),
        Finset.sum_congr rfl (fun c _ => hRHS c)]
    rw [Finset.sum_congr rfl
          (fun i _ => Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun j c => sgn (M i j) * (R.u i c * R.w j c))),
        Finset.sum_comm]
  rw [hcoord]
  -- termwise bound
  have hterm : ∀ c, (⟪Uc c, Av c⟫ : ℝ) ≤ ‖A‖ * (‖Uc c‖ * ‖Wc c‖) := by
    intro c
    have hmv : ‖Av c‖ ≤ ‖A‖ * ‖Wc c‖ := A.l2_opNorm_mulVec (Wc c)
    calc (⟪Uc c, Av c⟫ : ℝ)
        ≤ ‖Uc c‖ * ‖Av c‖ := real_inner_le_norm _ _
      _ ≤ ‖Uc c‖ * (‖A‖ * ‖Wc c‖) := by gcongr
      _ = ‖A‖ * (‖Uc c‖ * ‖Wc c‖) := by ring
  -- Parseval identities
  have hParsevalU : ∑ c, ‖Uc c‖ ^ 2 = (m : ℝ) := by
    rw [Finset.sum_congr rfl (fun c _ => eucl_normSq_eq_sum (Uc c)), Finset.sum_comm]
    have hu : ∀ i, ∑ c, (Uc c i) ^ 2 = 1 := by
      intro i
      rw [Finset.sum_congr rfl (fun c _ => by rw [hUc c i])]
      rw [← eucl_normSq_eq_sum (R.u i), R.u_unit i, one_pow]
    rw [Finset.sum_congr rfl (fun i _ => hu i)]; simp
  have hParsevalW : ∑ c, ‖Wc c‖ ^ 2 = (n : ℝ) := by
    rw [Finset.sum_congr rfl (fun c _ => eucl_normSq_eq_sum (Wc c)), Finset.sum_comm]
    have hw : ∀ j, ∑ c, (Wc c j) ^ 2 = 1 := by
      intro j
      rw [Finset.sum_congr rfl (fun c _ => by rw [hWc c j])]
      rw [← eucl_normSq_eq_sum (R.w j), R.w_unit j, one_pow]
    rw [Finset.sum_congr rfl (fun j _ => hw j)]; simp
  -- assemble
  calc ∑ c, (⟪Uc c, Av c⟫ : ℝ)
      ≤ ∑ c, ‖A‖ * (‖Uc c‖ * ‖Wc c‖) := Finset.sum_le_sum (fun c _ => hterm c)
    _ = ‖A‖ * ∑ c, ‖Uc c‖ * ‖Wc c‖ := by rw [Finset.mul_sum]
    _ ≤ ‖A‖ * Real.sqrt ((m : ℝ) * n) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hcs : (∑ c, ‖Uc c‖ * ‖Wc c‖) ^ 2 ≤ (m : ℝ) * n := by
          have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun c => ‖Uc c‖) (fun c => ‖Wc c‖)
          rwa [hParsevalU, hParsevalW] at h
        have hnn : 0 ≤ ∑ c, ‖Uc c‖ * ‖Wc c‖ :=
          Finset.sum_nonneg (fun c _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        have h := Real.sqrt_le_sqrt hcs
        rwa [Real.sqrt_sq hnn] at h

/-! ## Remaining obligation: ONLY the isotropic-position kernel (1) -/

/-- (3) **Spectral upper bound** obligation: `S ≤ ‖M‖₂ · √(mn)`.  Needs the l2
operator norm of the sign matrix and Cauchy–Schwarz; the substrate to build. -/
def SpectralUpperBound (M : Fin m -> Fin n -> Bool) (μ : ℝ) : Prop :=
  ∀ {d : Nat} (R : UnitRealization M d), forsterSum R ≤ μ * Real.sqrt ((m : ℝ) * n)

/-- (2) **Frame lower bound** obligation: a tight-frame unit realization has
`m·n/d ≤ S`.  **PROVED below** (`frameLowerBound`). -/
def FrameLowerBound (M : Fin m -> Fin n -> Bool) : Prop :=
  ∀ {d : Nat} (R : UnitRealization M d), 0 < d -> IsTightFrame R ->
    (m : ℝ) * n / d ≤ forsterSum R

/-- **(2) PROVED.**  For a tight-frame unit realization, `m·n/d ≤ S`.  Each
`|⟪û_i, ŵ_j⟫| ≥ ⟪û_i, ŵ_j⟫²` (Cauchy–Schwarz: `|·| ≤ 1`, so `x² ≤ |x|`); summing and
applying the tight-frame identity at each `ŵ_j` gives `∑ = (m/d)·n = m·n/d`. -/
theorem frameLowerBound (M : Fin m -> Fin n -> Bool) : FrameLowerBound M := by
  intro d R _ hframe
  have hsq_le : ∀ i j, ⟪R.u i, R.w j⟫ ^ 2 ≤ |⟪R.u i, R.w j⟫| := by
    intro i j
    have hcs : |⟪R.u i, R.w j⟫| ≤ 1 := by
      have h := abs_real_inner_le_norm (R.u i) (R.w j)
      rw [R.u_unit i, R.w_unit j] at h; simpa using h
    have h2 : |⟪R.u i, R.w j⟫| * |⟪R.u i, R.w j⟫| ≤ |⟪R.u i, R.w j⟫| := by
      nlinarith [abs_nonneg (⟪R.u i, R.w j⟫ : ℝ), hcs]
    rw [pow_two, ← abs_mul_abs_self]; exact h2
  have hsumsq : ∑ i, ∑ j, ⟪R.u i, R.w j⟫ ^ 2 = (m : ℝ) * n / d := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j _ => hframe (R.w j))]
    simp only [R.w_unit, one_pow, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc (m : ℝ) * n / d
      = ∑ i, ∑ j, ⟪R.u i, R.w j⟫ ^ 2 := hsumsq.symm
    _ ≤ ∑ i, ∑ j, |⟪R.u i, R.w j⟫| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq_le i j
    _ = forsterSum R := rfl

/-- (1) **Isotropic-position kernel** obligation: every unit realization can be
replaced (same dimension) by a tight-frame one with the same sign pattern.  The
hard analytic kernel (compactness/minimization over `GL(d)`). -/
def IsotropicKernel (M : Fin m -> Fin n -> Bool) : Prop :=
  ∀ {d : Nat}, (∃ R : UnitRealization M d, True) ->
    ∃ R' : UnitRealization M d, IsTightFrame R'

/-! ## Capstone: the full Forster reduction (everything PROVEN except the kernel)

Frame lower bound (2), spectral upper bound (3), and arithmetic core (4) are all
proven, so the entire Forster reduction holds: a **tight-frame** unit realization
of dimension `d` forces `√(mn)/‖sgnMat M‖ ≤ d`.  The *only* remaining input is a
tight frame — exactly what the isotropic-position kernel (1) provides. -/
theorem forster_bound_of_tightFrame (M : Fin m -> Fin n -> Bool) {d : Nat}
    (R : UnitRealization M d) (hd : 0 < d) (hframe : IsTightFrame R)
    (hmn : 0 < (m : ℝ) * n) (hμ : 0 < ‖sgnMat M‖) :
    Real.sqrt ((m : ℝ) * n) / ‖sgnMat M‖ ≤ (d : ℝ) :=
  forster_dim_ge_of_bounds (by exact_mod_cast hd) hμ hmn
    (frameLowerBound M R hd hframe) (spectralUpperBound_proof M R)

/-- **Forster, modulo the isotropic kernel.**  Given the kernel for `M` and any
unit realization of dimension `d`, the dimension is at least `√(mn)/‖sgnMat M‖`.
This is the complete Forster lower bound with the single research-grade obligation
`IsotropicKernel` as its only hypothesis. -/
theorem forster_of_kernel (M : Fin m -> Fin n -> Bool) (hker : IsotropicKernel M)
    {d : Nat} (R : UnitRealization M d) (hd : 0 < d)
    (hmn : 0 < (m : ℝ) * n) (hμ : 0 < ‖sgnMat M‖) :
    Real.sqrt ((m : ℝ) * n) / ‖sgnMat M‖ ≤ (d : ℝ) := by
  obtain ⟨R', hframe⟩ := hker ⟨R, trivial⟩
  exact forster_bound_of_tightFrame M R' hd hframe hmn hμ

#print axioms forster_dim_ge_of_bounds
#print axioms frameLowerBound
#print axioms spectralUpperBound_proof
#print axioms forster_bound_of_tightFrame
#print axioms forster_of_kernel

end PallLean.Paper93.DeepMath.PathB.Forster
