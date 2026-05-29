import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

open scoped InnerProductSpace BigOperators
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

/-! ## Remaining obligations (the long-haul targets), stated precisely -/

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

#print axioms forster_dim_ge_of_bounds
#print axioms forster_bound_of_frame_and_spectral

end PallLean.Paper93.DeepMath.PathB.Forster
