import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

/-!
# Amplituhedron-type positivity barrier (Paper §28.3)

This file defines the *amplituhedron-type positivity barrier*
\[
  B(A) \;=\; -\sum_{J\in\mathcal{J}} \log\det(A[J,J])
\]
as a sum of `-log` of principal minors of `A`, indexed by a fixed family
`𝒥 : Finset (Finset (Fin n))`.

The principal minor `A[J,J]` is the standard `principalMinor` of round 70
defined in `PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract`.

## Scope (per user instruction)

* We define the barrier as a real-valued function on square matrices;
* We prove that for the identity matrix every principal minor equals `1`,
  hence each `Real.log 1 = 0` and the barrier evaluates to `0`;
* We prove that for a positive-definite matrix every principal minor in
  the family is strictly positive, so the `-log` terms are finite real
  numbers (the barrier doesn't hit `+∞`);
* We prove a simple monotonicity fact: enlarging the index family `𝒥`
  on the identity matrix preserves the value `0`.

We deliberately do **not** prove convexity of `-∑ log det` — paper 28.3
does not assert this as a Lean-checked fact, and the user instruction is
to keep this file tightly scoped.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.Positroid
open scoped Matrix

/-- The amplituhedron-type positivity barrier:
    `B(A) = -∑_{J ∈ 𝒥} log det(A[J,J])`. -/
noncomputable def amplituhedronBarrier {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  - ∑ J ∈ 𝒥, Real.log (principalMinor A J)

/-- Every principal minor of the identity matrix is `1`, so each `Real.log` term
    in `amplituhedronBarrier 𝒥 1` is `Real.log 1 = 0`. -/
theorem amplituhedronBarrier_identity (n : ℕ)
    (𝒥 : Finset (Finset (Fin n))) :
    amplituhedronBarrier 𝒥 (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold amplituhedronBarrier
  have hzero : ∀ J ∈ 𝒥,
      Real.log (principalMinor (1 : Matrix (Fin n) (Fin n) ℝ) J) = 0 := by
    intro J _
    rw [principalMinor_one J, Real.log_one]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, neg_zero]

/-- Auxiliary: for an injective map `e : m → n` (any finite types),
    if `A : Matrix n n ℝ` is positive definite, then the principal submatrix
    `A.submatrix e e` is positive definite as well.

    The proof reduces to `Matrix.PosDef.mul_mul_conjTranspose_same` applied
    to the selection matrix `B i j = if (e i = j) then 1 else 0`, which has
    injective vector multiplication when `e` is injective. -/
theorem posDef_submatrix_of_posDef
    {n : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {e : m → Fin n} (he : Function.Injective e) :
    (A.submatrix e e).PosDef := by
  -- Selection matrix `B : Matrix m (Fin n) ℝ` with `B i j = if e i = j then 1 else 0`.
  classical
  let B : Matrix m (Fin n) ℝ := Matrix.of fun i j => if e i = j then (1 : ℝ) else 0
  -- B has injective vecMul when e is injective.
  have hBvecMul : Function.Injective B.vecMul := by
    intro x y hxy
    funext i
    -- (B.vecMul x) (e i) = ∑ k, x k * B k (e i) = x i (since e is injective).
    have hxi : (B.vecMul x) (e i) = x i := by
      simp only [Matrix.vecMul, dotProduct, B, Matrix.of_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        have : e k ≠ e i := fun h => hki (he h)
        simp [this]
      · intro hni
        exact (hni (Finset.mem_univ i)).elim
    have hyi : (B.vecMul y) (e i) = y i := by
      simp only [Matrix.vecMul, dotProduct, B, Matrix.of_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        have : e k ≠ e i := fun h => hki (he h)
        simp [this]
      · intro hni
        exact (hni (Finset.mem_univ i)).elim
    have := congrArg (fun f => f (e i)) hxy
    simp at this
    rw [hxi, hyi] at this
    exact this
  -- Express the submatrix as `B * A * Bᴴ`.
  have hsubmat : A.submatrix e e = B * A * Bᴴ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, B, Matrix.of_apply,
               Matrix.conjTranspose_apply, star_trivial]
    -- Goal: A (e i) (e j) = ∑ x, (∑ x_1, (if e i = x_1 then 1 else 0) * A x_1 x) *
    --                            (if e j = x then 1 else 0)
    rw [Finset.sum_eq_single (e j)]
    · rw [Finset.sum_eq_single (e i)]
      · simp
      · intro k _ hki
        have : e i ≠ k := fun h => hki h.symm
        simp [this]
      · intro hni
        exact (hni (Finset.mem_univ (e i))).elim
    · intro k _ hkj
      have hej : e j ≠ k := fun h => hkj h.symm
      simp [hej]
    · intro hni
      exact (hni (Finset.mem_univ (e j))).elim
  rw [hsubmat]
  exact hA.mul_mul_conjTranspose_same hBvecMul

/-- For each `J ∈ 𝒥`, the principal minor `A[J,J]` is strictly positive when
    `A` is positive definite. -/
theorem principalMinor_pos_of_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (J : Finset (Fin n)) :
    0 < principalMinor A J := by
  classical
  unfold principalMinor
  -- The map `Subtype.val : ↥J → Fin n` is injective.
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  -- The principal submatrix is positive definite.
  have hpd : (A.submatrix (fun i : J => (i.val : Fin n))
                          (fun j : J => (j.val : Fin n))).PosDef :=
    posDef_submatrix_of_posDef hA hInj
  exact hpd.det_pos

/-- For positive-definite `A`, every term in the barrier sum is a finite real
    number. The barrier itself is therefore a finite real number — this is
    just an existential restatement of the fact that `amplituhedronBarrier`
    is by definition a real number, but the meaningful content is the
    accompanying lemma `principalMinor_pos_of_posDef`, which shows each
    `log(det A[J,J])` is well-defined (not `log 0` or `log` of a negative). -/
theorem amplituhedronBarrier_finite {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.PosDef) :
    ∃ r : ℝ, amplituhedronBarrier 𝒥 A = r :=
  ⟨amplituhedronBarrier 𝒥 A, rfl⟩

/-- Monotonicity on the identity matrix: enlarging the index family `𝒥`
    preserves the barrier value `0`. -/
theorem amplituhedronBarrier_identity_mono {n : ℕ}
    (𝒥 𝒥' : Finset (Finset (Fin n))) (_hsub : 𝒥 ⊆ 𝒥') :
    amplituhedronBarrier 𝒥 (1 : Matrix (Fin n) (Fin n) ℝ)
      = amplituhedronBarrier 𝒥' (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [amplituhedronBarrier_identity n 𝒥, amplituhedronBarrier_identity n 𝒥']

/-! ## Log-det barrier bridge to unit principal minors -/

/-- If all designated positive principal minors are at most `1`, then the
log-det barrier is nonnegative.  This is the exact sign convention needed for a
minimization argument on a normalized amplituhedron cell. -/
theorem amplituhedronBarrier_nonneg_of_principalMinor_le_one {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef)
    (hminor_le : ∀ J ∈ 𝒥, principalMinor A J ≤ 1) :
    0 ≤ amplituhedronBarrier 𝒥 A := by
  unfold amplituhedronBarrier
  have hsum_nonpos :
      (∑ J ∈ 𝒥, Real.log (principalMinor A J)) ≤ 0 := by
    exact Finset.sum_nonpos (fun J hJ =>
      Real.log_nonpos (le_of_lt (principalMinor_pos_of_posDef hA J))
        (hminor_le J hJ))
  linarith

/-- If the normalized log-det barrier is zero, every designated principal minor
has logarithm zero. -/
theorem log_principalMinor_eq_zero_of_barrier_eq_zero {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef)
    (hminor_le : ∀ J ∈ 𝒥, principalMinor A J ≤ 1)
    (hbarrier : amplituhedronBarrier 𝒥 A = 0) :
    ∀ J ∈ 𝒥, Real.log (principalMinor A J) = 0 := by
  intro J hJ
  unfold amplituhedronBarrier at hbarrier
  have hsum_zero : (∑ J ∈ 𝒥, Real.log (principalMinor A J)) = 0 := by
    linarith
  have hnonpos : ∀ J ∈ 𝒥, Real.log (principalMinor A J) ≤ 0 := fun K hK =>
    Real.log_nonpos (le_of_lt (principalMinor_pos_of_posDef hA K))
      (hminor_le K hK)
  exact (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum_zero J hJ

/-- If the normalized log-det barrier is zero, every designated principal minor
is exactly `1`. -/
theorem principalMinor_eq_one_of_barrier_eq_zero {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef)
    (hminor_le : ∀ J ∈ 𝒥, principalMinor A J ≤ 1)
    (hbarrier : amplituhedronBarrier 𝒥 A = 0) :
    ∀ J ∈ 𝒥, principalMinor A J = 1 := by
  intro J hJ
  exact Real.eq_one_of_pos_of_log_eq_zero
    (principalMinor_pos_of_posDef hA J)
    (log_principalMinor_eq_zero_of_barrier_eq_zero 𝒥 A hA hminor_le hbarrier J hJ)

/-- On a positive-definite normalized cell, zero log-det barrier is sufficient
for the amplituhedron gauge condition.  This is the first concrete bridge from
variational minimization data to `IsAmplituhedronGauge`: the remaining analytic
work is to prove that the minimizer lies in such a normalized cell and attains
barrier value zero. -/
theorem isAmplituhedronGauge_of_barrier_eq_zero {n : ℕ}
    (𝒥 : Finset (Finset (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef)
    (hminor_le : ∀ J ∈ 𝒥, principalMinor A J ≤ 1)
    (hbarrier : amplituhedronBarrier 𝒥 A = 0) :
    IsAmplituhedronGauge A 𝒥 := by
  refine ⟨hA, ?_⟩
  intro J hJ e
  let B : Matrix J J ℝ :=
    A.submatrix (fun i : J => (i.val : Fin n)) (fun i : J => (i.val : Fin n))
  have hsub :
      A.submatrix (fun i => (e i).1) (fun i => (e i).1) =
        B.submatrix e e := rfl
  have hpm : principalMinor A J = 1 :=
    principalMinor_eq_one_of_barrier_eq_zero 𝒥 A hA hminor_le hbarrier J hJ
  unfold principalMinor at hpm
  rw [hsub, Matrix.det_submatrix_equiv_self e B]
  exact hpm

/-!
## Axiom audit anchors
-/
#print axioms amplituhedronBarrier_identity
#print axioms posDef_submatrix_of_posDef
#print axioms principalMinor_pos_of_posDef
#print axioms amplituhedronBarrier_finite
#print axioms amplituhedronBarrier_identity_mono
#print axioms amplituhedronBarrier_nonneg_of_principalMinor_le_one
#print axioms log_principalMinor_eq_zero_of_barrier_eq_zero
#print axioms principalMinor_eq_one_of_barrier_eq_zero
#print axioms isAmplituhedronGauge_of_barrier_eq_zero

end PallLean.Paper93.DeepMath.PathB
