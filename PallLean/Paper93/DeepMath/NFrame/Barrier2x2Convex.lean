import PallLean.Paper93.DeepMath.NFrame.NegLogConvex
import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetFinTwoGrad
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Pi

/-!
# N-Frame: convexity of the 2×2 barrier on positive-diagonal matrices

For 2×2 matrices, the barrier `B(A) = -log(det A)` equals
`-log(A 0 0 * A 1 1 - A 0 1 * A 1 0)` by `Matrix.det_fin_two`.
Without further structural hypotheses, `det : Matrix (Fin 2) (Fin 2) ℝ → ℝ`
is a quadratic polynomial and is NOT concave on the open set `{A | 0 < A.det}`,
so one cannot simply compose `-log` with `det`.

As a CORRECT and verifiable intermediate, we restrict to the subset of
`2 × 2` DIAGONAL matrices with POSITIVE entries on the diagonal, i.e.
`{A | 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0}`. On this convex
subset, `A.det = A 0 0 * A 1 1`, so
`barrier A = -log(A 0 0) + (-log(A 1 1))`, a sum of two convex compositions
of `-log` with linear coordinate projections.

We prove:
  `barrier_fin_two_diagonal_positive_convex` :
    `ConvexOn ℝ S (fun A => barrier A)`
  where `S` is the positive-diagonal set above.

The strategy is:
  (1) show `S` is convex (intersection of two open half-spaces and two
      linear-kernel hyperplanes);
  (2) apply `ConvexOn.comp_linearMap` twice to `neg_log_convexOn_Ioi` to
      obtain convexity of `A ↦ -log(A 0 0)` and `A ↦ -log(A 1 1)` on the
      two half-spaces;
  (3) restrict each summand to `S` via `ConvexOn.subset`;
  (4) add via `ConvexOn.add`;
  (5) identify the sum pointwise with `barrier` on `S` via `ConvexOn.congr`
      using `Matrix.det_fin_two` together with `Real.log_mul`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Set

/-- The positive-diagonal set of 2×2 matrices:
`{A | 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0}`. -/
private def posDiag2 : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0}

/-- Linear projection `A ↦ A 0 0`, as a composition of two `LinearMap.proj`s. -/
private noncomputable def proj00 :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => (Fin 2 → ℝ)) 0)

/-- Linear projection `A ↦ A 1 1`. -/
private noncomputable def proj11 :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => (Fin 2 → ℝ)) 1)

private theorem proj00_apply (A : Matrix (Fin 2) (Fin 2) ℝ) :
    proj00 A = A 0 0 := rfl

private theorem proj11_apply (A : Matrix (Fin 2) (Fin 2) ℝ) :
    proj11 A = A 1 1 := rfl

/-- The positive-diagonal set is convex. We exhibit it as the intersection of
four convex sets: the two open half-spaces `{A | 0 < A 0 0}`, `{A | 0 < A 1 1}`
(each a preimage of `Ioi 0` under a linear map) and the two linear affine
constraints `{A | A 0 1 = 0}`, `{A | A 1 0 = 0}` (each a preimage of `{0}`
under a linear map, i.e. a linear subspace). -/
private theorem convex_posDiag2 : Convex ℝ posDiag2 := by
  -- Unfold posDiag2 and work directly with the four constraints.
  intro A hA B hB t s ht hs htsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 0 < (t • A + s • B) 0 0
    have hA00 : 0 < A 0 0 := hA.1
    have hB00 : 0 < B 0 0 := hB.1
    -- Case on whether t = 0 (then s = 1 > 0 and we use hB00),
    -- similarly for s = 0.
    rcases (lt_or_eq_of_le ht) with ht' | ht'
    · rcases (lt_or_eq_of_le hs) with hs' | hs'
      · -- Both t, s > 0 strictly.
        have := add_pos (mul_pos ht' hA00) (mul_pos hs' hB00)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
      · -- s = 0, so t = 1.
        have hs0 : s = 0 := hs'.symm
        have ht1 : t = 1 := by linarith
        simp [Matrix.add_apply, hs0, ht1, hA00]
    · -- t = 0, so s = 1.
      have ht0 : t = 0 := ht'.symm
      have hs1 : s = 1 := by linarith
      simp [Matrix.add_apply, ht0, hs1, hB00]
  · -- 0 < (t • A + s • B) 1 1
    have hA11 : 0 < A 1 1 := hA.2.1
    have hB11 : 0 < B 1 1 := hB.2.1
    rcases (lt_or_eq_of_le ht) with ht' | ht'
    · rcases (lt_or_eq_of_le hs) with hs' | hs'
      · have := add_pos (mul_pos ht' hA11) (mul_pos hs' hB11)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
      · have hs0 : s = 0 := hs'.symm
        have ht1 : t = 1 := by linarith
        simp [Matrix.add_apply, hs0, ht1, hA11]
    · have ht0 : t = 0 := ht'.symm
      have hs1 : s = 1 := by linarith
      simp [Matrix.add_apply, ht0, hs1, hB11]
  · -- (t • A + s • B) 0 1 = 0
    have hA01 : A 0 1 = 0 := hA.2.2.1
    have hB01 : B 0 1 = 0 := hB.2.2.1
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA01, hB01]
  · -- (t • A + s • B) 1 0 = 0
    have hA10 : A 1 0 = 0 := hA.2.2.2
    have hB10 : B 1 0 = 0 := hB.2.2.2
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA10, hB10]

/-- Auxiliary: `fun A => -Real.log (A 0 0)` is convex on `{A | 0 < A 0 0}`. -/
private theorem negLog_proj00_convexOn :
    ConvexOn ℝ
      ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 0 0})
      (fun A => -Real.log (A 0 0)) := by
  have hneg : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => -Real.log x) :=
    neg_log_convexOn_Ioi
  have hcomp :
      ConvexOn ℝ (proj00 ⁻¹' Ioi (0 : ℝ))
        ((fun x => -Real.log x) ∘ proj00) :=
    hneg.comp_linearMap proj00
  -- Identify the preimage set.
  have hset :
      (proj00 ⁻¹' Ioi (0 : ℝ)) =
        ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 0 0}) := by
    ext A
    simp [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, proj00_apply]
  -- Identify the composed function.
  have hfun :
      ((fun x => -Real.log x) ∘ proj00) =
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 0 0)) := by
    funext A
    show -Real.log (proj00 A) = -Real.log (A 0 0)
    rw [proj00_apply]
  rw [hset, hfun] at hcomp
  exact hcomp

/-- Auxiliary: `fun A => -Real.log (A 1 1)` is convex on `{A | 0 < A 1 1}`. -/
private theorem negLog_proj11_convexOn :
    ConvexOn ℝ
      ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 1 1})
      (fun A => -Real.log (A 1 1)) := by
  have hneg : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => -Real.log x) :=
    neg_log_convexOn_Ioi
  have hcomp :
      ConvexOn ℝ (proj11 ⁻¹' Ioi (0 : ℝ))
        ((fun x => -Real.log x) ∘ proj11) :=
    hneg.comp_linearMap proj11
  have hset :
      (proj11 ⁻¹' Ioi (0 : ℝ)) =
        ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 1 1}) := by
    ext A
    simp [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, proj11_apply]
  have hfun :
      ((fun x => -Real.log x) ∘ proj11) =
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 1 1)) := by
    funext A
    show -Real.log (proj11 A) = -Real.log (A 1 1)
    rw [proj11_apply]
  rw [hset, hfun] at hcomp
  exact hcomp

/-- The 2×2 barrier `B(A) = -log(det A)` is convex on the set of 2×2
diagonal matrices with positive diagonal entries
`{A | 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0}`.

On this set, `A.det = A 0 0 * A 1 1`, hence by `Real.log_mul`,
`barrier A = -log(A 0 0) + (-log(A 1 1))`, a sum of two convex
compositions of `-log` with linear coordinate projections. -/
theorem barrier_fin_two_diagonal_positive_convex :
    ConvexOn ℝ
      ({A : Matrix (Fin 2) (Fin 2) ℝ |
          0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 = 0 ∧ A 1 0 = 0})
      (fun A => barrier A) := by
  -- Rename the target set to `posDiag2`.
  change ConvexOn ℝ posDiag2 (fun A => barrier A)
  -- Step 1: restrict `negLog_proj00_convexOn` from `{A | 0 < A 0 0}` to `posDiag2`.
  have hS_convex : Convex ℝ posDiag2 := convex_posDiag2
  have hsub00 :
      posDiag2 ⊆ ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 0 0}) := by
    intro A hA; exact hA.1
  have hsub11 :
      posDiag2 ⊆ ({A : Matrix (Fin 2) (Fin 2) ℝ | 0 < A 1 1}) := by
    intro A hA; exact hA.2.1
  have h00 : ConvexOn ℝ posDiag2
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 0 0)) :=
    negLog_proj00_convexOn.subset hsub00 hS_convex
  have h11 : ConvexOn ℝ posDiag2
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 1 1)) :=
    negLog_proj11_convexOn.subset hsub11 hS_convex
  -- Step 2: sum the two.
  have hsum : ConvexOn ℝ posDiag2
      ((fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 0 0)) +
       (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 1 1))) :=
    h00.add h11
  -- Step 3: show the sum equals `fun A => barrier A` on `posDiag2`.
  -- For A ∈ posDiag2: A.det = A 0 0 * A 1 1 (from det_fin_two with A01 = A10 = 0),
  -- both factors are positive, hence log(A.det) = log(A 0 0) + log(A 1 1),
  -- so barrier A = -log(A 0 0) + (-log(A 1 1)).
  have hEq :
      Set.EqOn
        ((fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 0 0)) +
         (fun A : Matrix (Fin 2) (Fin 2) ℝ => -Real.log (A 1 1)))
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => barrier A)
        posDiag2 := by
    intro A hA
    obtain ⟨h00, h11, h01z, h10z⟩ := hA
    -- Pointwise compute both sides.
    have hdet : A.det = A 0 0 * A 1 1 := by
      rw [Matrix.det_fin_two]
      rw [h01z, h10z]
      ring
    have h00ne : (A 0 0) ≠ 0 := ne_of_gt h00
    have h11ne : (A 1 1) ≠ 0 := ne_of_gt h11
    have hlog : Real.log A.det = Real.log (A 0 0) + Real.log (A 1 1) := by
      rw [hdet, Real.log_mul h00ne h11ne]
    -- Left side (sum of functions applied pointwise):
    show (-Real.log (A 0 0)) + (-Real.log (A 1 1)) = barrier A
    unfold barrier
    rw [hlog]
    ring
  -- Step 4: transport convexity along the pointwise equality.
  exact hsum.congr hEq

end PallLean.Paper93.DeepMath.NFrame
