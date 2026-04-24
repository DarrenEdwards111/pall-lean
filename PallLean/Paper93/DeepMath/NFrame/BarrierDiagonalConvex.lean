import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.NegLogConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# N-Frame: convexity of the diagonal barrier in general dimension `n`

The barrier on a strictly positive diagonal matrix `diagonal d` reduces
to `-∑ i, log (d i)`. We show this is convex in `d` on the positive
orthant `{d : Fin n → ℝ | ∀ i, 0 < d i}` for every `n`.

Strategy:
  (1) Each summand `fun d => -Real.log (d i)` is convex on the half-space
      `{d | 0 < d i}` via `ConvexOn.comp_linearMap` applied to
      `neg_log_convexOn_Ioi` with the coordinate linear map
      `LinearMap.proj i`.
  (2) The positive orthant `{d | ∀ i, 0 < d i}` is convex (intersection
      of the convex half-spaces).
  (3) Restrict each summand to the orthant via `ConvexOn.subset`.
  (4) Combine via a `Finset.induction` using `ConvexOn.add`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Set Finset

/-- The strictly positive orthant in `Fin n → ℝ`. -/
private def posOrthant (n : ℕ) : Set (Fin n → ℝ) :=
  {d : Fin n → ℝ | ∀ i, 0 < d i}

/-- The positive orthant is convex (intersection of positive-entry half-spaces). -/
private theorem convex_posOrthant (n : ℕ) : Convex ℝ (posOrthant n) := by
  intro a ha b hb t s ht hs htsum i
  -- ha : ∀ i, 0 < a i, hb : ∀ i, 0 < b i.
  have hai : 0 < a i := ha i
  have hbi : 0 < b i := hb i
  -- Combine. Case-split on ht, hs as in the 2x2 treatment.
  rcases (lt_or_eq_of_le ht) with ht' | ht'
  · rcases (lt_or_eq_of_le hs) with hs' | hs'
    · have hpos := add_pos (mul_pos ht' hai) (mul_pos hs' hbi)
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hpos
    · -- s = 0, t = 1.
      have hs0 : s = 0 := hs'.symm
      have ht1 : t = 1 := by linarith
      simp [Pi.add_apply, hs0, ht1, hai]
  · -- t = 0, s = 1.
    have ht0 : t = 0 := ht'.symm
    have hs1 : s = 1 := by linarith
    simp [Pi.add_apply, ht0, hs1, hbi]

/-- The coordinate projection `d ↦ d i` as a `LinearMap`. -/
private noncomputable def projCoord {n : ℕ} (i : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

private theorem projCoord_apply {n : ℕ} (i : Fin n) (d : Fin n → ℝ) :
    projCoord i d = d i := rfl

/-- The `i`-th summand `fun d => -Real.log (d i)` is convex on the
half-space `{d | 0 < d i}` via linear composition with `neg_log_convexOn_Ioi`. -/
private theorem negLog_coord_convexOn {n : ℕ} (i : Fin n) :
    ConvexOn ℝ
      ({d : Fin n → ℝ | 0 < d i})
      (fun d => -Real.log (d i)) := by
  have hneg : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => -Real.log x) :=
    neg_log_convexOn_Ioi
  have hcomp :
      ConvexOn ℝ ((projCoord i) ⁻¹' Set.Ioi (0 : ℝ))
        ((fun x => -Real.log x) ∘ (projCoord i)) :=
    hneg.comp_linearMap (projCoord i)
  have hset :
      ((projCoord i) ⁻¹' Set.Ioi (0 : ℝ)) =
        ({d : Fin n → ℝ | 0 < d i}) := by
    ext d
    simp [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, projCoord_apply]
  have hfun :
      ((fun x => -Real.log x) ∘ (projCoord i)) =
        (fun d : Fin n → ℝ => -Real.log (d i)) := by
    funext d
    show -Real.log (projCoord i d) = -Real.log (d i)
    rw [projCoord_apply]
  rw [hset, hfun] at hcomp
  exact hcomp

/-- The `i`-th summand restricted to the positive orthant is convex. -/
private theorem negLog_coord_convexOn_orthant {n : ℕ} (i : Fin n) :
    ConvexOn ℝ (posOrthant n) (fun d : Fin n → ℝ => -Real.log (d i)) := by
  apply (negLog_coord_convexOn i).subset
  · intro d hd
    exact hd i
  · exact convex_posOrthant n

/-- Finite sum over an arbitrary `Finset (Fin n)` of the convex
per-coordinate summands is convex on the positive orthant.

Proved by `Finset.induction` using `ConvexOn.add` and
`convexOn_const`. -/
private theorem sum_negLog_convexOn_finset {n : ℕ} (T : Finset (Fin n)) :
    ConvexOn ℝ (posOrthant n)
      (fun d : Fin n → ℝ => ∑ i ∈ T, -Real.log (d i)) := by
  induction T using Finset.induction_on with
  | empty =>
    -- Empty sum is the zero function, a constant: convex on any convex set.
    have h0 :
        (fun d : Fin n → ℝ => ∑ i ∈ (∅ : Finset (Fin n)), -Real.log (d i)) =
          (fun _ : Fin n → ℝ => (0 : ℝ)) := by
      funext d
      simp
    rw [h0]
    exact convexOn_const 0 (convex_posOrthant n)
  | insert j T hjT ih =>
    -- On `insert j T`, `∑ i ∈ insert j T, f i = f j + ∑ i ∈ T, f i`.
    have hInsert :
        (fun d : Fin n → ℝ =>
            ∑ i ∈ insert j T, -Real.log (d i)) =
          ((fun d : Fin n → ℝ => -Real.log (d j)) +
           (fun d : Fin n → ℝ => ∑ i ∈ T, -Real.log (d i))) := by
      funext d
      simp [Finset.sum_insert hjT, Pi.add_apply]
    rw [hInsert]
    exact (negLog_coord_convexOn_orthant j).add ih

/-- **Barrier on strictly positive diagonal vectors is convex (for all `n`).**

The function `d ↦ -∑ i, Real.log (d i)` is convex on the strictly positive
orthant `{d : Fin n → ℝ | ∀ i, 0 < d i}`.

This is the "diagonal" shadow of the full `-log det` barrier: when applied
to a diagonal matrix with diagonal entries `d i`, the determinant is the
product `∏ i, d i` and hence `barrier (diagonal d) = -∑ i, log (d i)`,
which is a finite sum of `-log` applied to linear coordinate projections,
each convex on `(0, ∞)`. -/
theorem barrier_diagonal_convexOn_n {n : ℕ} :
    ConvexOn ℝ
      ({d : Fin n → ℝ | ∀ i, 0 < d i})
      (fun d => -∑ i, Real.log (d i)) := by
  -- Identify the target set with `posOrthant n`.
  change ConvexOn ℝ (posOrthant n) (fun d => -∑ i, Real.log (d i))
  -- Pull negation inside the sum: `-∑ i, log (d i) = ∑ i, -log (d i)`.
  have hfun :
      (fun d : Fin n → ℝ => -∑ i, Real.log (d i)) =
        (fun d : Fin n → ℝ => ∑ i, -Real.log (d i)) := by
    funext d
    rw [Finset.sum_neg_distrib]
  rw [hfun]
  -- Apply the finite-sum lemma with `T = Finset.univ`.
  exact sum_negLog_convexOn_finset (Finset.univ : Finset (Fin n))

end PallLean.Paper93.DeepMath.NFrame
