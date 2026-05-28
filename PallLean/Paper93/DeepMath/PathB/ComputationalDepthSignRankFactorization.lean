import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankRankLower
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Sign-rank monotonicity in the dimension (toward sign-rank = min realizer rank)

Step toward the `≤` direction of `signRank M = min { rank A : A sign-realizes M }`.
`ComputationalDepthSignRankRankLower` proves the `≥` direction.  The `≤` direction
needs (i) monotonicity of `HasSignRankLE` in the dimension (this file) and
(ii) rank-factorization (`rank A ≤ d ⇒ A = B * C` through dimension `d`), which is
not in Mathlib and is the next piece.

This file proves (i): padding a factorization with a zero column/row.  No socket,
no carried hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Matrix

variable {m n : Nat}

/-- One extra dimension never hurts: pad `B` with a zero column and `C` with a zero
row. -/
theorem hasSignRankLE_succ {M : Fin m -> Fin n -> Bool} {d : Nat}
    (h : HasSignRankLE M d) : HasSignRankLE M (d + 1) := by
  obtain ⟨B, C, hBC⟩ := h
  refine ⟨Matrix.of (fun (i : Fin m) (k : Fin (d + 1)) =>
            @Fin.snoc d (fun _ => ℝ) (fun k' => B i k') 0 k),
          Matrix.of (fun (k : Fin (d + 1)) (j : Fin n) =>
            @Fin.snoc d (fun _ => ℝ) (fun k' => C k' j) 0 k), ?_⟩
  intro i j
  have hmul :
      (Matrix.of (fun (i : Fin m) (k : Fin (d + 1)) =>
            @Fin.snoc d (fun _ => ℝ) (fun k' => B i k') 0 k)
        * Matrix.of (fun (k : Fin (d + 1)) (j : Fin n) =>
            @Fin.snoc d (fun _ => ℝ) (fun k' => C k' j) 0 k)) i j
        = (B * C) i j := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, Matrix.mul_apply]
  rw [hmul]; exact hBC i j

/-- Monotonicity of `HasSignRankLE` in the dimension. -/
theorem hasSignRankLE_mono {M : Fin m -> Fin n -> Bool} {d d' : Nat}
    (hdd : d ≤ d') (h : HasSignRankLE M d) : HasSignRankLE M d' := by
  induction hdd with
  | refl => exact h
  | step _ ih => exact hasSignRankLE_succ ih

/-! ## Rank-factorization (not in Mathlib): `A = B * C` through `Fin A.rank` -/

/-- Every real matrix factors through its rank: `A = B * C` with inner dimension
`A.rank`.  Built from a basis of the column space (range of `mulVecLin`). -/
theorem exists_factor_rank (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (B : Matrix (Fin m) (Fin A.rank) ℝ) (C : Matrix (Fin A.rank) (Fin n) ℝ),
      B * C = A := by
  classical
  -- `A.rank = finrank of the range of mulVecLin`, definitionally.
  let W := LinearMap.range A.mulVecLin
  let e : W ≃ₗ[ℝ] (Fin A.rank → ℝ) := (Module.finBasis ℝ W).equivFun
  let g : (Fin n → ℝ) →ₗ[ℝ] (Fin A.rank → ℝ) :=
    e.toLinearMap ∘ₗ A.mulVecLin.rangeRestrict
  let h : (Fin A.rank → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    W.subtype ∘ₗ e.symm.toLinearMap
  have hcomp : h ∘ₗ g = A.mulVecLin := by
    refine LinearMap.ext fun x => ?_
    simp only [g, h, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
      LinearMap.rangeRestrict]
    rfl
  have htl : (Matrix.toLin' A) = A.mulVecLin := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.mulVecLin_apply]
  refine ⟨LinearMap.toMatrix' h, LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_comp, hcomp, ← htl, LinearMap.toMatrix'_toLin']

/-- **`≤` direction.**  A sign-realizer of ordinary rank `≤ d` yields a
`HasSignRankLE M d` witness. -/
theorem hasSignRankLE_of_signRealizes_rank_le {M : Fin m -> Fin n -> Bool}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : SignRealizes M A) {d : Nat}
    (hr : A.rank ≤ d) : HasSignRankLE M d := by
  obtain ⟨B, C, hBC⟩ := exists_factor_rank A
  have hbase : HasSignRankLE M A.rank := by
    refine ⟨B, C, ?_⟩
    intro i j
    rw [hBC]
    exact hA i j
  exact hasSignRankLE_mono hr hbase

#print axioms hasSignRankLE_succ
#print axioms hasSignRankLE_mono
#print axioms exists_factor_rank
#print axioms hasSignRankLE_of_signRealizes_rank_le

end PallLean.Paper93.DeepMath.PathB
