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

/-! ## The depth-2 base gate: a bipartite halfspace has sign-rank ≤ 2

A single threshold gate whose weights split across the two input blocks computes
the sign of `α i + β j`, whose realizer matrix has rank `≤ 2` (a sum of two
rank-1 terms).  By the `≤` direction above, its sign-rank is `≤ 2`.  This is the
honest *bottom* of the depth-2 threshold route.

**Honest scope (the correction).**  This does NOT extend to a full depth-2
threshold circuit `THR ∘ LTF` by "rank ≤ size": a majority of `s` halfspaces is
`sign(∑ w_k · sign(R_k))`, where each `sign(R_k)` is a full-rank ±1 matrix, so the
combination is not low rank.  The true bridge runs through unbounded-error (UPP)
communication — `sign-rank ≤ 2^{UPP}` and a size-`s` depth-2 threshold circuit has
`UPP = O(log s)`, giving `sign-rank ≤ poly(s)` — which requires the
communication-protocol machinery, not the rank-factorization here.  That UPP
bridge is the genuine remaining piece; it is not faked. -/

/-- A bipartite halfspace: the sign of `α i + β j` (a threshold gate whose weights
split across the two blocks).  Non-degeneracy `α i + β j ≠ 0` is assumed (standard
for sign representations). -/
noncomputable def bipartiteHalfspace (α : Fin m -> ℝ) (β : Fin n -> ℝ) :
    Fin m -> Fin n -> Bool :=
  fun i j => decide (0 < α i + β j)

/-- **Depth-2 base gate.**  A bipartite halfspace has sign-rank `≤ 2`, via the
explicit rank-2 factorization `α i + β j = α i · 1 + 1 · β j`. -/
theorem bipartiteHalfspace_hasSignRankLE_two (α : Fin m -> ℝ) (β : Fin n -> ℝ)
    (hne : ∀ i j, α i + β j ≠ 0) :
    HasSignRankLE (bipartiteHalfspace α β) 2 := by
  refine ⟨Matrix.of (fun i (k : Fin 2) => if k = 0 then α i else 1),
          Matrix.of (fun (k : Fin 2) j => if k = 0 then (1 : ℝ) else β j), ?_⟩
  intro i j
  have hmul :
      (Matrix.of (fun i (k : Fin 2) => if k = 0 then α i else 1)
        * Matrix.of (fun (k : Fin 2) j => if k = 0 then (1 : ℝ) else β j)) i j
        = α i + β j := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  rw [hmul]
  rcases lt_or_gt_of_ne (hne i j) with hlt | hgt
  · have hb : bipartiteHalfspace α β i j = false := by
      simp only [bipartiteHalfspace, decide_eq_false_iff_not, not_lt]; linarith
    rw [hb, show sgn false = (-1 : ℝ) from rfl]; nlinarith
  · have hb : bipartiteHalfspace α β i j = true := by
      simp only [bipartiteHalfspace, decide_eq_true_eq]; linarith
    rw [hb, show sgn true = (1 : ℝ) from rfl]; nlinarith

#print axioms hasSignRankLE_succ
#print axioms hasSignRankLE_mono
#print axioms exists_factor_rank
#print axioms hasSignRankLE_of_signRealizes_rank_le
#print axioms bipartiteHalfspace_hasSignRankLE_two

end PallLean.Paper93.DeepMath.PathB
