import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankRankLower

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

#print axioms hasSignRankLE_succ
#print axioms hasSignRankLE_mono

end PallLean.Paper93.DeepMath.PathB
