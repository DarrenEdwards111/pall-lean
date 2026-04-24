import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PallLean.Paper93.DeepMath.LPS

open Matrix

/-- The all-ones vector is an eigenvector of the complete-graph adjacency
matrix with eigenvalue `n - 1`. -/
theorem completeAdj_ones_eigen (n : ℕ) (i : Fin n) :
    (completeAdj n).mulVec (fun _ => (1 : ℝ)) i = (n - 1 : ℝ) := by
  -- Unfold `mulVec`, `dotProduct`, and simplify `(... ) * 1`.
  unfold completeAdj Matrix.mulVec dotProduct
  simp only [mul_one]
  -- Now the goal reduces to:
  --   ∑ j, (if i = j then (0 : ℝ) else 1) = (n : ℝ) - 1
  -- Rewrite the sum as a filter cardinality.
  have h1 :
      (∑ j : Fin n, (if i = j then (0 : ℝ) else 1))
        = ((Finset.univ.filter (fun j : Fin n => ¬ i = j)).card : ℝ) := by
    classical
    rw [Finset.sum_ite]
    simp [Finset.sum_const]
  rw [h1]
  -- Filter complement: card of `{j | ¬ i = j}` = n - 1.
  have hfilter :
      (Finset.univ.filter (fun j : Fin n => ¬ i = j)).card = n - 1 := by
    classical
    -- `¬ i = j` is definitionally `i ≠ j`, so the filter equals
    -- `Finset.univ.erase i` by `Finset.filter_ne`.
    have hrewrite :
        (Finset.univ.filter (fun j : Fin n => ¬ i = j))
          = (Finset.univ : Finset (Fin n)).erase i :=
      Finset.filter_ne (Finset.univ : Finset (Fin n)) i
    rw [hrewrite, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Finset.card_univ, Fintype.card_fin]
  rw [hfilter]
  -- Turn `((n - 1 : ℕ) : ℝ)` into `(n : ℝ) - 1`.  This requires `1 ≤ n`,
  -- which holds because `i : Fin n` provides a witness.
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    exact (Fin.elim0 (hzero ▸ i)))
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  exact hcast

end PallLean.Paper93.DeepMath.LPS
