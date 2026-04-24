import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GraphSpectral

open scoped BigOperators

/-- Graph Laplacian of a symmetric adjacency matrix `A : Matrix (Fin n) (Fin n) ℝ`:
    `L := D - A`, where `D` is the diagonal degree matrix whose `(i,i)` entry is the
    row-sum `∑ j, A i j`. This is the standard combinatorial Laplacian. -/
def laplacian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (∑ k, A i k) - A i j else -A i j

/-- The Laplacian of a symmetric adjacency matrix is itself symmetric. -/
theorem laplacian_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : (laplacian A).IsSymm := by
  -- Unfold `IsSymm` and show the transpose equals the matrix.
  ext i j
  -- Replace `A j i` by `A i j` via the symmetry hypothesis.
  have hA' : ∀ p q, A p q = A q p := by
    intro p q
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M p q) hA
    -- `A.transpose p q = A q p` and this equals `A p q` by symmetry.
    simpa [Matrix.transpose_apply] using this.symm
  by_cases h : i = j
  · subst h
    simp [Matrix.transpose_apply, laplacian]
  · -- Off-diagonal: both sides equal `-A i j = -A j i`.
    have hji : j ≠ i := fun e => h e.symm
    simp [Matrix.transpose_apply, laplacian, h, hji, hA' j i]

end PallLean.Paper93.DeepMath.GraphSpectral

namespace PallLean.Paper93.DeepMath.GadgetRank

open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- Canonical Cook–Levin compiled gadget matrix parametrised by coupling `α ≥ 0`:
    `Q(α, n) := α • I + L_{K_n}`, where `L_{K_n}` is the Laplacian of the complete
    graph on `Fin n`. This is the §28.3 α-term matrix. -/
def compiledGadget (α : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n)

/-- Symmetry of the compiled gadget. -/
theorem compiledGadget_isSymm (α : ℝ) (n : ℕ) : (compiledGadget α n).IsSymm := by
  unfold compiledGadget
  have h_one_symm : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by
    unfold Matrix.IsSymm
    exact Matrix.transpose_one
  have h_lap_symm : (laplacian (completeAdj n)).IsSymm :=
    laplacian_isSymm _ (completeAdj_symm n)
  -- (α • A + B).transpose = α • A.transpose + B.transpose
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_smul, h_one_symm, h_lap_symm]

end PallLean.Paper93.DeepMath.GadgetRank
