/-
  PallLean/Paper93/Paper283/BlockDiagonalFamily.lean

  Paper §28.3 — Bridge B: Block-diagonal structure of `A(P)`.

  This file encodes the block-diagonal property of a matrix with
  respect to a family of index blocks, and verifies that the identity
  matrix is block-diagonal with respect to the family of singleton
  blocks indexed by the vertices.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.Paper283

open Matrix

/-- Block-diagonal matrix from a family of block matrices indexed by vertices. -/
def isBlockDiagonal {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ)
    (blocks : Finset (Finset (Fin N))) : Prop :=
  ∀ i j : Fin N, (∀ B ∈ blocks, ¬ (i ∈ B ∧ j ∈ B)) → A i j = 0

/-- Identity matrix is block-diagonal with singleton blocks. -/
theorem one_isBlockDiagonal_singletons {N : ℕ} :
    isBlockDiagonal (1 : Matrix (Fin N) (Fin N) ℝ)
      (Finset.univ.image (fun i : Fin N => ({i} : Finset (Fin N)))) := by
  intro i j h
  have h_ij : ¬ (i ∈ ({i} : Finset (Fin N)) ∧ j ∈ ({i} : Finset (Fin N))) := by
    apply h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp at h_ij
  have hne : i ≠ j := fun heq => h_ij heq.symm
  simp [Matrix.one_apply, hne]

end PallLean.Paper93.Paper283
