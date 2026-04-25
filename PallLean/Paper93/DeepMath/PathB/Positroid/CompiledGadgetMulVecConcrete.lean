import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Explicit
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Explicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4Explicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetStructIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Concrete `mulVec` formulas for the compiled gadget

This file proves a handful of explicit `mulVec` identities for
`compiledGadget α n` at small `n`. These pin down the action of the
matrix on concrete vectors:

* `compiledGadget_mulVec_e0_n3` — multiplying the 3×3 compiled gadget
  by the first standard basis vector `e_0 = (1, 0, 0)` returns the
  first column `(α + 2, -1, -1)`.
* `compiledGadget_mulVec_e0_n4` — analogous identity at `n = 4`,
  with first column `(α + 3, -1, -1, -1)`.
* `compiledGadget_mulVec_allOnes_n2` — the all-ones vector
  `(1, 1) : Fin 2 → ℝ` maps to `(α, α)`. (Eigenvalue α with the
  all-ones eigenvector at n = 2.)
* `compiledGadget_mulVec_allOnes_n3` — the all-ones vector at `n = 3`
  maps to `(α, α, α)`.

The proofs proceed by `funext i; fin_cases i`, then explicitly unfold
`Matrix.mulVec` to `dotProduct`, expand the finite sum via
`Fin.sum_univ_two` / `Fin.sum_univ_three` / `Fin.sum_univ_four`, and
substitute the matrix entries via the existing `compiledGadget_2x2_*`,
`compiledGadget_3x3_*`, and `compiledGadget_off_diag` lemmas. The final
arithmetic identity is closed with `ring`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB
open Matrix

/-- **`mulVec` of the 3×3 compiled gadget on the first standard basis vector.**

Multiplying `compiledGadget α 3` by `e_0 = (1, 0, 0)` returns the first
column of the matrix, which is `(α + 2, -1, -1)`. -/
theorem compiledGadget_mulVec_e0_n3 (α : ℝ) :
    (compiledGadget α 3).mulVec (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)
      = (fun i : Fin 3 => if i = 0 then α + 2 else -1) := by
  -- Distinctness facts among indices in `Fin 3`.
  have hne10 : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
  have hne20 : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
  have hne01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hne02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hne12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hne21 : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
  -- Compiled gadget entries at `n = 3`.
  have h00 : compiledGadget α 3 (0 : Fin 3) (0 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 0
  have h11 : compiledGadget α 3 (1 : Fin 3) (1 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 1
  have h22 : compiledGadget α 3 (2 : Fin 3) (2 : Fin 3) = α + 2 :=
    compiledGadget_3x3_diag α 2
  have h01 : compiledGadget α 3 (0 : Fin 3) (1 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 0 1 hne01
  have h02 : compiledGadget α 3 (0 : Fin 3) (2 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 0 2 hne02
  have h10 : compiledGadget α 3 (1 : Fin 3) (0 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 1 0 hne10
  have h12 : compiledGadget α 3 (1 : Fin 3) (2 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 1 2 hne12
  have h20 : compiledGadget α 3 (2 : Fin 3) (0 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 2 0 hne20
  have h21 : compiledGadget α 3 (2 : Fin 3) (1 : Fin 3) = -1 :=
    compiledGadget_3x3_off_diag α 2 1 hne21
  -- Decompose mulVec at any `Fin 3` index as a 3-term sum.
  have hmv : ∀ k : Fin 3,
      ((compiledGadget α 3).mulVec
          (fun j : Fin 3 => if j = 0 then (1 : ℝ) else 0)) k
        = compiledGadget α 3 k 0 *
            (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
          + compiledGadget α 3 k 1 *
              (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
          + compiledGadget α 3 k 2 *
              (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) := by
    intro k
    show (∑ j : Fin 3, compiledGadget α 3 k j *
            (if j = 0 then (1 : ℝ) else 0)) = _
    rw [Fin.sum_univ_three]
  funext i
  fin_cases i
  · -- Index 0.
    show ((compiledGadget α 3).mulVec
        (fun j : Fin 3 => if j = 0 then (1 : ℝ) else 0)) 0
        = (if (0 : Fin 3) = 0 then α + 2 else -1)
    rw [hmv 0]
    rw [if_pos rfl, if_neg hne10, if_neg hne20]
    rw [h00, h01, h02]
    rw [if_pos rfl]
    ring
  · -- Index 1.
    show ((compiledGadget α 3).mulVec
        (fun j : Fin 3 => if j = 0 then (1 : ℝ) else 0)) 1
        = (if (1 : Fin 3) = 0 then α + 2 else -1)
    rw [hmv 1]
    rw [if_pos rfl, if_neg hne10, if_neg hne20]
    rw [h10, h11, h12]
    rw [if_neg hne10]
    ring
  · -- Index 2.
    show ((compiledGadget α 3).mulVec
        (fun j : Fin 3 => if j = 0 then (1 : ℝ) else 0)) 2
        = (if (2 : Fin 3) = 0 then α + 2 else -1)
    rw [hmv 2]
    rw [if_pos rfl, if_neg hne10, if_neg hne20]
    rw [h20, h21, h22]
    rw [if_neg hne20]
    ring

/-- **`mulVec` of the 4×4 compiled gadget on the first standard basis vector.**

Multiplying `compiledGadget α 4` by `e_0 = (1, 0, 0, 0)` returns the
first column of the matrix, which is `(α + 3, -1, -1, -1)`. -/
theorem compiledGadget_mulVec_e0_n4 (α : ℝ) :
    (compiledGadget α 4).mulVec (fun i : Fin 4 => if i = 0 then (1 : ℝ) else 0)
      = (fun i : Fin 4 => if i = 0 then α + 3 else -1) := by
  -- Distinctness facts among indices in `Fin 4`.
  have hne10 : (1 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne20 : (2 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne30 : (3 : Fin 4) ≠ (0 : Fin 4) := by decide
  have hne01 : (0 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne02 : (0 : Fin 4) ≠ (2 : Fin 4) := by decide
  have hne03 : (0 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne12 : (1 : Fin 4) ≠ (2 : Fin 4) := by decide
  have hne13 : (1 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne21 : (2 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne23 : (2 : Fin 4) ≠ (3 : Fin 4) := by decide
  have hne31 : (3 : Fin 4) ≠ (1 : Fin 4) := by decide
  have hne32 : (3 : Fin 4) ≠ (2 : Fin 4) := by decide
  -- Diagonal entries at `n = 4`.
  have h00 : compiledGadget α 4 (0 : Fin 4) (0 : Fin 4) = α + 3 :=
    compiledGadget_4x4_diag α 0
  have h11 : compiledGadget α 4 (1 : Fin 4) (1 : Fin 4) = α + 3 :=
    compiledGadget_4x4_diag α 1
  have h22 : compiledGadget α 4 (2 : Fin 4) (2 : Fin 4) = α + 3 :=
    compiledGadget_4x4_diag α 2
  have h33 : compiledGadget α 4 (3 : Fin 4) (3 : Fin 4) = α + 3 :=
    compiledGadget_4x4_diag α 3
  -- Off-diagonal entries at `n = 4`, via the generic `compiledGadget_off_diag`.
  have h01 : compiledGadget α 4 (0 : Fin 4) (1 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne01
  have h02 : compiledGadget α 4 (0 : Fin 4) (2 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne02
  have h03 : compiledGadget α 4 (0 : Fin 4) (3 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne03
  have h10 : compiledGadget α 4 (1 : Fin 4) (0 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne10
  have h12 : compiledGadget α 4 (1 : Fin 4) (2 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne12
  have h13 : compiledGadget α 4 (1 : Fin 4) (3 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne13
  have h20 : compiledGadget α 4 (2 : Fin 4) (0 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne20
  have h21 : compiledGadget α 4 (2 : Fin 4) (1 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne21
  have h23 : compiledGadget α 4 (2 : Fin 4) (3 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne23
  have h30 : compiledGadget α 4 (3 : Fin 4) (0 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne30
  have h31 : compiledGadget α 4 (3 : Fin 4) (1 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne31
  have h32 : compiledGadget α 4 (3 : Fin 4) (2 : Fin 4) = -1 :=
    compiledGadget_off_diag α 4 hne32
  -- Decompose mulVec at any `Fin 4` index as a 4-term sum, using the
  -- left-associative form coming from `Fin.sum_univ_four`.
  have hmv : ∀ k : Fin 4,
      ((compiledGadget α 4).mulVec
          (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 0)) k
        = compiledGadget α 4 k 0 *
              (if (0 : Fin 4) = 0 then (1 : ℝ) else 0)
            + compiledGadget α 4 k 1 *
                (if (1 : Fin 4) = 0 then (1 : ℝ) else 0)
            + compiledGadget α 4 k 2 *
                (if (2 : Fin 4) = 0 then (1 : ℝ) else 0)
            + compiledGadget α 4 k 3 *
                (if (3 : Fin 4) = 0 then (1 : ℝ) else 0) := by
    intro k
    show (∑ j : Fin 4, compiledGadget α 4 k j *
            (if j = 0 then (1 : ℝ) else 0)) = _
    rw [Fin.sum_univ_four]
  funext i
  fin_cases i
  · show ((compiledGadget α 4).mulVec
        (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 0)) 0
        = (if (0 : Fin 4) = 0 then α + 3 else -1)
    rw [hmv 0]
    rw [if_pos rfl, if_neg hne10, if_neg hne20, if_neg hne30]
    rw [h00, h01, h02, h03]
    rw [if_pos rfl]
    ring
  · show ((compiledGadget α 4).mulVec
        (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 0)) 1
        = (if (1 : Fin 4) = 0 then α + 3 else -1)
    rw [hmv 1]
    rw [if_pos rfl, if_neg hne10, if_neg hne20, if_neg hne30]
    rw [h10, h11, h12, h13]
    rw [if_neg hne10]
    ring
  · show ((compiledGadget α 4).mulVec
        (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 0)) 2
        = (if (2 : Fin 4) = 0 then α + 3 else -1)
    rw [hmv 2]
    rw [if_pos rfl, if_neg hne10, if_neg hne20, if_neg hne30]
    rw [h20, h21, h22, h23]
    rw [if_neg hne20]
    ring
  · show ((compiledGadget α 4).mulVec
        (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 0)) 3
        = (if (3 : Fin 4) = 0 then α + 3 else -1)
    rw [hmv 3]
    rw [if_pos rfl, if_neg hne10, if_neg hne20, if_neg hne30]
    rw [h30, h31, h32, h33]
    rw [if_neg hne30]
    ring

/-- **`mulVec` of the 2×2 compiled gadget on the all-ones vector.**

Multiplying `compiledGadget α 2` by the all-ones vector `(1, 1)`
returns `(α, α)`. Each row sums to
`(α + 1) * 1 + (-1) * 1 = α`.

This is the specialisation of `compiledGadget_mulVec_one` to `n = 2`,
i.e. the all-ones vector is an eigenvector with eigenvalue `α`. -/
theorem compiledGadget_mulVec_allOnes_n2 (α : ℝ) :
    (compiledGadget α 2).mulVec (fun _ : Fin 2 => (1 : ℝ))
      = (fun _ : Fin 2 => α) :=
  compiledGadget_mulVec_one α 2

/-- **`mulVec` of the 3×3 compiled gadget on the all-ones vector.**

Multiplying `compiledGadget α 3` by the all-ones vector `(1, 1, 1)`
returns `(α, α, α)`. Each row sums to
`(α + 2) * 1 + (-1) * 1 + (-1) * 1 = α`.

This is the specialisation of `compiledGadget_mulVec_one` to `n = 3`,
i.e. the all-ones vector is an eigenvector with eigenvalue `α`. -/
theorem compiledGadget_mulVec_allOnes_n3 (α : ℝ) :
    (compiledGadget α 3).mulVec (fun _ : Fin 3 => (1 : ℝ))
      = (fun _ : Fin 3 => α) :=
  compiledGadget_mulVec_one α 3

end PallLean.Paper93.DeepMath.PathB.Positroid
