import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The compiled gadget is never the identity matrix for `n ≥ 2`

This file establishes that for any real `α` and any `n ≥ 2`, the compiled
gadget
`compiledGadget α n = α • I + L_{K_n}`
is **not** equal to the identity matrix on `Fin n`.

The argument is purely structural: at the off-diagonal `(0, 1)` position
(which is well-defined since `n ≥ 2`), the compiled gadget evaluates to
`-1`, while the identity matrix evaluates to `0`. The smul-by-`α` term
contributes nothing off the diagonal because the identity matrix
vanishes there, and the Laplacian off-diagonal is
`(diagonal (rowSum A)) 0 1 - completeAdj n 0 1 = 0 - 1 = -1`.

This generalises the previously-proved `compiledGadget_2x2_ne_identity`
to all `n ≥ 2`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral
open Matrix

/-- For `n ≥ 2`, the indices `0` and `1` are distinct in `Fin n`. -/
private lemma fin_zero_ne_one_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
  intro h
  have hval : (⟨0, by omega⟩ : Fin n).val = (⟨1, by omega⟩ : Fin n).val :=
    congrArg Fin.val h
  simp at hval

/-- The (0, 1) entry of `completeAdj n` equals `1` for `n ≥ 2`. -/
private lemma completeAdj_zero_one_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    completeAdj n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 1 := by
  unfold completeAdj
  have h : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) :=
    fin_zero_ne_one_of_two_le hn
  simp [h]

/-- The (0, 1) entry of the row-sum diagonal of `completeAdj n` is `0`,
because the off-diagonal of any matrix of the form `Matrix.diagonal d`
vanishes. -/
private lemma diagonal_rowSum_completeAdj_zero_one_of_two_le
    (n : ℕ) (hn : 2 ≤ n) :
    (Matrix.diagonal (rowSum (completeAdj n)))
        (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 0 := by
  exact Matrix.diagonal_apply_ne _ (fin_zero_ne_one_of_two_le hn)

/-- The (0, 1) entry of the identity matrix on `Fin n` is `0` for
`n ≥ 2`. -/
private lemma one_apply_zero_one_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    (1 : Matrix (Fin n) (Fin n) ℝ)
        (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 0 :=
  Matrix.one_apply_ne (fin_zero_ne_one_of_two_le hn)

/-- **The (0, 1) off-diagonal entry of the compiled gadget equals `-1`.**

For every `α : ℝ` and every `n ≥ 2`,
`compiledGadget α n ⟨0, _⟩ ⟨1, _⟩ = -1`.

The proof unfolds `compiledGadget` to `α • I + L_{K_n}`, evaluates
entrywise at `(0, 1)`, and uses the off-diagonal vanishing of the
identity matrix together with
`(L_{K_n}) 0 1 = (diagonal (rowSum A)) 0 1 - A 0 1 = 0 - 1 = -1`. -/
theorem compiledGadget_off_diag_01 (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    compiledGadget α n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
      = -1 := by
  -- Unfold the definition `α • 1 + laplacian (completeAdj n)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n))
          (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
        = (α • (1 : Matrix (Fin n) (Fin n) ℝ))
              (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
          + (laplacian (completeAdj n))
              (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := rfl
  rw [hadd]
  -- `(α • I) 0 1 = α • (I 0 1) = α • 0 = 0`.
  have hsmul :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ))
          (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 0 := by
    show α • ((1 : Matrix (Fin n) (Fin n) ℝ)
        (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)) = 0
    rw [one_apply_zero_one_of_two_le n hn]
    simp
  rw [hsmul]
  -- `(L_{K_n}) 0 1 = (diagonal (rowSum A)) 0 1 - A 0 1 = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj n))
          (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj n)) - completeAdj n)
              (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
          = (Matrix.diagonal (rowSum (completeAdj n)))
                (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
              - (completeAdj n)
                (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := rfl
    rw [hsub,
        diagonal_rowSum_completeAdj_zero_one_of_two_le n hn,
        completeAdj_zero_one_of_two_le n hn]
    ring
  rw [hlap]
  ring

/-- **The compiled gadget is never the identity for `n ≥ 2`.**

For every `α : ℝ` and every `n ≥ 2`,
`compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)`.

The proof compares the `(0, 1)` entries:

* `compiledGadget α n ⟨0, _⟩ ⟨1, _⟩ = -1` by
  `compiledGadget_off_diag_01`,
* `(1 : Matrix (Fin n) (Fin n) ℝ) ⟨0, _⟩ ⟨1, _⟩ = 0` by
  `Matrix.one_apply_ne`,

and `(-1 : ℝ) ≠ 0`. -/
theorem compiledGadget_ne_identity (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro h_eq
  -- Compare entry (0, 1): compiledGadget = -1, identity = 0.
  have h01 :
      compiledGadget α n
          (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
        = (1 : Matrix (Fin n) (Fin n) ℝ)
          (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
    rw [h_eq]
  rw [compiledGadget_off_diag_01 α n hn] at h01
  rw [one_apply_zero_one_of_two_le n hn] at h01
  -- h01 : (-1 : ℝ) = 0
  linarith

end PallLean.Paper93.DeepMath.PathB.Positroid
