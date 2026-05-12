import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.Positroid.SubmatrixDetStructural
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Extended structural facts about principal submatrices of `compiledGadget`

This file extends `SubmatrixDetStructural.lean` by recording additional
kernel-only structural facts about principal submatrices of
`compiledGadget α n`.  The previous file proved that the diagonal `(i, i)`
entry of every principal submatrix at any `J : Finset (Fin n)` is
`α + (n - 1)`, the same diagonal value carried by the ambient
`compiledGadget α n`.  Here we pin down four further structural items:

1. `compiledGadget_principal_submatrix_off_diag` — the off-diagonal
   `(i, j)` entry of a principal submatrix (for `i ≠ j` in the index
   subtype `J`) is `-1`, inherited verbatim from the ambient gadget.

2. `compiledGadget_principal_submatrix_diag_sum` — the sum of all
   diagonal entries of the principal submatrix indexed by `J` equals
   `|J| * (α + (n - 1))`.  This is the principal-submatrix analogue of
   the trace formula, and follows from the diagonal value being
   constant across the index subtype.

3. `compiledGadget_trace_n42` and `compiledGadget_trace_n99` — explicit
   restatements of `compiledGadget_trace_formula` at `n = 42` and
   `n = 99`, two values not previously specialised in the codebase.

4. `principalMinor_singleton_eq_diag` — the principal minor at the
   singleton `{i}` equals the diagonal entry `A i i`, expressed in the
   `principalMinor` notation of `PluckerAbstract`.

All proofs are kernel-only and use no `sorry`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-! ## Off-diagonal entries of principal submatrices -/

/-- The off-diagonal entry of `completeAdj n` is `1` whenever the two
indices differ.  Direct unfolding of the `if i = j then 0 else 1`
definition. -/
private lemma completeAdj_apply_ne_local
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    completeAdj n i j = 1 := by
  unfold completeAdj
  simp [hij]

/-- **Structural off-diagonal entry of a principal submatrix.**

For every coupling `α : ℝ`, every dimension `n : ℕ`, every subset
`J : Finset (Fin n)`, and every pair `i j : J` whose underlying values
in `Fin n` differ, the `(i, j)` entry of the principal submatrix of
`compiledGadget α n` indexed by `J` along both axes equals `-1`.

The principal submatrix is `(compiledGadget α n).submatrix r r`, where
`r : J → Fin n` is the canonical inclusion `k ↦ k.val`.  By
`Matrix.submatrix_apply`, the `(i, j)` entry unfolds to
`compiledGadget α n i.val j.val`, which equals `-1` whenever
`i.val ≠ j.val` by the standard off-diagonal computation
`α • I + L_{K_n} = 0 + (0 - 1) = -1` for distinct indices. -/
theorem compiledGadget_principal_submatrix_off_diag
    (α : ℝ) (n : ℕ) (J : Finset (Fin n)) (i j : J)
    (hij : (i.val : Fin n) ≠ j.val) :
    ((compiledGadget α n).submatrix
      (fun k : J => (k.val : Fin n)) (fun k : J => (k.val : Fin n))) i j
        = -1 := by
  -- Unfold the submatrix indexing.
  show compiledGadget α n i.val j.val = -1
  -- Unfold the definition `α • 1 + laplacian (completeAdj n)`.
  unfold compiledGadget
  -- Sum is computed entrywise.
  have hadd :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ) + laplacian (completeAdj n))
          i.val j.val
        = (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i.val j.val
          + (laplacian (completeAdj n)) i.val j.val := rfl
  rw [hadd]
  -- `(α • I) i j = α • (I i j) = α • 0 = 0` since `i.val ≠ j.val`.
  have hsmul :
      (α • (1 : Matrix (Fin n) (Fin n) ℝ)) i.val j.val = 0 := by
    show α • ((1 : Matrix (Fin n) (Fin n) ℝ) i.val j.val) = 0
    rw [Matrix.one_apply_ne hij]
    simp
  rw [hsmul]
  -- `(L_{K_n}) i j = (diagonal (rowSum A)) i j - A i j = 0 - 1 = -1`.
  have hlap :
      (laplacian (completeAdj n)) i.val j.val = -1 := by
    unfold laplacian
    have hsub :
        (Matrix.diagonal (rowSum (completeAdj n)) - completeAdj n) i.val j.val
          = (Matrix.diagonal (rowSum (completeAdj n))) i.val j.val
              - (completeAdj n) i.val j.val := rfl
    rw [hsub, Matrix.diagonal_apply_ne _ hij,
        completeAdj_apply_ne_local hij]
    ring
  rw [hlap]
  ring

/-! ## Diagonal sum of principal submatrices -/

/-- **Diagonal sum of a principal submatrix equals `|J| * (α + (n - 1))`.**

For every coupling `α : ℝ`, every dimension `n : ℕ`, and every subset
`J : Finset (Fin n)`, the sum of all diagonal entries of the principal
submatrix of `compiledGadget α n` indexed by `J` along both axes is
`|J| * (α + (n - 1))`.

The proof uses the diagonal value
`compiledGadget_principal_submatrix_diag` (each diagonal entry equals
`α + (n - 1)`), then sums `|J|` constant copies via `Finset.sum_const`.
This is the principal-submatrix analogue of the trace formula
`trace (compiledGadget α n) = n * α + n * (n - 1)`. -/
theorem compiledGadget_principal_submatrix_diag_sum
    (α : ℝ) (n : ℕ) (J : Finset (Fin n)) :
    ∑ i : J, ((compiledGadget α n).submatrix
      (fun k : J => (k.val : Fin n)) (fun k : J => (k.val : Fin n))) i i
        = (J.card : ℝ) * (α + ((n : ℝ) - 1)) := by
  -- Each diagonal entry equals `α + (n - 1)` by the structural diagonal lemma.
  have hconst : ∀ i : J,
      ((compiledGadget α n).submatrix
        (fun k : J => (k.val : Fin n)) (fun k : J => (k.val : Fin n))) i i
          = α + ((n : ℝ) - 1) :=
    fun i => compiledGadget_principal_submatrix_diag α n J i
  -- Replace each summand by the constant value.
  rw [Finset.sum_congr rfl (fun i _ => hconst i)]
  -- `∑ _ : J, c = |J| • c = |J| * c`.
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Cast `Fintype.card J` back to `J.card`.
  congr 1
  exact_mod_cast (Fintype.card_coe J)

/-! ## Trace at specific dimensions not previously specialised -/

/-- **Trace of `compiledGadget α 42`.**

`trace (compiledGadget α 42) = 42 * α + 42 * 41 = 42 * α + 1722`.

This is an explicit specialisation of `compiledGadget_trace_formula` at
the dimension `n = 42`, complementing the existing `n = 3`, `n = 9`,
`n = 10`, etc. specialisations. -/
theorem compiledGadget_trace_n42 (α : ℝ) :
    (compiledGadget α 42).trace = 42 * α + 42 * 41 := by
  rw [compiledGadget_trace_formula]
  norm_num

/-- **Trace of `compiledGadget α 99`.**

`trace (compiledGadget α 99) = 99 * α + 99 * 98 = 99 * α + 9702`.

This is an explicit specialisation of `compiledGadget_trace_formula` at
`n = 99`. -/
theorem compiledGadget_trace_n99 (α : ℝ) :
    (compiledGadget α 99).trace = 99 * α + 99 * 98 := by
  rw [compiledGadget_trace_formula]
  norm_num

/-! ## Principal minor at a singleton equals the diagonal entry -/

/-- The subtype `↥({i} : Finset (Fin n))` has a unique inhabitant, namely
`⟨i, Finset.mem_singleton.mpr rfl⟩`.  We expose this `Unique` instance
locally so that `Matrix.det_unique` applies to the singleton-indexed
principal submatrix, with `default.val` reducing to `i` definitionally. -/
local instance singletonFinsetUnique_local {n : ℕ} (i : Fin n) :
    Unique ({i} : Finset (Fin n)) where
  default := ⟨i, Finset.mem_singleton.mpr rfl⟩
  uniq := by
    rintro ⟨j, hj⟩
    have hji : j = i := Finset.mem_singleton.mp hj
    subst hji
    rfl

/-- **Principal minor at a singleton subset equals the diagonal entry.**

For every square matrix `A : Matrix (Fin n) (Fin n) ℝ` and every index
`i : Fin n`, the principal minor at the singleton subset `{i}` equals
the diagonal entry `A i i`.

This is the `principalMinor`-notation analogue of
`principalMinor_singleton` from `CompiledGadgetSingletonMinor.lean`,
recast in the `PluckerAbstract.principalMinor` form: the principal
submatrix at `{i}` is a `1 × 1` matrix whose unique entry is `A i i`,
so its determinant equals `A i i`. -/
theorem principalMinor_singleton_eq_diag
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    principalMinor A ({i} : Finset (Fin n)) = A i i := by
  -- Unfold `principalMinor` to the determinant of the principal submatrix.
  unfold principalMinor
  -- `Matrix.det_unique` reduces the `1 × 1` determinant to the unique entry.
  rw [Matrix.det_unique]
  -- After `det_unique`, the goal is the value of the submatrix at
  -- `(default, default)`, which by definition of `submatrix` is
  -- `A default.val default.val = A i i`.
  rfl

/-- **Principal minor of `compiledGadget α n` at a singleton equals the
diagonal entry `α + (n - 1)`.**

Combining `principalMinor_singleton_eq_diag` with
`compiledGadget_diagonal` gives the explicit value of the singleton
principal minor of the compiled gadget under the `principalMinor`
notation. -/
theorem compiledGadget_principalMinor_singleton
    (α : ℝ) (n : ℕ) (i : Fin n) :
    principalMinor (compiledGadget α n) ({i} : Finset (Fin n))
      = α + ((n : ℝ) - 1) := by
  rw [principalMinor_singleton_eq_diag, compiledGadget_diagonal]

end PallLean.Paper93.DeepMath.PathB.Positroid
