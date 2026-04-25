import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerAbstract
import PallLean.Paper93.DeepMath.PathB.Positroid.PrincipalMinorUnivDet
import PallLean.Paper93.DeepMath.PathB.Positroid.PrincipalMinorEmptyOne
import PallLean.Paper93.DeepMath.PathB.Positroid.SubmatrixDetStructuralExtended
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Principal minor of `compiledGadget` at small index sets

This kernel-only file packages four to six structural facts that
specialise the abstract `principalMinor` of `compiledGadget α n` at the
three "extreme" index sets: a singleton, the empty subset, and the
universe.  The closed-form determinant identities
`compiledGadget_5x5_det` and `compiledGadget_6x6_det` are used for the
universe case at `n = 5` and `n = 6`, while `principalMinor_empty_one`
covers the empty case and `principalMinor_singleton_eq_diag` together
with `compiledGadget_diagonal` covers the singleton case.

The lemmas collected here are:

* `principalMinor_compiledGadget_singleton` — the principal minor of
  `compiledGadget α n` at the singleton subset `{i}` equals the
  diagonal value `α + (n - 1)`.

* `principalMinor_compiledGadget_n5_univ` — the principal minor of
  `compiledGadget α 5` at `Finset.univ` equals `α * (α + 5)^4`.

* `principalMinor_compiledGadget_n6_univ` — the principal minor of
  `compiledGadget α 6` at `Finset.univ` equals `α * (α + 6)^5`.

* `principalMinor_compiledGadget_n5_empty` — the principal minor of
  `compiledGadget α 5` at the empty subset equals `1`.

* `principalMinor_compiledGadget_n6_empty` — the principal minor of
  `compiledGadget α 6` at the empty subset equals `1`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-! ## Singleton principal minor of `compiledGadget α n` -/

/-- **Principal minor of `compiledGadget α n` at a singleton subset.**

For every coupling `α : ℝ`, every dimension `n : ℕ`, and every index
`i : Fin n`, the principal minor of `compiledGadget α n` at the
singleton subset `{i}` equals the diagonal value `α + (n - 1)`.

The proof combines `principalMinor_singleton_eq_diag` (which reduces
the singleton principal minor to the diagonal entry `A i i`) with
`compiledGadget_diagonal` (which evaluates that diagonal entry of
`compiledGadget α n` to `α + ((n : ℝ) - 1)`).  The final cast from
`((n : ℝ) - 1)` to the natural-number coercion `((n - 1 : ℕ) : ℝ)`
uses the fact that `i : Fin n` forces `n ≥ 1`, which makes truncated
subtraction agree with integer subtraction. -/
theorem principalMinor_compiledGadget_singleton
    (α : ℝ) (n : ℕ) (i : Fin n) :
    principalMinor (compiledGadget α n) ({i} : Finset (Fin n))
      = α + ((n - 1 : ℕ) : ℝ) := by
  -- Reduce the singleton principal minor to the diagonal entry.
  rw [principalMinor_singleton_eq_diag, compiledGadget_diagonal]
  -- Reconcile `(n : ℝ) - 1` with `((n - 1 : ℕ) : ℝ)` using `n ≥ 1`
  -- (which is forced by the existence of `i : Fin n`).
  have hn : 1 ≤ n := i.pos
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast]

/-! ## Universe principal minor of `compiledGadget α 5` and `compiledGadget α 6` -/

/-- **Principal minor of `compiledGadget α 5` at `Finset.univ`.**

For every coupling `α : ℝ`, the principal minor of the 5×5 compiled
gadget `compiledGadget α 5` at the universe index set equals the closed
form `α * (α + 5)^4`.

The proof rewrites the universe principal minor as the determinant via
`principalMinor_univ_det`, then applies the closed-form identity
`compiledGadget_5x5_det`. -/
theorem principalMinor_compiledGadget_n5_univ (α : ℝ) :
    principalMinor (compiledGadget α 5) (Finset.univ : Finset (Fin 5))
      = α * (α + 5)^4 := by
  rw [principalMinor_univ_det, compiledGadget_5x5_det]

/-- **Principal minor of `compiledGadget α 6` at `Finset.univ`.**

For every coupling `α : ℝ`, the principal minor of the 6×6 compiled
gadget `compiledGadget α 6` at the universe index set equals the closed
form `α * (α + 6)^5`.

The proof rewrites the universe principal minor as the determinant via
`principalMinor_univ_det`, then applies the closed-form identity
`compiledGadget_6x6_det`. -/
theorem principalMinor_compiledGadget_n6_univ (α : ℝ) :
    principalMinor (compiledGadget α 6) (Finset.univ : Finset (Fin 6))
      = α * (α + 6)^5 := by
  rw [principalMinor_univ_det, compiledGadget_6x6_det]

/-! ## Empty-subset principal minor of `compiledGadget α 5` and `compiledGadget α 6` -/

/-- **Principal minor of `compiledGadget α 5` at the empty subset.**

For every coupling `α : ℝ`, the principal minor of the 5×5 compiled
gadget `compiledGadget α 5` at the empty subset equals `1`, since the
underlying `0 × 0` submatrix has empty index type and its determinant
is `1` by `Matrix.det_isEmpty`.

This is a direct specialisation of the general lemma
`principalMinor_empty_one` to the matrix `compiledGadget α 5`. -/
theorem principalMinor_compiledGadget_n5_empty (α : ℝ) :
    principalMinor (compiledGadget α 5) (∅ : Finset (Fin 5)) = 1 :=
  principalMinor_empty (compiledGadget α 5)

/-- **Principal minor of `compiledGadget α 6` at the empty subset.**

For every coupling `α : ℝ`, the principal minor of the 6×6 compiled
gadget `compiledGadget α 6` at the empty subset equals `1`, since the
underlying `0 × 0` submatrix has empty index type and its determinant
is `1` by `Matrix.det_isEmpty`.

This is a direct specialisation of the general lemma
`principalMinor_empty_one` to the matrix `compiledGadget α 6`. -/
theorem principalMinor_compiledGadget_n6_empty (α : ℝ) :
    principalMinor (compiledGadget α 6) (∅ : Finset (Fin 6)) = 1 :=
  principalMinor_empty (compiledGadget α 6)

end PallLean.Paper93.DeepMath.PathB.Positroid
