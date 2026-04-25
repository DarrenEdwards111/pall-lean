import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Principal minor of the compiled gadget at a singleton subset

This file proves the explicit formula for the principal minor of
`compiledGadget α n` at a singleton subset `{i} : Finset (Fin n)`.

The principal submatrix at `{i}` is the `1 × 1` matrix `[[M i i]]`, whose
determinant equals `M i i`.  Combined with `compiledGadget_diagonal`, this
gives:
`(compiledGadget α n).submatrix … {i} = α + (n - 1)`.

We isolate the general fact for arbitrary square matrices (any singleton
principal minor equals the corresponding diagonal entry) and then specialise
to the compiled gadget.

A corollary fixes the value of `α` forced by the unit singleton-minor
constraint, namely `α = 2 - n`, providing the singleton-level analogue of
`compiledGadget_diagonal_eq_one_iff`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- The subtype `↥({i} : Finset (Fin n))` has a unique inhabitant, namely
`⟨i, Finset.mem_singleton.mpr rfl⟩`.  We expose this `Unique` instance
locally so that `Matrix.det_unique` applies to the singleton-indexed
principal submatrix. -/
local instance singletonFinsetUnique {n : ℕ} (i : Fin n) :
    Unique ({i} : Finset (Fin n)) where
  default := ⟨i, Finset.mem_singleton.mpr rfl⟩
  uniq := by
    rintro ⟨j, hj⟩
    have hji : j = i := Finset.mem_singleton.mp hj
    subst hji
    rfl

/-- **Principal minor of any matrix at a singleton equals the diagonal entry.**

For any square matrix `M : Matrix (Fin n) (Fin n) ℝ` and any index `i`, the
principal submatrix at the singleton subset `{i}` is the `1 × 1` matrix whose
single entry is `M i i`, so its determinant is `M i i`.

Proof: the index type `↥({i} : Finset (Fin n))` is `Unique` with unique
inhabitant `⟨i, …⟩`, so `Matrix.det_unique` reduces the determinant to the
single submatrix entry, which by `submatrix` unfolding is `M i i`. -/
theorem principalMinor_singleton {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) :
    (M.submatrix
        (fun (j : ({i} : Finset (Fin n))) => j.val)
        (fun (j : ({i} : Finset (Fin n))) => j.val)).det = M i i := by
  -- The principal submatrix is `1 × 1` with diagonal entry `M i i`.
  rw [Matrix.det_unique]
  -- After `det_unique`, the goal is the value of the submatrix at `(default,
  -- default)`, which by definition of `submatrix` is `M default.val default.val`.
  -- The unique inhabitant has `.val = i`, so this is `M i i` by `rfl`.
  rfl

/-- **Principal minor of `compiledGadget α n` at a singleton.**

For every index `i : Fin n`, the principal minor of `compiledGadget α n` at
the singleton subset `{i}` equals `α + (n - 1)`.

Proof: combine `principalMinor_singleton` (which reduces the singleton minor
to the diagonal entry) with `compiledGadget_diagonal` (which evaluates the
diagonal entry of the compiled gadget). -/
theorem compiledGadget_singleton_minor (α : ℝ) (n : ℕ) (i : Fin n) :
    (compiledGadget α n |>.submatrix
        (fun (j : ({i} : Finset (Fin n))) => j.val)
        (fun (j : ({i} : Finset (Fin n))) => j.val)).det
      = α + ((n : ℝ) - 1) := by
  rw [principalMinor_singleton, compiledGadget_diagonal]

/-- **Singleton minor equals one iff `α = 2 - n`.**

The singleton principal minor of `compiledGadget α n` at any `{i}` equals `1`
iff `α = 2 - n`.  This is the singleton-level analogue of
`compiledGadget_diagonal_eq_one_iff`: enforcing the unit singleton-minor
condition forces a *negative* coupling for `n ≥ 3`, structurally obstructing
positive-definiteness of the compiled gadget at the singleton scale. -/
theorem compiledGadget_singleton_minor_eq_one_iff (α : ℝ) (n : ℕ) (i : Fin n) :
    (compiledGadget α n |>.submatrix
        (fun (j : ({i} : Finset (Fin n))) => j.val)
        (fun (j : ({i} : Finset (Fin n))) => j.val)).det = 1
      ↔ α = 2 - (n : ℝ) := by
  rw [compiledGadget_singleton_minor]
  constructor <;> intro h <;> linarith

end PallLean.Paper93.DeepMath.PathB
