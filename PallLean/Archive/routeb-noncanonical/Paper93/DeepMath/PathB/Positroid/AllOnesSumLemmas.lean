import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Basic all-ones sum identities over `Fin n`

This file provides the elementary sum identities used by the spectral
path for the compiled gadget. They are direct consequences of
`Finset.sum_const`, `Finset.card_univ`, and `Fintype.card_fin`, but we
factor them out as named lemmas so that downstream files can `rw` (or
`simp [...]`) against them without re-proving the same combinatorial
identity each time.

The three lemmas provided are:

* `sum_one_fin (n : ℕ) :
    ∑ _ ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) = n`
  – the basic "sum of `1`'s over `Fin n` is `n`" identity.

* `dotProduct_one_one_fin (n : ℕ) :
    dotProduct
      (Function.const (Fin n) (1 : ℝ))
      (Function.const (Fin n) 1) = n`
  – the dot product of the all-ones vector with itself, which expands
    via the definition of `dotProduct` to a sum of `1 * 1 = 1`'s
    over `Fin n`.

* `dotProduct_const_one_fin (c : ℝ) (n : ℕ) :
    dotProduct
      (Function.const (Fin n) c)
      (Function.const (Fin n) 1) = c * n`
  – the dot product of a constant-`c` vector with the all-ones vector,
    which expands to a sum of `c * 1 = c`'s over `Fin n`.

These identities feed directly into the matrix-level eigenvalue/spectral
calculations for the compiled gadget on the all-ones vector.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open scoped BigOperators

/-- **Sum of `1`'s over `Fin n` is `n`.**

This is a direct consequence of `Finset.sum_const`,
`Finset.card_univ`, and `Fintype.card_fin`: the sum
`∑ _ ∈ Finset.univ, (1 : ℝ)` equals `(Finset.univ : Finset (Fin n)).card • (1 : ℝ)`,
which equals `n • (1 : ℝ) = n`. -/
theorem sum_one_fin (n : ℕ) :
    ∑ _ ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) = n := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- **All-ones dot all-ones is `n`.**

For the `dotProduct` of the all-ones vector with itself over
`Fin n`, we have
`dotProduct (Function.const _ 1) (Function.const _ 1) = n`.

The proof unfolds `dotProduct` and `Function.const`, leaving a
sum of `1 * 1 = 1`'s over `Fin n`, then applies `Finset.sum_const`,
`Finset.card_univ`, and `Fintype.card_fin`. -/
theorem dotProduct_one_one_fin (n : ℕ) :
    dotProduct
      (Function.const (Fin n) (1 : ℝ))
      (Function.const (Fin n) 1) = n := by
  -- Unfold `dotProduct` and `Function.const`:
  --   ∑ i, (Function.const _ 1 i) * (Function.const _ 1 i)
  --     = ∑ i, 1 * 1 = ∑ i, 1.
  simp only [dotProduct, Function.const_apply, mul_one]
  -- Now reduce to `sum_one_fin`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- **Constant-`c` dot all-ones is `c * n`.**

For the `dotProduct` of a constant-`c` vector with the all-ones
vector over `Fin n`, we have
`dotProduct (Function.const _ c) (Function.const _ 1) = c * n`.

The proof unfolds `dotProduct` and `Function.const`, leaving a
sum of `c * 1 = c`'s over `Fin n`, then applies `Finset.sum_const`,
`Finset.card_univ`, and `Fintype.card_fin`, and finally `ring` to land
on `c * n`. -/
theorem dotProduct_const_one_fin (c : ℝ) (n : ℕ) :
    dotProduct
      (Function.const (Fin n) c)
      (Function.const (Fin n) 1) = c * n := by
  -- Unfold `dotProduct` and `Function.const`:
  --   ∑ i, (Function.const _ c i) * (Function.const _ 1 i)
  --     = ∑ i, c * 1 = ∑ i, c.
  simp only [dotProduct, Function.const_apply, mul_one]
  -- `∑ i ∈ Finset.univ, c = (Finset.univ : Finset (Fin n)).card • c = n • c = c * n`.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]

end PallLean.Paper93.DeepMath.PathB.Positroid
