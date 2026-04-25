import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Toy bounded affine permutation (positroid building block)

A *bounded affine permutation* of `[n]` is a bijection `f : ℤ → ℤ` such that
`f(i+n) = f(i)+n` and `i ≤ f(i) ≤ i + n`.  Such permutations index positroid
cells in the Grassmannian `Gr(k,n)`.

This file provides a toy version on `Fin n`: a permutation
`σ : Fin n ≃ Fin n`.  We package this as a `DecorationMap`, and prove four
basic structural lemmas (identity is self-inverse, identity is a left/right
unit for composition, and inversion is involutive).

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A toy "decoration map" `Fin n → Fin n` capturing a single positroid cell.
    The non-positroid version: any permutation `σ : Fin n ≃ Fin n`. -/
abbrev DecorationMap (n : ℕ) := Fin n ≃ Fin n

/-- The identity decoration: `σ = id`. -/
def identityDecoration (n : ℕ) : DecorationMap n := Equiv.refl (Fin n)

/-- Two decorations compose. -/
def composeDecorations {n : ℕ} (σ τ : DecorationMap n) : DecorationMap n :=
  σ.trans τ

/-- The inverse of a decoration. -/
def invertDecoration {n : ℕ} (σ : DecorationMap n) : DecorationMap n := σ.symm

/-- The identity decoration is involutive (its inverse is itself). -/
theorem invertDecoration_identity (n : ℕ) :
    invertDecoration (identityDecoration n) = identityDecoration n := by
  rfl

/-- Composing with the identity on the left is the identity. -/
theorem composeDecorations_id_left {n : ℕ} (σ : DecorationMap n) :
    composeDecorations (identityDecoration n) σ = σ := by
  unfold composeDecorations identityDecoration
  exact Equiv.refl_trans σ

/-- Composing with the identity on the right is the identity. -/
theorem composeDecorations_id_right {n : ℕ} (σ : DecorationMap n) :
    composeDecorations σ (identityDecoration n) = σ := by
  unfold composeDecorations identityDecoration
  exact Equiv.trans_refl σ

/-- Inverting twice gives the identity. -/
theorem invertDecoration_invertDecoration {n : ℕ} (σ : DecorationMap n) :
    invertDecoration (invertDecoration σ) = σ := by
  unfold invertDecoration
  exact σ.symm_symm

end PallLean.Paper93.DeepMath.PathB.Positroid
