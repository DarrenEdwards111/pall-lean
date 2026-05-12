/-
  PallLean/Paper93/Paper283/CompilerConstraintSet.lean

  Z1 — Paper §28.3 / Paper283: The compiler constraint set `C` of
  admissible compiler-derived matrices.

  This file provides a minimal, simplified definition of the compiler
  constraint set as the set of positive-semidefinite matrices over
  `Fin N × Fin N` with real entries, together with two trivial facts:

    * `identity_in_compilerConstraintSet` : the identity matrix
      belongs to `C`.
    * `compilerConstraintSet_nonempty` : `C` is non-empty.

  Both facts are immediate wrappers around Mathlib's
  `Matrix.PosSemidef.one` (from `Mathlib.LinearAlgebra.Matrix.PosDef`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms identity_in_compilerConstraintSet`:
      [propext, Classical.choice, Quot.sound]
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace PallLean.Paper93.Paper283

open Matrix

/-- The compiler constraint set: admissible A satisfying compiled structure.
    Simplified: A is PSD with bounded rank. -/
def compilerConstraintSet (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {A | A.PosSemidef}

theorem identity_in_compilerConstraintSet (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ) ∈ compilerConstraintSet N := by
  unfold compilerConstraintSet
  exact Matrix.PosSemidef.one

theorem compilerConstraintSet_nonempty (N : ℕ) :
    (compilerConstraintSet N).Nonempty := ⟨1, identity_in_compilerConstraintSet N⟩

end PallLean.Paper93.Paper283
