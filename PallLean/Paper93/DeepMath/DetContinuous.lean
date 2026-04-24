import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Continuity of the determinant on `N × N` real matrices

This file exposes a thin wrapper around Mathlib's continuity lemma for the
determinant, specialised to square real matrices indexed by `Fin N`.

Mathlib provides the general fact `Continuous.matrix_det`, which states that
if `A : X → Matrix n n R` is continuous (with `R` a topological commutative
ring) then `x ↦ (A x).det` is continuous.  Applying this lemma to
`A = id` immediately yields continuity of `Matrix.det` as a function
`Matrix (Fin N) (Fin N) ℝ → ℝ`.

Namespace: `PallLean.Paper93.DeepMath`.
-/

namespace PallLean.Paper93.DeepMath

/--
The determinant map `Matrix (Fin N) (Fin N) ℝ → ℝ` is continuous.

This is the `Fin N`-indexed real specialisation of Mathlib's
`Continuous.matrix_det` applied to the identity, which expands
`Matrix.det` via `Matrix.det_apply` as a finite sum over permutations of
products of matrix entries, each of which is continuous in the matrix.
-/
theorem matrix_det_continuous (N : ℕ) :
    Continuous (Matrix.det : Matrix (Fin N) (Fin N) ℝ → ℝ) :=
  Continuous.matrix_det (continuous_id)

end PallLean.Paper93.DeepMath
