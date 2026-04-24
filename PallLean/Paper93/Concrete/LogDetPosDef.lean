/-
  PallLean/Paper93/Concrete/LogDetPosDef.lean

  Log-determinant properties on positive-definite matrices.

  This module bridges the concrete `matrixLogDet` wrapper (Paper §18's
  log-determinant barrier; see `PallLean.Paper93.Concrete.LogDet`) with
  Mathlib's spectral theory of positive-(semi)definite matrices
  (`Matrix.PosDef`, `Matrix.PosDef.det_pos`, `Real.log_prod`).

  ## Contents

  * `posDef_det_pos` — a positive-definite `n × n` real matrix has
    strictly positive determinant, so `log (det M)` is well-defined in
    the usual `Real.log` convention.

  * `logDet_diagonal_posDef` — the log-determinant of a diagonal matrix
    with strictly positive diagonal entries equals the sum of the
    pointwise logarithms of those entries.

  * `logDet_one` — the identity matrix has log-determinant zero,
    delegating to `matrixLogDet_identity` from `LogDet.lean`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PallLean.Paper93.Concrete.LogDet

namespace PallLean.Paper93.Concrete

open Matrix Real

/-- For a PosDef matrix, det > 0 so log(det) is well-defined. -/
theorem posDef_det_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) : 0 < M.det :=
  hM.det_pos

/-- Log-det of diagonal PosDef matrix. -/
theorem logDet_diagonal_posDef {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    matrixLogDet (Matrix.diagonal d) = ∑ i, Real.log (d i) := by
  unfold matrixLogDet
  rw [Matrix.det_diagonal]
  exact Real.log_prod (s := Finset.univ) (f := d)
    (fun i _ => ne_of_gt (hd i))

/-- Identity has log-det 0. -/
theorem logDet_one (n : ℕ) : matrixLogDet (1 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
  matrixLogDet_identity n

end PallLean.Paper93.Concrete
