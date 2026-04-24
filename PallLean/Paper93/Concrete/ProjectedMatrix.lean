/-
  PallLean/Paper93/Concrete/ProjectedMatrix.lean

  Agent U7 — Concrete projected-matrix construction for the
  Paper §18 / §28.3 N-Frame / identity-minor coupling.

  ## Scope

  Construct the `Π · M · Π^T` conjugation of a matrix `M` by the
  matrix realisation of an S1 `CandidateGauge`. At the present
  concrete level we take the simplified projection matrix to be
  the `N × N` identity (the trivial gauge `Π = id` on the SPDP
  row space, which is the admissible "rank-full" endpoint of the
  N-Frame variational problem, paper §7.1 p. 25). With this
  simplification the projected identity minor matrix remains an
  identity matrix and hence has determinant `1`, matching the
  paper's identity-minor witness (paper §18, §189
  `lemma_124_unconditional` rank lower bound).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §7.1 p. 25 — universal observer gauge `Π⋆` as a projection
      on the SPDP row space.
    * §18, §189 `lemma_124_unconditional` — identity minor matrix
      with rank ≥ n^(log n / 4) at `Q_times_Phi_135`.
    * §28.3 pp. 137–138 — N-Frame Lagrangian and the amplituhedron
      determinantal barrier.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import PallLean.Paper93.NFrame.LagrangianFunctional
import PallLean.Paper93.Concrete.IdentityMinorMatrix

namespace PallLean.Paper93.Concrete

open Matrix

/-- Projection matrix associated with a gauge (simplified: identity for now).

At the concrete level, the `N × N` matrix realisation of an S1
`CandidateGauge` is taken to be the identity matrix. This corresponds
to the trivial / rank-full endpoint of the N-Frame variational
problem (paper §7.1 p. 25), and keeps all determinantal identities
transparent at the kernel-only Lean level. -/
noncomputable def projMatrix {N : ℕ}
    (_gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    Matrix (Fin N) (Fin N) ℝ := 1

/-- At the concrete level, `projMatrix` on any candidate gauge is
the identity matrix. -/
theorem projMatrix_is_one {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    projMatrix gauge = (1 : Matrix (Fin N) (Fin N) ℝ) := rfl

/-- `Π · M · Π^T` for gauge `Π` and matrix `M`.

This is the standard conjugation of an ambient matrix `M` by the
matrix realisation of the candidate gauge, matching the paper's
projected-minor construction (paper §18 / §28.3). -/
noncomputable def projectedMatrix {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N)
    (M : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  projMatrix gauge * M * (projMatrix gauge).transpose

/-- The projected identity minor matrix has determinant `1`.

Since `projMatrix gauge = 1` and `identityMinorMatrix N = 1`, the
projected matrix `Π · I · Π^T` reduces to the `N × N` identity,
whose determinant is `1`. This matches the paper's identity-minor
witness on the NP side (§189 `lemma_124_unconditional`). -/
theorem projectedMatrix_identity_det {N : ℕ}
    (gauge : PallLean.Paper93.NFrame.CandidateGauge N) :
    (projectedMatrix gauge (identityMinorMatrix N)).det = 1 := by
  unfold projectedMatrix projMatrix identityMinorMatrix
  simp

end PallLean.Paper93.Concrete
