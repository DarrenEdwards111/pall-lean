import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.StarOrdered

namespace PallLean.Paper93.DeepMath.PathB

/-- Paper §7.1 amplituhedron gauge property: a matrix A satisfies "gauge" if
    (a) it is positive definite and (b) every principal minor at indices
    in a designated family J is 1. -/
def IsAmplituhedronGauge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) : Prop :=
  A.PosDef ∧ ∀ J ∈ 𝒥, ∀ (e : Fin J.card ≃ {i // i ∈ J}),
    (A.submatrix (fun i => (e i).1) (fun i => (e i).1)).det = 1

/-- Identity matrix is a gauge for the empty family. -/
theorem identity_isAmplituhedronGauge_empty {n : ℕ} :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) ∅ := by
  refine ⟨Matrix.PosDef.one, ?_⟩
  intros J hJ
  exact absurd hJ (Finset.notMem_empty J)

end PallLean.Paper93.DeepMath.PathB
