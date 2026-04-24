import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.GraphSpectral

theorem posSemidef_has_eigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    ∃ es : Fin N → ℝ, ∀ i, 0 ≤ es i :=
  ⟨hA.1.eigenvalues, fun i => hA.eigenvalues_nonneg i⟩
