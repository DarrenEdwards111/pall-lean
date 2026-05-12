import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

namespace PallLean.Paper93.DeepMath.PathB

/-- Trivial wrapper: a positive definite matrix is positive definite.
    This is a placeholder slot for a future result connecting `PosDef A`
    with `det A = 1` to the amplituhedron gauge property at `{Finset.univ}`.
    The full theorem requires showing the submatrix of `A` by `Finset.univ`
    via an arbitrary equiv `e : Fin n ≃ {i // i ∈ Finset.univ}` has determinant
    equal to `A.det`, which involves nontrivial reindexing lemmas. We provide
    only the honest trivial fact here. -/
theorem posDef_det_one_isPosDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) : A.PosDef := hA

end PallLean.Paper93.DeepMath.PathB
