import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A sufficient common-span criterion, not a SAT lower bound.
The common map and row factorizations are explicit hypotheses; no claim is
made that the paper's compiler supplies them. -/

namespace CuriosityProfileAudit

theorem common_image_span_bound
    {K U V I : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (decode : U →ₗ[K] V) (rows : I → V)
    (hfactor : ∀ i, ∃ u, decode u = rows i) :
    Module.finrank K (Submodule.span K (Set.range rows)) ≤ Module.finrank K U := by
  have hspan : Submodule.span K (Set.range rows) ≤ LinearMap.range decode := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hfactor i
  exact (Submodule.finrank_mono hspan).trans (LinearMap.finrank_range_le decode)

end CuriosityProfileAudit

#print axioms CuriosityProfileAudit.common_image_span_bound
