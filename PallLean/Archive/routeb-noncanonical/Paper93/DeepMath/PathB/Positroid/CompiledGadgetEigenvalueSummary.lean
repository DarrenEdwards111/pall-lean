import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Combined eigenvalue summary: compiledGadget has spectrum {α} ∪ {α+n repeated}. -/
theorem compiledGadget_spectrum_summary (α : ℝ) (n : ℕ) :
    -- (1) all-ones is eigenvector with eigenvalue α
    ((compiledGadget α n).mulVec (fun _ => (1 : ℝ)) = (fun _ => α)) ∧
    -- (2) sum-zero vectors are eigenvectors with eigenvalue α+n
    (∀ v : Fin n → ℝ, ∑ i, v i = 0 →
       (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_mulVec_one α n
  · intros v hv
    exact compiledGadget_mulVec_sumZero α n v hv

/-- Existence of an eigenvector pair: all-ones (eigenvalue α) and a non-trivial sum-zero (eigenvalue α+n). -/
theorem exists_two_eigenvectors_compiledGadget (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = α • v) ∧
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v) := by
  refine ⟨?_, ?_⟩
  · exact exists_eigenvector_alpha α n (by omega : 1 ≤ n)
  · exact exists_eigenvector_alpha_plus_n α n hn

end PallLean.Paper93.DeepMath.PathB.Positroid
