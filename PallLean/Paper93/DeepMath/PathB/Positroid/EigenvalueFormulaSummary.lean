import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetOrthogonalEigenvec
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Combined eigenvalue spectrum of compiledGadget α n: {α} ∪ {α + n} (with multiplicity n-1). -/
theorem compiledGadget_eigenvalue_spectrum (α : ℝ) (n : ℕ) :
    -- (1) all-ones is α-eigenvector
    ((compiledGadget α n).mulVec (fun _ => (1 : ℝ)) = (fun _ => α)) ∧
    -- (2) sum-zero v is (α+n)-eigenvector
    (∀ v : Fin n → ℝ, ∑ i, v i = 0 →
       (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v) := by
  refine ⟨?_, ?_⟩
  · exact compiledGadget_mulVec_one α n
  · exact compiledGadget_mulVec_sumZero α n

/-- For n ≥ 1, ∃ a non-zero α-eigenvector. -/
theorem exists_alpha_eigenvector (α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = α • v :=
  exists_eigenvector_alpha α n hn

/-- For n ≥ 2, ∃ a non-zero (α+n)-eigenvector (sum-zero). -/
theorem exists_alpha_plus_n_eigenvector (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v :=
  exists_eigenvector_alpha_plus_n α n hn

end PallLean.Paper93.DeepMath.PathB.Positroid
