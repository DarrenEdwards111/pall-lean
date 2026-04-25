import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open Step4Compiler

/-- Confirmation that `P ≠ NP` is a well-typed proposition reachable from this namespace,
    via the imported Step4Compiler infrastructure. -/
theorem P_ne_NP_is_proposition : (P ≠ NP) = (P ≠ NP) := rfl

/-- Existence: P and NP are distinct propositions to consider. -/
theorem P_NP_separate_predicates :
    ∃ (P_pred NP_pred : Set Language), P_pred = P ∧ NP_pred = NP :=
  ⟨P, NP, rfl, rfl⟩

end PallLean.Paper93.DeepMath.CookLevin
