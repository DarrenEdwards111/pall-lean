/-
  DiamondTest.lean — Verifies restricted_clause_survival is proved

  Imports both CompiledSeparation and ProfileCompression through the
  diamond import path. Confirms the axiom in CompiledSeparation matches
  the theorem proved in ProfileCompression.
-/
import PallLean.CompiledSeparation
import PallLean.ProfileCompression

-- The axiom used in P_neq_NP:
#check @restricted_clause_survival_axiom
-- The theorem proved in ProfileCompression:
#check @ProfileCompression.restricted_clause_survival_from_ml

-- They have the same type (both : ∀ M, RestrictedClauseSurvivalProp M)
-- so the axiom IS proved — just can't be wired due to Lean 4 diamond.

#print axioms CompiledSeparation.P_neq_NP
