/-
  DiamondTest.lean — Axiom inventory for P_neq_NP
-/
import PallLean.CompiledSeparation

#print axioms CompiledSeparation.P_neq_NP
-- Expected:
-- propext, Classical.choice, Quot.sound (standard Lean)
-- CompiledSeparation.cookLevin_rank_bound (paper §11-13)
-- PneqNP_Paper.f_n_family_in_NP (paper §8.6)
-- SupportedDim.finrank_restrictSupportDeg_le (proved, axiomatized for diamond safety)
-- ProfileCompression.scaffold_blockClosure_card_le (|blockClosure| ≤ 24)
