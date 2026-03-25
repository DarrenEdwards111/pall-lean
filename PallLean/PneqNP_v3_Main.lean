import PallLean.PneqNP_v3
import PallLean.CompiledInstance

/-!
Canonical main theorem wrapper after instance-aware refactor.

This file makes the instance-aware route the preferred top-level statement,
while keeping legacy `PneqNP_v3.P_neq_NP` available for comparison.
-/

namespace PneqNP_v3_Main

open PneqNP_Defs

/-- Canonical main theorem (instance-aware compiled polynomial route). -/
theorem P_neq_NP : ¬ P_eq_NP := by
  exact PneqNPv3.P_neq_NP_inst

/-- Legacy theorem from the old non-instance route (kept for compatibility). -/
theorem P_neq_NP_legacy : ¬ P_eq_NP := by
  exact PneqNP_v3.P_neq_NP

end PneqNP_v3_Main
