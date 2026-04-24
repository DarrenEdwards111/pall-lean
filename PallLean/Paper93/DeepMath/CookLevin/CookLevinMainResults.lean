import PallLean.Paper93.DeepMath.CookLevin.NTM
import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.CookLevin.CompiledTMNonzero
import PallLean.Paper93.DeepMath.CookLevin.CompiledTMPocketRank
import PallLean.Paper93.DeepMath.CookLevin.TableauEmbedRank
import PallLean.Paper93.DeepMath.CookLevin.BridgeA
import PallLean.Paper93.DeepMath.CookLevin.BridgeB
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

/-!
# Cook-Levin Structural Main Results (Paper §40)

This module re-exports the main Cook-Levin / SPDP rank bound results:

- **NTM**: `NTM`, `NTMConfig`, initial/accept state predicates
- **Compiled matrix**: `compiledTMMatrix`, nonzero, rank ≥ 1
- **Pocket decomposition**: `pocketFamily`, block-diagonal rank = sum of block ranks
- **Bridge A**: each pocket rank ≥ 1 via energy-to-rank
- **Bridge B**: κ pockets ⇒ total rank ≥ κ
- **Theorem 207 chain**: rank(pocketFamily α κ n) ≥ κ
-/

namespace PallLean.Paper93.DeepMath.CookLevin

/-- Sanity check: the Cook-Levin compilation produces a nonzero, rank-at-least-1 matrix. -/
theorem cookLevin_structural_nontrivial
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ) (hα : 0 < α)
    (hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)) :
    (compiledTMMatrix numStates numSymbols numTimesteps α) ≠ 0 ∧
    1 ≤ (compiledTMMatrix numStates numSymbols numTimesteps α).rank :=
  ⟨compiledTMMatrix_ne_zero _ _ _ α hα hcard,
   compiledTMMatrix_rank_pos _ _ _ α hα hcard⟩

end PallLean.Paper93.DeepMath.CookLevin
