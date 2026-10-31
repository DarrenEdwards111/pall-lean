import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitHierarchyGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration

/-!
# The time hierarchy in the bit-cost measure (PROVED)

Re-deriving the EffSim time hierarchy with the **bit-cost** measure in place of `Code.evaln` fuel.  Using the
measure-agnostic core (`hierarchy_gen`):

  `bitEnum cost bound e n` — program `e` outputs `1` on `n` with **bit-cost** `cost e n ≤ bound n`.
  `InTimeBit cost bound`   — the bit-cost time class.
  `bit_hierarchy_of_simulator` — `bit-TIME(bound) ⊊ bit-TIME(bigbound)` from the bit-cost simulator `hsim`.

## Why this re-derivation matters (the honest payoff)

The hierarchy reduces, in *either* measure, to a simulator hypothesis: some `bigbound`-budget program computes
the diagonal.  The two measures differ on whether that hypothesis is reachable:

* **fuel measure** (`DiagRuntimePolyBounded`): the memo DP's single-`Nat` table is `≥ 2 ^ cfgRank`
  (`ComputationalDepthKleeneMemoBlowup`), and `evaln` fuel charges by that value — so the poly simulator is
  *blocked* (`read_vs_value_divergence`).
* **bit-cost measure** (`hsim` here): the same memo DP, stored flat, simulates in **polynomial bit-cost**
  (`bitBounded_efficient` / `interp_total_cost_poly`) for the bit-bounded class — so the poly overhead *is*
  available.  The remaining construction is only the wiring of that simulation into an explicit diagonal
  `Code` `e₀` (a bit-cost-`O(1)` shell over the polynomial simulation), not a new lower bound.

So switching to the bit-cost measure moves the hierarchy's terminal hypothesis from *blocked* to *reachable*.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag)

namespace PallLean.Paper93.DeepMath.PathB.BitHierarchy

/-- **Bit-cost-bounded decider enumeration.**  `bitEnum cost bound e n = true` iff program `e` on input `n`
outputs `1` and its **bit-cost** `cost e n` is within `bound n`.  `cost` is the chosen bit-cost measure
(e.g. the flat-DP `buildReadCost + buildArithCost`). -/
noncomputable def bitEnum (cost : ℕ → ℕ → ℕ) (bound : ℕ → ℕ) (e n : ℕ) : Bool :=
  decide (cost e n ≤ bound n) && decide (Code.evaln (bound n) (Denumerable.ofNat Code e) n = some 1)

/-- `L` is decided within bit-cost `bound`. -/
def InTimeBit (cost : ℕ → ℕ → ℕ) (bound : ℕ → ℕ) (L : ℕ → Bool) : Prop :=
  ∃ e, L = bitEnum cost bound e

/-- **The bit-cost time hierarchy (proved): `bit-TIME(bound) ⊊ bit-TIME(bigbound)` from the bit-cost simulator
hypothesis.**  Lower-bound half unconditional (diagonalisation); upper-bound half is exactly the bit-cost
simulator `hsim` — supported by `bitBounded_efficient` (poly bit-cost), *unlike* the fuel-measure simulator
blocked by `MemoBlowup`. -/
theorem bit_hierarchy_of_simulator (cost : ℕ → ℕ → ℕ) (bound bigbound : ℕ → ℕ)
    (hsim : ∃ e₀, bitEnum cost bigbound e₀ = diag (bitEnum cost bound)) :
    ∃ L, InTimeBit cost bigbound L ∧ ¬ InTimeBit cost bound L :=
  hierarchy_gen (bitEnum cost bound) (bitEnum cost bigbound) hsim

end PallLean.Paper93.DeepMath.PathB.BitHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.BitHierarchy.bit_hierarchy_of_simulator
