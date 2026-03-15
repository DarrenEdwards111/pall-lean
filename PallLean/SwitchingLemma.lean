/-
  SwitchingLemma.lean — Universal SPDP Collapse (Paper Theorem 7.3)

  Paper Theorem 7.3: Every P-time function collapses to low SPDP rank
  under the universal restriction ρ*, for sufficiently large n.

  Combines: Cook-Levin + Agrawal-Vinay depth-4 + Håstad switching + union bound.

  NOTE: The paper's argument is asymptotic. At small n (e.g. n=2),
  the bound Nat.sqrt n = 1 is violated by non-constant restricted functions.
  We therefore state the axiom with a threshold n₀ below which it need not hold.
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.Depth4Simulation
import PallLean.BoolEval
import PallLean.TuringMachine
import Mathlib.Tactic

namespace SwitchingLemma

open MvPolynomial SPDP RestrictedSPDP Restriction Depth4Simulation BoolEval

/-- Paper Theorem 7.3 (Universal SPDP Collapse):
    There exists a threshold n₀ such that for every DTM M and n ≥ n₀,
    M's function has restricted SPDP rank ≤ √n under ρ*.

    The bound √n is a coarsening of the paper's O(log² N).
    The threshold n₀ absorbs the constants from Cook-Levin, depth-4 reduction,
    and the switching lemma. -/
axiom universal_spdp_collapse :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool)
      (M : TuringMachine.DTM) (_ : M.decides f),
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n

end SwitchingLemma
