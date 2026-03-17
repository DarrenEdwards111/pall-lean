/-
  SwitchingLemma.lean — Universal SPDP Collapse (Paper Theorem 92)

  The P-side collapse theorem: every P-time function has SPDP rank ≤ √n
  at κ = ℓ = log₂ n under the universal restriction.

  Derived from BoolCircuit.ptime_spdp_collapse, which encapsulates
  the paper's profile compression argument (Sections 9, 17.3).
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.Depth4Simulation
import PallLean.BoolEval
import PallLean.TuringMachine
import PallLean.BoolCircuit
import Mathlib.Tactic

namespace SwitchingLemma

open MvPolynomial SPDP RestrictedSPDP Restriction Depth4Simulation BoolEval

/-- Paper Theorem 92 (Universal SPDP Collapse):
    For any DTM M, there exists n₀ such that for all n ≥ n₀,
    every function decided by M has SPDP rank ≤ √n.

    This is a direct restatement of BoolCircuit.ptime_spdp_collapse
    for downstream compatibility. -/
theorem universal_spdp_collapse (M : TuringMachine.DTM) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool),
      M.decides f →
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n :=
  BoolCircuit.ptime_spdp_collapse M

end SwitchingLemma
