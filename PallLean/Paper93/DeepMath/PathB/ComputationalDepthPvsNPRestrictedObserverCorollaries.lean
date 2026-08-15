import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanQueryMERACompiler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityAC0pClass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCapstone

/-!
# Restricted observer lower-bound corollaries

This downstream module collects the bounded-bond/log-depth MERA consequences
next to the holographic observer development without introducing an import
cycle.  These are restricted-model results; no compilation of arbitrary
polynomial-time SAT machines into MERA is assumed.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler

/-- Above the polynomial state ceiling of a fixed bounded-bond, fixed-cone,
logarithmic-depth MERA family, no exact Ramanujan-routed transcript of the
independent SAT-query batch exists for a SAT-correct decision machine. -/
theorem no_boundedMERA_routed_SAT_transcript_at_gap
    {n : Nat} {U : MachineModel} {D : DecisionMachine U}
    (M : MERAFamily)
    (hn : 1 ≤ n) (hgap : n ^ M.polyExponent < 2 ^ n)
    (hD : DecidesSAT U D) :
    ¬ Nonempty (RamanujanMERAQueryTranscript (n := n) D M) := by
  exact RamanujanMERAQueryTranscript.no_routed_transcript_at_size M hn hgap hD

/-- No SAT-correct decision machine has an all-size exact compiler into one
fixed bounded-bond, fixed-cone, logarithmic-depth MERA family. -/
theorem no_boundedMERA_compiler_for_SAT
    {U : MachineModel} {D : DecisionMachine U}
    (C : RamanujanQueryMERACompiler U D) :
    ¬ DecidesSAT U D := by
  exact C.not_decidesSAT

/-! ## Small bounded-depth modular circuits -/

open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPParityAC0pClass

/-- Razborov--Smolensky restricted-model cash-out: under the explicit prime,
degree, size, and input-length regime, no SAT decision machine has a circuit
of depth at most `d` and size below `lower` in `AC⁰[p]` that realizes its
answers on the parity-CNF family. -/
theorem no_smallAC0p_realization_for_parityCNF_SAT
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 ≤ t) (hpt : 1 ≤ (p - 1) * t)
    (hlow : 4 * lower ≤ p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 ≤ m) :
    ¬ SATDecisionInClass (SmallAC0pParityClass U p m d lower) := by
  exact no_SATDecisionInClass_smallAC0pParity
    U p m t d lower hp2 ht1 hpt hlow hm

/-! ## De Morgan formulas -/

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard

/-- Headline Nečiporuk family lower bound.  At every block exponent `b ≥ 5`
there is an explicit `hardF` instance on `N = nn b m` variables for which
every De Morgan (`B₂`) formula requires at least `N²/(64b)` literal leaves. -/
theorem exists_hardF_quadratic_over_log_formula_lower_bound
    (b : Nat) (hb : 5 ≤ b) :
    ∃ m, ∀ (F : BFormula (nn b m)),
      (∀ x, BFormula.eval F x = hardF x) →
      (nn b m) ^ 2 / (64 * b) ≤ BFormula.litCount F := by
  exact hardF_rate_opt_family b hb

end PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.no_boundedMERA_routed_SAT_transcript_at_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.no_boundedMERA_compiler_for_SAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.no_smallAC0p_realization_for_parityCNF_SAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.exists_hardF_quadratic_over_log_formula_lower_bound
