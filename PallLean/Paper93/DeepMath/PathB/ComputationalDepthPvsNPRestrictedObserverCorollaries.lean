import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanQueryMERACompiler

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

end PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.no_boundedMERA_routed_SAT_transcript_at_gap
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedObserverCorollaries.no_boundedMERA_compiler_for_SAT
