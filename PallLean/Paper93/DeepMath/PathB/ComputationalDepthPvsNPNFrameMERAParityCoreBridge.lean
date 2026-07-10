import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameRestrictedMERADecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPHardSurvivalProbe
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMathlibCandidates

/-!
# N-Frame MERA bridge to a concrete exponential SPDP target

The restricted MERA theorem gives a polynomial accessible-rank ceiling, but its original diagonal
witness depended on the decoder family itself.  This file replaces that witness by the concrete
inner-product/parity cut matrix from `ComputationalDepthSPDPHardSurvivalProbe`.

That matrix has projected SPDP rank exactly `2^n`, while every fixed-bond, fixed-cone,
logarithmic-depth MERA family has accessible rank at most `n^k` for one fixed `k`.  Exponential
growth therefore eventually beats the MERA ceiling, so no such family preserves the parity-core
SPDP rank at all input sizes.

This is a genuine concrete restricted-decoder lower bound.  The parity core is in `P`, not an
NP-complete hard family.  Consequently SAT correctness does not by itself imply preservation of
this representation-dependent rank.  The final section names that separate transport obligation
and proves the exact conditional SAT cash-out, without asserting the transport theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection
open PallLean.Paper93.DeepMath.PathB.SPDPHardSurvivalProbe
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder

abbrev MERAFamily := BoundedBondLocalMERADecoderFamily

/-- The projected SPDP rank of the concrete inner-product/parity cut matrix, at the fixed
nontrivial projection parameters `k = 0`, `d = 1`. -/
def parityCoreSPDPRequiredRank (n : Nat) : Nat :=
  pcrank (spdpProj n 0 1) (ipMatrix n)

/-- The concrete parity core has exponential projected SPDP rank. -/
theorem parityCoreSPDPRequiredRank_eq_two_pow (n : Nat) :
    parityCoreSPDPRequiredRank n = 2 ^ n := by
  unfold parityCoreSPDPRequiredRank
  exact spdp_ipMatrix_survives 0 1 (by omega)

/-- Exponential projected rank eventually exceeds the polynomial ceiling of every fixed restricted
MERA family. -/
theorem exists_parityCoreRank_exceeds_ceiling (M : MERAFamily) :
    ∃ n : Nat, 1 ≤ n ∧ n ^ M.polyExponent < parityCoreSPDPRequiredRank n := by
  obtain ⟨n, hn, hgap⟩ :=
    Nat.exists_poly_lt_pow (p := 2) (by omega) 1 M.polyExponent 0
  refine ⟨n, hn, ?_⟩
  simpa [parityCoreSPDPRequiredRank_eq_two_pow] using hgap

/-- **Concrete restricted MERA lower bound.**  No fixed-bond, fixed-cone,
logarithmic-depth local MERA family preserves the projected SPDP rank of the parity cut matrix at
all sizes. -/
theorem not_preserves_parityCoreSPDPRequiredRank (M : MERAFamily) :
    ¬ M.PreservesRequiredRank parityCoreSPDPRequiredRank := by
  obtain ⟨n, hn, hgap⟩ := exists_parityCoreRank_exceeds_ceiling M
  exact M.not_preservesRequiredRank_of_exceeds_ceiling
    parityCoreSPDPRequiredRank n hn hgap

/-- Pointwise form: for every restricted MERA family there is a concrete size where its accessible
rank is strictly smaller than the parity core's projected SPDP rank. -/
theorem exists_parityCoreRank_exceeds_accessibleRank (M : MERAFamily) :
    ∃ n : Nat, M.accessibleRank n < parityCoreSPDPRequiredRank n := by
  obtain ⟨n, hn, hgap⟩ := exists_parityCoreRank_exceeds_ceiling M
  refine ⟨n, lt_of_le_of_lt (M.accessibleRank_le_poly n hn) hgap⟩

/-! ## Exact SAT transport frontier -/

/-- The missing representation/decision bridge for one alleged SAT machine and one restricted MERA
family.  It says SAT correctness forces preservation of the concrete parity-core projected rank.

This is deliberately a named proposition, not an axiom or theorem: the parity core is easy, and
ordinary language correctness need not preserve an algorithm's internal representation rank. -/
def SATCorrectnessTransportsParityCoreRank
    (U : MachineModel) (D : DecisionMachine U) (M : MERAFamily) : Prop :=
  DecidesSAT U D → M.PreservesRequiredRank parityCoreSPDPRequiredRank

/-- If a restricted MERA realization of a machine had the missing correctness-to-rank transport,
the concrete exponential rank theorem would rule out that machine as a SAT decider. -/
theorem not_decidesSAT_of_parityCore_transport
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (htransport : SATCorrectnessTransportsParityCoreRank U D M) :
    ¬ DecidesSAT U D := by
  intro hD
  exact (not_preserves_parityCoreSPDPRequiredRank M) (htransport hD)

/-- A machine belongs to the explicitly restricted class when it is accompanied by a bounded-bond
local MERA family and the task-rank transport certificate. -/
def HasParityCoreFaithfulRestrictedMERA
    (U : MachineModel) (D : DecisionMachine U) : Prop :=
  ∃ M : MERAFamily, SATCorrectnessTransportsParityCoreRank U D M

/-- No machine in the parity-core-faithful restricted MERA class decides SAT. -/
theorem no_SAT_decider_with_parityCoreFaithfulRestrictedMERA
    {U : MachineModel} :
    ¬ ∃ D : DecisionMachine U,
      HasParityCoreFaithfulRestrictedMERA U D ∧ DecidesSAT U D := by
  rintro ⟨D, ⟨M, htransport⟩, hD⟩
  exact (not_decidesSAT_of_parityCore_transport M htransport) hD

/-!
## Honest endpoint

The NP-side growth calculation is now concrete for the parity/Tseitin linear core: its projected
SPDP rank is exactly exponential and it defeats every restricted MERA polynomial ceiling.  This does
not prove a SAT lower bound without `SATCorrectnessTransportsParityCoreRank`.  Establishing an
analogous transport theorem for a genuine NP-complete residual family remains the load-bearing step;
generic SAT correctness alone cannot be substituted for it.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.parityCoreSPDPRequiredRank_eq_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.exists_parityCoreRank_exceeds_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.not_preserves_parityCoreSPDPRequiredRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.exists_parityCoreRank_exceeds_accessibleRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.not_decidesSAT_of_parityCore_transport
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAParityCoreBridge.no_SAT_decider_with_parityCoreFaithfulRestrictedMERA
