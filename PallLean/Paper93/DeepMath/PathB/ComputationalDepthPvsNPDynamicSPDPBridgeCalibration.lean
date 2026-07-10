import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicSPDPGlobalGodMove

/-!
# Calibration of the dynamic-SPDP global-God-Move bridge

This file pressure-tests `SATCorrectnessFormsGlobalGodMove`.  The result is decisive:
for a fixed bounded-local-access profile and one decision machine, the bridge is
equivalent to that machine not deciding SAT.

The forward direction uses the already proved exponential-vs-polynomial gap and the
dynamic-SPDP boundary contradiction.  The reverse direction is vacuous: if the machine
does not decide SAT, any implication from `DecidesSAT` holds.

Thus the bridge is an exact restatement of the desired per-machine lower bound, not a
strictly easier intermediate lemma.  This is a calibration theorem, not a P≠NP claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge
open PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove

/-- The proposed all-size dynamic-SPDP global-God-Move bridge already excludes the
machine from SAT. -/
theorem not_decidesSAT_of_formsGlobalGodMove
    {U : MachineModel} {D : DecisionMachine U}
    (P : BoundedLocalAccessProfile)
    (hform : SATCorrectnessFormsGlobalGodMove U D P) :
    ¬ DecidesSAT U D := by
  intro hD
  obtain ⟨n, hn, hgap⟩ :=
    exists_holonomyRank_exceeds_MERA_ceiling P.toMERA
  obtain ⟨Input, State, R, G, x, hminor⟩ := hform hD n
  have hgap' : n ^ P.toMERA.polyExponent < 2 ^ n := by
    simpa [holonomyPatternRank_eq_two_pow] using hgap
  exact
    (G.no_exponential_globalGodMove_above_ceiling hn hgap')
      ⟨x, hminor⟩

/-- Conversely, if the machine does not decide SAT, the bridge holds vacuously. -/
theorem formsGlobalGodMove_of_not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U}
    (P : BoundedLocalAccessProfile)
    (hno : ¬ DecidesSAT U D) :
    SATCorrectnessFormsGlobalGodMove U D P := by
  intro hD
  exact False.elim (hno hD)

/-- **Exact calibration.**  For every fixed profile and decision machine, the proposed
bridge is logically equivalent to the desired SAT lower bound for that machine. -/
theorem formsGlobalGodMove_iff_not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U}
    (P : BoundedLocalAccessProfile) :
    SATCorrectnessFormsGlobalGodMove U D P ↔ ¬ DecidesSAT U D := by
  constructor
  · exact not_decidesSAT_of_formsGlobalGodMove P
  · exact formsGlobalGodMove_of_not_decidesSAT P

/-! ## Polynomial-round pressure test -/

/-- With one binary local choice per round and `n` sequential rounds, the number of
possible local histories is already `2^n`.  This is the basic obstruction to extending
the logarithmic-depth profile-count argument to arbitrary polynomial-time runs. -/
def polynomialRoundHistoryRank (n : Nat) : Nat := 2 ^ n

theorem polynomialRoundHistoryRank_eq_localHistories (n : Nat) :
    polynomialRoundHistoryRank n = 2 ^ (1 * n) := by
  simp [polynomialRoundHistoryRank]

/-- At every ordinary exponential-vs-polynomial gap, the polynomial-round local-history
rank violates the proposed polynomial ceiling. -/
theorem polynomialRoundHistoryRank_not_le_poly_at_gap
    {n k : Nat} (hgap : n ^ k < 2 ^ n) :
    ¬ polynomialRoundHistoryRank n ≤ n ^ k := by
  simp only [polynomialRoundHistoryRank]
  omega

/-!
## Honest consequence

`SATCorrectnessFormsGlobalGodMove` cannot be advertised as a smaller bridge to be filled
by Lean plumbing: for a fixed machine it is exactly the theorem that the machine is not
a SAT decider.  A productive replacement must expose weaker, independently provable
local event-generation conditions rather than quantifying over the already contradictory
all-size global minor.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration.not_decidesSAT_of_formsGlobalGodMove
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration.formsGlobalGodMove_of_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration.formsGlobalGodMove_iff_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPBridgeCalibration.polynomialRoundHistoryRank_not_le_poly_at_gap
