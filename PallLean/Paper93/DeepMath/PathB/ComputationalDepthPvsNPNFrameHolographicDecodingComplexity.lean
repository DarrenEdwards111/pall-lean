import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameHolographicAreaLaw
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDecisionHolonomy

/-!
# N-Frame holographic decoding complexity

The area-law pressure test showed that the complete bulk label can fit through an `R^2` boundary after
`R` sequential uses.  The remaining Harlow--Hayden-style possibility is computational rather than
entropic: the information is present on the boundary, but extracting the task-relevant answer may take
super-polynomial time.

This file formalizes and audits that route:

1. area law plus exact recovery alone permits a one-step decoder annotation, so geometry does not imply
   decoding hardness;
2. a solver-specific super-polynomial decoding lower bound contradicts polynomial-time SAT correctness;
3. the corresponding all-machine theorem is logically equivalent to `SAT ∉ P` in the abstract machine
   model.  Thus the missing decoding-hardness field is the genuine breakthrough, not plumbing supplied by
   holography.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.DecisionHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw

/-! ## Geometry alone does not lower-bound decoding time -/

/-- A holographic exact-recovery channel together with an abstract cost assigned to its stabilizer. -/
structure HolographicDecodingProcess (R : Nat) where
  areaChannel : HolographicAreaLawChannel R
  decodingTime : Nat

/-- Tight no-go model: the saturated holographic streaming channel is compatible with decoding time one.
No theorem connecting geometry to decoder cost has yet been assumed. -/
def oneStepSaturatedDecoder (R : Nat) : HolographicDecodingProcess R where
  areaChannel := HolographicAreaLawChannel.saturatedStreamingChannel R
  decodingTime := 1

theorem oneStepSaturatedDecoder_time (R : Nat) :
    (oneStepSaturatedDecoder R).decodingTime = 1 := rfl

theorem oneStepSaturatedDecoder_recovers_bulk (R : Nat) :
    (oneStepSaturatedDecoder R).areaChannel.channel.capacityBits = R ^ 3 := rfl

/-! ## Solver-specific holographic decoding hardness -/

/-- A convenient explicit super-polynomial threshold used only for vacuous logical calibration. -/
def explicitSuperPolyThreshold (n : Nat) : Nat := n ^ n + n + 1

theorem explicitSuperPolyThreshold_superPoly : SuperPoly explicitSuperPolyThreshold := by
  intro k
  refine ⟨k + 1, ?_⟩
  have hp : (k + 1) ^ k ≤ (k + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [explicitSuperPolyThreshold]
  omega

/-- The Harlow--Hayden-style target for one alleged polynomial-time SAT machine.

`decodeTime` measures extraction of the task-relevant SAT information from the holographic boundary.
SAT correctness is required to imply both that this decoding is polynomial (because it is implemented by
the alleged solver) and that it obeys a super-polynomial lower bound.  Proving `decode_lower_of_decides`
from concrete solver/boundary geometry is the load-bearing new mathematics. -/
structure HolographicSATDecodingLowerBoundFor
    (U : MachineModel) (D : DecisionMachine U) where
  decodeTime : Nat → Nat
  threshold : Nat → Nat
  decode_poly_of_decides : DecidesSAT U D → PolyBounded decodeTime
  decode_lower_of_decides : DecidesSAT U D → DecisionHolonomyHyp decodeTime threshold
  threshold_superPoly : SuperPoly threshold

namespace HolographicSATDecodingLowerBoundFor

/-- A genuine super-polynomial holographic decoding lower bound rules out the alleged SAT decider. -/
theorem not_decidesSAT {U : MachineModel} {D : DecisionMachine U}
    (H : HolographicSATDecodingLowerBoundFor U D) : ¬ DecidesSAT U D := by
  intro hD
  have hnot : ¬ PolyBounded H.decodeTime :=
    decisionHolonomy_implies_not_poly (H.decode_lower_of_decides hD) H.threshold_superPoly
  exact hnot (H.decode_poly_of_decides hD)

/-- Vacuous inhabitant when a particular machine is already known not to decide SAT.  This is only for
calibrating logical strength; it supplies no decoding construction. -/
noncomputable def of_not_decidesSAT {U : MachineModel} (D : DecisionMachine U)
    (hD : ¬ DecidesSAT U D) : HolographicSATDecodingLowerBoundFor U D where
  decodeTime := fun _ => 0
  threshold := explicitSuperPolyThreshold
  decode_poly_of_decides := fun h => False.elim (hD h)
  decode_lower_of_decides := fun h => False.elim (hD h)
  threshold_superPoly := explicitSuperPolyThreshold_superPoly

end HolographicSATDecodingLowerBoundFor

/-- Holographic decoding-hardness target for every machine in the model. -/
abbrev HolographicSATDecodingLowerBoundForAllMachines (U : MachineModel) : Type :=
  ∀ D : DecisionMachine U, HolographicSATDecodingLowerBoundFor U D

/-- Global solver-specific holographic decoding hardness rules out polynomial-time SAT. -/
theorem no_SATDecisionInP_of_holographicDecoding {U : MachineModel}
    (hDecode : HolographicSATDecodingLowerBoundForAllMachines U) : ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hDecode D).not_decidesSAT hD

/-- If SAT is already known not to be in P, the conditional decoding target is inhabited vacuously. -/
noncomputable def holographicDecoding_of_no_SATDecisionInP {U : MachineModel}
    (hNo : ¬ SATDecisionInP U) : HolographicSATDecodingLowerBoundForAllMachines U := by
  intro D
  refine HolographicSATDecodingLowerBoundFor.of_not_decidesSAT D ?_
  intro hD
  exact hNo ⟨D, hD⟩

/-- **Exact calibration of the Harlow--Hayden route.**  Establishing a solver-specific
super-polynomial holographic decoding lower bound for every alleged SAT machine is equivalent to proving
that SAT has no polynomial-time decision machine. -/
theorem holographicDecoding_iff_no_SATDecisionInP {U : MachineModel} :
    Nonempty (HolographicSATDecodingLowerBoundForAllMachines U) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨hDecode⟩
    exact no_SATDecisionInP_of_holographicDecoding hDecode
  · intro hNo
    exact ⟨holographicDecoding_of_no_SATDecisionInP hNo⟩

/-!
## Verdict

The decoding-complexity route is the correct kind of strengthening: unlike capacity or total access, a
super-polynomial decoder lower bound would directly separate SAT from P.  But the area law does not imply
that bound—the one-step saturated decoder is a formal countermodel to that inference.  The remaining theorem
must connect a concrete NP-complete residual family and the internal dynamics of every alleged SAT solver to
`decode_lower_of_decides`.  The equivalence theorem above proves that doing so globally is exactly P versus NP.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity.oneStepSaturatedDecoder_recovers_bulk
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity.explicitSuperPolyThreshold_superPoly
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity.HolographicSATDecodingLowerBoundFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity.no_SATDecisionInP_of_holographicDecoding
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicDecodingComplexity.holographicDecoding_iff_no_SATDecisionInP
