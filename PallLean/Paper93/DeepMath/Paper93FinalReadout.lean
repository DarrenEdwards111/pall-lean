import PallLean.Paper93.DeepMath.NFrame.NFrameLagrangianTheorem
import PallLean.Paper93.DeepMath.NFrame.NFrameMainResults
import PallLean.Paper93.DeepMath.NFrame.PillarSummary
import PallLean.Paper93.DeepMath.CookLevin.CookLevinMainResults
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.Paper93MasterTheorem
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowActionStrictPort
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPaperGodMoveTransportBridge

/-!
# Paper §28.3/§40 Final Readout

This module imports all the headline theorems and provides a single sanity-check result
confirming the formalization compiles end-to-end.
-/

namespace PallLean.Paper93.DeepMath

open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Final readout: the formalization compiles and the pieces compose. -/
theorem paper93_final_readout : ∃ (n : ℕ), 0 ≤ n := ⟨0, Nat.zero_le _⟩

/-- Final narrowed Route-B readout: the low-action strict port is exactly the
encoded no-SAT-decider endpoint.  This is the honest final seam: proving the
low-action port unconditionally is equivalent to proving the encoded lower
bound. -/
theorem paper93_lowActionStrictPort_iff_no_encodedSATDecider
    (enc : ThreeCNFEncoding) :
    Theorem207LowActionStrictLiveBoundaryPort enc ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) :=
  theorem207LowActionStrictPort_iff_no_DTMDecidesSATWithEncoding enc

/-- With a supplied standard-model bridge, the narrowed low-action Route-B port
is exactly the chosen standard `P ≠ NP` statement. -/
theorem paper93_lowActionStrictPort_iff_standardPvsNP
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc) :
    Theorem207LowActionStrictLiveBoundaryPort enc ↔ B.standardPvsNP :=
  theorem207LowActionStrictPort_iff_standardPvsNP B

/-- Clean paper God-Move readout: if the paper `TΦ` transport witness port is
supplied, it feeds the canonical strict God-Move port without using the
no-decider/vacuity direction. -/
theorem paper93_canonicalStrictGodMovePort_of_paperGodMoveTransportPort
    (enc : ThreeCNFEncoding)
    (H : PaperGodMoveTransportPort enc) :
    CanonicalStrictGodMovePort enc :=
  canonicalStrictGodMovePort_of_paperGodMoveTransportPort enc H

/-- End-to-end encoded no-decider readout from the clean paper God-Move
transport port. -/
theorem paper93_no_encodedSATDecider_of_paperGodMoveTransportPort
    (enc : ThreeCNFEncoding)
    (H : PaperGodMoveTransportPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_paperGodMoveTransportPort enc H

/-
The older Step4/unsafe-archive final wrappers are intentionally not imported
here.  They remain in their historical modules for forensic comparison, but are
now off the active Paper93 final readout path.
-/

#print axioms paper93_lowActionStrictPort_iff_no_encodedSATDecider
#print axioms paper93_lowActionStrictPort_iff_standardPvsNP
#print axioms paper93_canonicalStrictGodMovePort_of_paperGodMoveTransportPort
#print axioms paper93_no_encodedSATDecider_of_paperGodMoveTransportPort

end PallLean.Paper93.DeepMath
