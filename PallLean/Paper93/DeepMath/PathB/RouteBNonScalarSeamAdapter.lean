import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.PathB.RouteBTransportSeamClosure

/-!
# Route-B non-scalar seam adapter (no Step4Compiler rewrite)

Thin adapter layer: keep `Step4Compiler` untouched and package the remaining
non-scalar Route-B obligations behind one interface.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation

/-- Adapter package for the remaining non-scalar Route-B closure seam. -/
structure RouteBNonScalarSeamAdapterPackage : Prop where
  mapPreimage : RouteBRicherConcreteNPNonScalarMapPreimageSeam
  activeTemplateBlockers :
    ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      CookLevinActiveProfileTemplateCollapseBlockers M n hn2 htb hns
  prependedNP : RouteBRicherConcreteNPPrependedMultilinearNPSeam

/-- Adapter closeout: once the package is supplied, the non-scalar transport
chain discharges `PeqNP_Paper`. -/
theorem not_PeqNP_of_nonScalarSeamAdapterPackage
    (h : RouteBNonScalarSeamAdapterPackage) :
    ∀ (_ : PeqNP_Paper), False :=
  not_PeqNP_of_nonScalarMapPreimage_activeTemplateBlockers_np
    h.mapPreimage h.activeTemplateBlockers h.prependedNP

#print axioms not_PeqNP_of_nonScalarSeamAdapterPackage

end PallLean.Paper93.DeepMath.PathB
