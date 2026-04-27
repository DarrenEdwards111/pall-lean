import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteW
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWH3
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWH4
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWI5
import PallLean.Paper93.DeepMath.PathB.ZeroProfileScalarClosure

/-!
# Augmented keepFOB P-side closure progress

This file aggregates the current checked progress on the keepFOB P-side
template-collapse frontier.

The round closes several previously ambiguous sub-obligations:

* H3 can be discharged against row-insensitive/global augmented `W` families,
  avoiding a fake canonical-row transport theorem.
* H4 can be discharged after adding endpoint variables to the canonical
  adjacency space.
* I5 should be stated as a charged-profile closure, not as raw same-profile
  closure, because the old same-profile form overforces the zero profile.

It also records the important negative result: the scalar-singleton
zero-profile route is false for the actual Cook-Levin zero-profile base
product.  The final P-side closure therefore needs a non-scalar zero-profile
package or a different quotient/gauge adapter.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open TuringMachine

/-- The scalar-singleton zero-profile escape route is not available for the
actual Cook-Levin base product. -/
theorem keepFOB_zeroProfile_scalar_route_obstructed
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ CookLevinZeroProfileTemplateScalarObligation M n hn htb hns :=
  not_CookLevinZeroProfileTemplateScalarObligation M n hn htb hns

/-! ## Axiom audit anchors -/

#print axioms keepFOB_zeroProfile_scalar_route_obstructed

end PathB
end DeepMath
end Paper93
end PallLean
