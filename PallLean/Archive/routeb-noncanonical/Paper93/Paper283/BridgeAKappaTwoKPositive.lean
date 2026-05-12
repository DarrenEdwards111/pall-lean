import PallLean.Paper93.Paper283.BridgeAKappaTwoIdentityOne

/-!
# Positivity of the kappa=2 cross-block K value

This file discharges the positivity input for
`K = crossBlockKValue (transCoeffSum M)`.  The only machine-specific
ingredient is `TuringMachine.DTM.hStates`, which gives a nonempty state set;
each transition coefficient is a successor natural cast to `Rat`.
-/

namespace PallLean.Paper93.Paper283

open PaperFaithfulSeparation
open BridgeAKappaTwoIdentityOne

/-- Every transition coefficient is strictly positive. -/
theorem transCoeff_pos (M : TuringMachine.DTM) (q : Fin M.numStates) :
    0 < transCoeff M q := by
  unfold transCoeff
  exact_mod_cast Nat.succ_pos (M.transition q false).1.val

/-- The transition-coefficient sum is strictly positive. -/
theorem transCoeffSum_pos (M : TuringMachine.DTM) :
    0 < transCoeffSum M := by
  unfold transCoeffSum
  refine Finset.sum_pos (fun q _ => transCoeff_pos M q) ?_
  exact ⟨⟨0, by have := M.hStates; omega⟩, Finset.mem_univ _⟩

/-- Positivity input for the kappa=2 four-identity package. -/
theorem crossBlockKValue_transCoeffSum_pos (M : TuringMachine.DTM) :
    0 < crossBlockKValue (transCoeffSum M) := by
  exact crossBlockKValue_pos_of_pos (transCoeffSum_pos M)

/-! ## Axiom audit anchors -/

#print axioms transCoeff_pos
#print axioms transCoeffSum_pos
#print axioms crossBlockKValue_transCoeffSum_pos

end PallLean.Paper93.Paper283
