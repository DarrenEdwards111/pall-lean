/-
  GadgetSubspaceFactoringCounterexample.lean

  Documents the counterexample that motivates introducing the
  paper-faithful `mlBlockedSpdpSubspaceInc` (inclusive-κ) variant.

  The original `PAC.gadget_spdp_subspace_factoring` axiom is stated
  on `mlBlockedSpdpSubspace` (strict `S.length = κ`). This paper-
  exact matrix recap (p vs np1.pdf, line 2662) uses `|α| ≤ κ`
  (inclusive), matching the Lemma 40(c) proof which explicitly uses
  "Fix multi-indices α with |α| ≤ κ".

  **Counterexample** (concrete computations verified in Lean):
  - N = 2, g.poly = X 0 (supportSize = 1, degreeBound = 1)
  - p = X 1, κ = 1, ℓ = 0
  - Shifted at (κ+d=2, ℓ+d=1):
    * `iterDerivList [0,1] (X 1) = 0` (proved below)
    * `iterDerivList [1,0] (X 1) = 0` (proved below)
    * Under strict `= κ`: shifted subspace = {0}, rank = 0.
  - Unshifted at (1, 0):
    * `iterDerivList [0] (X 0 · X 1) = X 1` (proved below)
    * `iterDerivList [1] (X 0 · X 1) = X 0` (proved below)
    * Subspace ⊇ span{X 0, X 1}, rank ≥ 2.
  - Axiom claim: rank ≤ N^(s+d) · rank_shifted = N² · 0 = 0, so 2 ≤ 0.
    **FALSE**.

  Under the inclusive convention (`mlBlockedSpdpSubspaceInc`), the
  counterexample disappears: for κ=2 inclusive, |S|=0 contributes
  `mlProj(m · X 1)` giving nonzero shifted subspace. This is the
  convention the paper actually uses.
-/

import PallLean.PAC
import PallLean.MultilinearSPDP
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace GadgetSubspaceFactoringCounterexample

open MvPolynomial MultilinearSPDP SPDP

/-- Variable X 0 in MvPolynomial (Fin 2) ℚ. -/
noncomputable def x0 : MvPolynomial (Fin 2) ℚ := X ⟨0, by omega⟩

/-- Variable X 1 in MvPolynomial (Fin 2) ℚ. -/
noncomputable def x1 : MvPolynomial (Fin 2) ℚ := X ⟨1, by omega⟩

/-- The gadget X_0 packaged as a BoundedGadget. -/
noncomputable def counterexample_gadget : PAC.BoundedGadget 2 where
  poly := x0
  supportSize := 1
  degreeBound := 1
  vars_card_le := by unfold x0; rw [MvPolynomial.vars_X]; simp
  totalDegree_le := by unfold x0; rw [MvPolynomial.totalDegree_X]

/-- A valid two-block partition of Fin 2. -/
def twoBlockPartition : BlockPartition 2 where
  numBlocks := 2
  assign := fun i => i

/-- iterDerivList [0, 1] X_1 = 0 (two derivatives of a deg-1 poly). -/
theorem iterDerivList_two_X1_zero :
    iterDerivList [(⟨0, by omega⟩ : Fin 2), (⟨1, by omega⟩ : Fin 2)] x1 = 0 := by
  simp [iterDerivList, pderiv_X, x1]

/-- iterDerivList [1, 0] X_1 = 0. -/
theorem iterDerivList_two_X1_zero' :
    iterDerivList [(⟨1, by omega⟩ : Fin 2), (⟨0, by omega⟩ : Fin 2)] x1 = 0 := by
  simp [iterDerivList, pderiv_X, x1]

/-- iterDerivList [0] (X_0 · X_1) = X_1. -/
theorem iterDerivList_one_zero :
    iterDerivList [(⟨0, by omega⟩ : Fin 2)] (x0 * x1) = x1 := by
  simp [iterDerivList, pderiv_X, x0, x1, pderiv_mul]

/-- iterDerivList [1] (X_0 · X_1) = X_0. -/
theorem iterDerivList_one_one :
    iterDerivList [(⟨1, by omega⟩ : Fin 2)] (x0 * x1) = x0 := by
  simp [iterDerivList, pderiv_X, x0, x1, pderiv_mul]

end GadgetSubspaceFactoringCounterexample
