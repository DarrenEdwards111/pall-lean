import PallLean.Paper93.DeepMath.PathC.PiPlusDirectRowSynthesis
import PallLean.WithinProfileBound

/-!
# Booleanity branch obstruction for the actual constraint-type case split

Adjacency and transition rows now derive directly from the signed-cross atom.
This file pins the remaining failure of the requested top-level case split to
the actual initial Booleanity segment of `cookLevinFactorList`: when
`cookLevinConstraintType` is `booleanity`, the factor is the real Cook--Levin
Booleanity factor `1 - (boolLC n v).poly`, not the mixed block atom certified by
52ae1750.

No new payload surface is introduced here; this is the exact polynomial identity
that blocks the Booleanity branch of a direct case-split synthesis.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open WithinProfileBound
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- In the initial `n` slots of the actual Cook--Levin factor list, the selected
factor is exactly the real Booleanity factor `1 - (boolLC n v).poly`. -/
theorem cookLevinFactorList_get_booleanity_segment_eq_boolLC_factor
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (j : Fin (cookLevinFactorList M n hn2 htb hns).length)
    (hj : j.val < n) :
    (cookLevinFactorList M n hn2 htb hns).get j =
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n ⟨j.val, hj⟩).poly) := by
  unfold cookLevinFactorList
  simp [cook_levin_compilation, boolConstraintList, boolLC, boolPoly', hj]

/-- Consequently, the Booleanity branch of the concrete `cookLevinConstraintType`
case split selects a real Booleanity factor, not a mixed block atom. -/
theorem cookLevinConstraintType_booleanity_branch_factor_ne_mixed_atom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (j : Fin (cookLevinFactorList M n hn2 htb hns).length)
    (hj : j.val < n)
    (i : D.blockIndex) :
    (cookLevinConstraintType M n hn2 htb hns j = ConstraintType.booleanity) ∧
    (cookLevinFactorList M n hn2 htb hns).get j ≠
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)) :
        SATDeciderGaugeSpace M n hn2 htb hns) := by
  constructor
  · exact cookLevinConstraintType_eq_booleanity M n hn2 htb hns j hj
  · intro hmix
    have hfactor := cookLevinFactorList_get_booleanity_segment_eq_boolLC_factor
      M n hn2 htb hns j hj
    have hboolMixed :
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n ⟨j.val, hj⟩).poly :
            SATDeciderGaugeSpace M n hn2 htb hns) =
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            SATDeciderGaugeSpace M n hn2 htb hns) := by
      exact hfactor.symm.trans hmix
    exact boolLC_factor_ne_mixed_monomial
      M n hn2 htb hns D ⟨j.val, hj⟩ i hboolMixed

/-- Exact missing identity for direct synthesis of the Booleanity branch from the
52ae1750 mixed-atom discharge. -/
theorem direct_caseSplit_booleanity_missing_identity_false
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (j : Fin (cookLevinFactorList M n hn2 htb hns).length)
    (hj : j.val < n)
    (i : D.blockIndex) :
    ¬ ((cookLevinFactorList M n hn2 htb hns).get j =
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)) :
        SATDeciderGaugeSpace M n hn2 htb hns)) := by
  exact (cookLevinConstraintType_booleanity_branch_factor_ne_mixed_atom
    M n hn2 htb hns D j hj i).2

/-! ## Axiom audit anchors -/

#print axioms cookLevinFactorList_get_booleanity_segment_eq_boolLC_factor
#print axioms cookLevinConstraintType_booleanity_branch_factor_ne_mixed_atom
#print axioms direct_caseSplit_booleanity_missing_identity_false

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
