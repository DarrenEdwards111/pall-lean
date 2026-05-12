import PallLean.Paper93.Paper283.BridgeASquareHelperExactRow
import PallLean.Paper93.Paper283.BridgeASquareHelperKronecker

/-!
# Exact square-helper Bridge A local polynomial

This file closes the arbitrary-`kappa` square-helper candidate isolated in
`BridgeAGeneralizedNonzeroWitness`: the derivative-row Kronecker calculation
gives the lower bound, and the missing-helper/exact-row dichotomy gives the
matching upper containment.

The result is packaged through the existing compiler-SPDP normalized local
polynomial surface.  This identifies a concrete local polynomial realization
with the current `BridgeAPerVertexCompilerSPDPData` abstraction; it is not a
claim that the full Cook-Levin compiler has been refactored to expose this
polynomial as its literal emitted gadget.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open SPDP

namespace BridgeAGeneralizedNonzeroWitness

attribute [local instance] Classical.dec

/-- The concrete square-helper derivative rows satisfy the Kronecker
coefficient obligation. -/
theorem squareHelperDerivativeRowKronecker_closed (kappa gadgetN : Nat) :
    squareHelperDerivativeRowKronecker kappa gadgetN :=
  squareHelperDerivativeRowKronecker_squareHelperQ kappa gadgetN

/-- Every strict blocked SPDP generator of `squareHelperQ` lies in the
predicted square-helper row space. -/
theorem squareHelperExactUpperContainment_closed (kappa gadgetN : Nat) :
    squareHelperExactUpperContainment kappa gadgetN := by
  classical
  unfold squareHelperExactUpperContainment
  unfold mlBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hLen, hdeg, hvars, hAdm, hq⟩
  subst q
  by_cases hmissing :
      ∀ r : Fin (rowCount kappa gadgetN),
        ∃ j : Fin kappa, squareHelperIndex kappa gadgetN r j ∉ S
  · rw [squareHelperRowSpace_eq_squareHelperRowSpan]
    exact
      mlProj_shift_iterDerivList_squareHelperQ_mem_rowSpan_of_forall_missing_helper
        kappa gadgetN S m hmissing
  · push_neg at hmissing
    rcases hmissing with ⟨r, hrow⟩
    exact
      mlProj_shift_iterDerivList_squareHelperQ_mem_rowSpace_of_exactRow
        kappa gadgetN S m r hLen hAdm hrow hvars hdeg

/-- Exact arbitrary-`kappa` rank equality for the square-helper candidate. -/
theorem squareHelperExactRankTarget_closed (kappa gadgetN : Nat) :
    squareHelperExactRankTarget kappa gadgetN :=
  squareHelperExactRankTarget_of_derivativeRowKronecker_and_exactUpperContainment
    (squareHelperDerivativeRowKronecker_closed kappa gadgetN)
    (squareHelperExactUpperContainment_closed kappa gadgetN)

/-- Per-vertex normalized Bridge A local-polynomial package supplied by the
exact square-helper candidate. -/
noncomputable def squareHelper_normalizedLocalPolynomial
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N) :
    BridgeAPerVertexLocalPolynomialNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi v where
  spdpVars := squareHelperVarCount kappa gadgetN
  partition := discretePartition (squareHelperVarCount kappa gadgetN)
  Qv := squareHelperQ kappa gadgetN
  rank_eq_normalized := squareHelperExactRankTarget_closed kappa gadgetN

/-- Family-level normalized Bridge A local-polynomial package supplied by the
exact square-helper candidate. -/
noncomputable def squareHelper_normalizedLocalPolynomialFamily
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) :
    BridgeACompilerLocalPolynomialFamilyNormalized
      alpha beta alpha0 kappa gadgetN G chi Phi where
  spdpVars := fun _ => squareHelperVarCount kappa gadgetN
  partition := fun _ => discretePartition (squareHelperVarCount kappa gadgetN)
  Qv := fun _ => squareHelperQ kappa gadgetN
  rank_eq_normalized := by
    intro _v
    exact squareHelperExactRankTarget_closed kappa gadgetN

/-- Per-vertex compiler-SPDP data obtained from the exact square-helper
local-polynomial package. -/
noncomputable def squareHelper_perVertexCompilerSPDPData
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 kappa gadgetN G chi Phi v :=
  bridgeA_perVertexCompilerSPDPData_of_normalizedLocalPolynomial
    (squareHelper_normalizedLocalPolynomial
      alpha beta alpha0 kappa gadgetN G chi Phi v)
    halpha hgadgetN

/-- Family-level compiler-SPDP data obtained from the exact square-helper
local-polynomial package. -/
noncomputable def squareHelper_compilerSPDPFamilyData
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeACompilerSPDPFamilyData
      alpha beta alpha0 kappa gadgetN G chi Phi :=
  bridgeA_compilerSPDPFamilyData_of_normalizedLocalPolynomialFamily
    (squareHelper_normalizedLocalPolynomialFamily
      alpha beta alpha0 kappa gadgetN G chi Phi)
    halpha hgadgetN

/-- Pointwise Bridge A SPDP-rank lower bound for the square-helper compiler
adapter. -/
theorem squareHelper_perVertex_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) := by
  exact
    bridgeA_perVertex_spdpRank_lower_bound_of_normalizedLocalPolynomial
      (squareHelper_normalizedLocalPolynomial
        alpha beta alpha0 kappa gadgetN G chi Phi v)
      halpha hgadgetN hE

/-- Family-level Bridge A SPDP-rank lower bound for the square-helper compiler
adapter. -/
theorem squareHelper_family_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (v : Fin N)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    kappa <=
      mlBlockedSpdpRank
        (discretePartition (squareHelperVarCount kappa gadgetN))
        kappa kappa (squareHelperQ kappa gadgetN) := by
  exact
    bridgeA_family_spdpRank_lower_bound_of_normalizedLocalPolynomialFamily
      (squareHelper_normalizedLocalPolynomialFamily
        alpha beta alpha0 kappa gadgetN G chi Phi)
      halpha hgadgetN v hE

/-! ## Axiom audit anchors -/

#print axioms squareHelperDerivativeRowKronecker_closed
#print axioms squareHelperExactUpperContainment_closed
#print axioms squareHelperExactRankTarget_closed
#print axioms squareHelper_normalizedLocalPolynomial
#print axioms squareHelper_normalizedLocalPolynomialFamily
#print axioms squareHelper_perVertexCompilerSPDPData
#print axioms squareHelper_compilerSPDPFamilyData
#print axioms squareHelper_perVertex_spdpRank_lower_bound
#print axioms squareHelper_family_spdpRank_lower_bound

end BridgeAGeneralizedNonzeroWitness

end PallLean.Paper93.Paper283
