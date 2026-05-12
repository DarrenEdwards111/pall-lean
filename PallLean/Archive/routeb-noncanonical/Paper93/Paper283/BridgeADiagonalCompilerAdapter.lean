import PallLean.Paper93.Paper283.BridgeADiagonalQuadraticFamily

/-!
# Bridge A diagonal local-polynomial compiler adapter

This file wires the exact arbitrary-width `kappa = 1` diagonal-quadratic
local-polynomial witness into the existing Paper283 compiler-SPDP surfaces.

It does not identify this witness with the full arbitrary-`kappa`
Cook-Levin compiler-local polynomial.  It records the strongest exact
compiler-facing adapter currently available from the checked local
polynomial construction.
-/

namespace PallLean.Paper93.Paper283

namespace BridgeADiagonalCompilerAdapter

open MultilinearSPDP
open BridgeADiagonalQuadraticFamily

/-- Per-vertex compiler-SPDP data produced by the exact arbitrary-width
diagonal-quadratic local polynomial at `kappa = 1`. -/
noncomputable def diagonalQuadratic_perVertexCompilerSPDPData
    {N d : Nat} (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeAPerVertexCompilerSPDPData
      alpha beta alpha0 1 gadgetN G chi Phi v :=
  bridgeA_perVertexCompilerSPDPData_of_normalizedLocalPolynomial
    (diagonalQuadratic_normalizedLocalPolynomial
      alpha beta alpha0 gadgetN G chi Phi v)
    halpha hgadgetN

/-- Family-level compiler-SPDP data produced by the exact arbitrary-width
diagonal-quadratic local polynomial at `kappa = 1`. -/
noncomputable def diagonalQuadratic_compilerSPDPFamilyData
    {N d : Nat} (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 1 <= gadgetN) :
    BridgeACompilerSPDPFamilyData
      alpha beta alpha0 1 gadgetN G chi Phi :=
  bridgeA_compilerSPDPFamilyData_of_normalizedLocalPolynomialFamily
    (diagonalQuadratic_normalizedLocalPolynomialFamily
      alpha beta alpha0 gadgetN G chi Phi)
    halpha hgadgetN

/-- Pointwise Bridge A SPDP-rank lower bound for the diagonal-quadratic
compiler adapter. -/
theorem diagonalQuadratic_perVertex_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real) (v : Fin N)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    1 <=
      mlBlockedSpdpRank (oneBlockPartition gadgetN) 1 1
        (diagonalQuadratic gadgetN) := by
  exact
    bridgeA_perVertex_spdpRank_lower_bound_of_normalizedLocalPolynomial
      (diagonalQuadratic_normalizedLocalPolynomial
        alpha beta alpha0 gadgetN G chi Phi v)
      halpha hgadgetN hE

/-- Family-level Bridge A SPDP-rank lower bound for the diagonal-quadratic
compiler adapter. -/
theorem diagonalQuadratic_family_spdpRank_lower_bound
    {N d : Nat} (alpha beta alpha0 : Real) (gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (hgadgetN : 2 <= gadgetN)
    (v : Fin N)
    (hE : alpha0 <= localEnergy alpha beta G chi Phi v) :
    1 <=
      mlBlockedSpdpRank (oneBlockPartition gadgetN) 1 1
        (diagonalQuadratic gadgetN) := by
  exact
    bridgeA_family_spdpRank_lower_bound_of_normalizedLocalPolynomialFamily
      (diagonalQuadratic_normalizedLocalPolynomialFamily
        alpha beta alpha0 gadgetN G chi Phi)
      halpha hgadgetN v hE

/-! ## Axiom audit anchors -/

#print axioms diagonalQuadratic_perVertexCompilerSPDPData
#print axioms diagonalQuadratic_compilerSPDPFamilyData
#print axioms diagonalQuadratic_perVertex_spdpRank_lower_bound
#print axioms diagonalQuadratic_family_spdpRank_lower_bound

end BridgeADiagonalCompilerAdapter

end PallLean.Paper93.Paper283
