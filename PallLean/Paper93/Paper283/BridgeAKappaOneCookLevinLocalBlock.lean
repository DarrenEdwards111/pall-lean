import PallLean.Paper93.Paper283.BridgeABlockEvalAtZero
import PallLean.Paper93.Paper283.RouteBBridgeARealCompilerQvFrontier

/-!
# Bridge A at kappa = 1 for the real Cook-Levin local block product

This file composes the five kernel-checked supporting computations:

* the real local polynomial is `cookLevinLocalBlockQ`, the product of actual
  Cook-Levin factors touching the locality block;
* the booleanity factor for `v` is in the block containing `v`;
* the constant term of `pderiv v` of that product is nonzero;
* multilinear projection preserves that constant coefficient;
* one nonzero first-order row gives first-order blocked SPDP rank at least
  one.

The result is the first paper-faithful Bridge A instance for the actual
compiler-local polynomial, at the smallest nondegenerate scale `kappa = 1`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-- The nonzero constant coefficient from `BridgeABlockEvalAtZero` survives
multilinear projection, so the first derivative row of the real local
Cook-Levin block product is nonzero. -/
theorem mlProj_iterDerivList_cookLevinLocalBlockQ_ne_zero
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    mlProj
        (iterDerivList [v]
          (cookLevinLocalBlockQ M n hn htb hns
            ((cook_levin_compilation M n hn htb hns).partition.assign v))) ≠
      0 := by
  intro hzero
  let Q :=
    cookLevinLocalBlockQ M n hn htb hns
      ((cook_levin_compilation M n hn htb hns).partition.assign v)
  have hcoeff_zero :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (mlProj (iterDerivList [v] Q)) = 0 := by
    rw [hzero]
    simp
  have hcoeff_project :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (mlProj (iterDerivList [v] Q)) =
        MvPolynomial.coeff (0 : Fin n →₀ ℕ) (MvPolynomial.pderiv v Q) := by
    rw [MultilinearSPDP.coeff_mlProj_of_isMultilinear_mono
      (iterDerivList [v] Q) (0 : Fin n →₀ ℕ) (by intro i; simp)]
    rw [IterDerivHelpers.iterDerivList_single]
  have hcoeff_pderiv :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ) (MvPolynomial.pderiv v Q) = 0 := by
    rwa [hcoeff_project] at hcoeff_zero
  exact coeff_zero_pderiv_cookLevinLocalBlockQ_ne_zero
    M n hn htb hns v hcoeff_pderiv

/-- First-order Bridge A rank lower bound for the real Cook-Levin local block
product at the compiler block containing `v`. -/
theorem cookLevinLocalBlockQ_rank_one_le
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    1 ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        1 1
        (cookLevinLocalBlockQ M n hn htb hns
          ((cook_levin_compilation M n hn htb hns).partition.assign v)) := by
  exact mlBlockedSpdpRank_one_le_of_nonzero_derivative
    (cook_levin_compilation M n hn htb hns).partition
    (cookLevinLocalBlockQ M n hn htb hns
      ((cook_levin_compilation M n hn htb hns).partition.assign v))
    v
    (mlProj_iterDerivList_cookLevinLocalBlockQ_ne_zero M n hn htb hns v)

/-- Energy-to-rank form of the `kappa = 1` Bridge A target, using compiler
variables themselves as the Route B vertices.  The energy hypothesis is no
longer a placeholder here: the rank conclusion is proved directly for the real
local Cook-Levin product, so the implication is uniformly true at `kappa = 1`.
-/
theorem cookLevinLocalBlockQEnergyToRankTarget_one_assign
    {d : ℕ}
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n → Real) :
    CookLevinLocalBlockQEnergyToRankTarget
      M n hn htb hns alpha beta alpha0 1 G chi Phi
      (fun v => (cook_levin_compilation M n hn htb hns).partition.assign v) := by
  intro v _henergy
  exact cookLevinLocalBlockQ_rank_one_le M n hn htb hns v

/-- Packaged `kappa = 1` Bridge A data for the real Cook-Levin local block
product. -/
noncomputable def cookLevinLocalBlockQBridgeAData_one_assign
    {d : ℕ}
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (alpha beta alpha0 : Real)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed n d)
    (chi : TseitinCharge n) (Phi : Fin n → Real) :
    CookLevinLocalBlockQBridgeAData
      M n hn htb hns alpha beta alpha0 1 G chi Phi where
  blockOfVertex :=
    fun v => (cook_levin_compilation M n hn htb hns).partition.assign v
  energy_to_spdpRank :=
    cookLevinLocalBlockQEnergyToRankTarget_one_assign
      M n hn htb hns alpha beta alpha0 G chi Phi

/-! ## Axiom audit anchors -/

#print axioms mlProj_iterDerivList_cookLevinLocalBlockQ_ne_zero
#print axioms cookLevinLocalBlockQ_rank_one_le
#print axioms cookLevinLocalBlockQEnergyToRankTarget_one_assign
#print axioms cookLevinLocalBlockQBridgeAData_one_assign

end PallLean.Paper93.Paper283
