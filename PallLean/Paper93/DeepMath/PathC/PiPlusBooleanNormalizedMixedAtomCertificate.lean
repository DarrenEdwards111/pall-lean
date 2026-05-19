import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageUnconditionalObstruction
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCoordinateAtom

/-!
# Boolean-normalized mixed-atom certificate for Pi+

The raw fixedness socket cannot be discharged for Cook--Levin Booleanity atoms:
`Pi+` sends the mixed monomial to a difference of squares.  The Boolean route
repairs exactly that leakage by normalizing squares first and then pulling back
with the inverse half-Hadamard.

This file packages that repaired local calculation as an unconditional
certificate.  It is the replacement target for the impossible raw fixed-piece
certificate: a mixed block atom is not raw-fixed, but its Boolean-projected
`Pi+` image pulls back to a one-derivative source row.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Local block-coordinate Boolean-projected row certificate: after applying
raw `Pi+`, Boolean-normalizing, and pulling back by the inverse, `p` becomes an
ordinary source SPDP row of `p` with the displayed derivative list and
multiplier. -/
def BlockPiPlusBooleanProjectedPullbackRowCertificate
    {ι : Type*} (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
    blockPiPlusInvAlgHom ι
        (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
      mlProj (m * blockIterDerivList S p)

/-- The mixed Booleanity atom has an unconditional Boolean-projected row
certificate, with derivative list `[(i,false)]` and multiplier `1`. -/
theorem blockPiPlusBooleanProjectedPullbackRowCertificate_mixed
    {ι : Type*} [DecidableEq ι] (i : ι) :
    BlockPiPlusBooleanProjectedPullbackRowCertificate
      (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) := by
  refine ⟨[(i, false)], 1, ?_⟩
  exact blockPiPlus_booleanProjected_mixed_pullback_iterDerivRow (i := i)

/-- Budgeted form of the same local certificate.  This is the exact `(1,0)`
shape used by the paper-scale Boolean-projected route: one extra derivative and
zero extra multiplier degree. -/
def BlockPiPlusBooleanProjectedOneZeroRowCertificate
    {ι : Type*} (p : MvPolynomial (ι × Bool) ℚ) : Prop :=
  ∃ (S : List (ι × Bool)) (m : MvPolynomial (ι × Bool) ℚ),
    S.length ≤ 1 ∧ m.totalDegree ≤ 0 ∧
      blockPiPlusInvAlgHom ι
          (blockBooleanNormalize (blockPiPlusAlgHom ι p)) =
        mlProj (m * blockIterDerivList S p)

/-- The mixed atom satisfies the budgeted `(1,0)` Boolean-projected certificate
unconditionally. -/
theorem blockPiPlusBooleanProjectedOneZeroRowCertificate_mixed
    {ι : Type*} [DecidableEq ι] (i : ι) :
    BlockPiPlusBooleanProjectedOneZeroRowCertificate
      (((X (i, false)) * (X (i, true))) : MvPolynomial (ι × Bool) ℚ) := by
  refine ⟨[(i, false)], 1, by simp, by simp, ?_⟩
  exact blockPiPlus_booleanProjected_mixed_pullback_iterDerivRow (i := i)

/-- Flat SAT-coordinate version of the repaired mixed-atom certificate. -/
def PiPlusBooleanProjectedMixedAtomRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) : Prop :=
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            SATDeciderGaugeSpace M n hn2 htb hns))) =
    mlProj
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
        SPDP.iterDerivList [satBlockFalse M n hn2 htb hns D i]
          (((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i))) :
            SATDeciderGaugeSpace M n hn2 htb hns))

/-- The flat SAT-coordinate repaired mixed-atom certificate is unconditional. -/
theorem piPlusBooleanProjectedMixedAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex) :
    PiPlusBooleanProjectedMixedAtomRowCertificate M n hn2 htb hns D i := by
  exact piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_oneDerivativeRow
    M n hn2 htb hns D i

/-- Membership form: the unconditional mixed-atom certificate is already a
source row in the inclusive `(1,0)` SPDP window whenever the singleton derivative
is block-admissible. -/
theorem piPlusBooleanProjectedMixedAtom_mem_inc_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex)
    (B : SPDP.BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (hadm : SPDP.isBlockAdmissible B [satBlockFalse M n hn2 htb hns D i]) :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            SATDeciderGaugeSpace M n hn2 htb hns))) ∈
      mlBlockedSpdpSubspaceInc B 1 0
        (((X (satBlockFalse M n hn2 htb hns D i)) *
          (X (satBlockTrue M n hn2 htb hns D i))) :
          SATDeciderGaugeSpace M n hn2 htb hns) :=
  piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_mem_inc
    M n hn2 htb hns D i B hadm

/-- Paper-scale public-coordinate version of the unconditional repaired
mixed-atom row certificate. -/
theorem cookLevinPiPlusBooleanProjectedMixedAtomRowCertificate_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex) :
    PiPlusBooleanProjectedMixedAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i :=
  piPlusBooleanProjectedMixedAtomRowCertificate_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i

/-- Paper-scale public membership form of the repaired mixed atom. -/
theorem cookLevinPiPlusBooleanProjectedMixedAtom_mem_inc_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (i : (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).blockIndex)
    (B : SPDP.BlockPartition (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hadm : SPDP.isBlockAdmissible B
      [satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i]) :
    (cookLevinPiPlusSATTransform_paperScale M htb hns).equiv.symm
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns
        ((X (satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) *
          (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) ∈
      mlBlockedSpdpSubspaceInc B 1 0
        (((X (satBlockFalse M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) *
          (X (satBlockTrue M (2 ^ 804) paperScale_ge_two htb hns
              (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) i)) :
          SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) := by
  exact cookLevinPiPlusSATTransform_paperScale_symm_booleanProjected_mixed_mem_inc
    M htb hns i B hadm

/-! ## Axiom audit anchors -/

#print axioms blockPiPlusBooleanProjectedPullbackRowCertificate_mixed
#print axioms blockPiPlusBooleanProjectedOneZeroRowCertificate_mixed
#print axioms piPlusBooleanProjectedMixedAtomRowCertificate_unconditional
#print axioms piPlusBooleanProjectedMixedAtom_mem_inc_unconditional
#print axioms cookLevinPiPlusBooleanProjectedMixedAtomRowCertificate_paperScale
#print axioms cookLevinPiPlusBooleanProjectedMixedAtom_mem_inc_paperScale

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
