import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCompiledRowCertificateBridge

/-!
# Coordinate-level Boolean-projected Pi+ atom

The block-local row atom lives over variables `ι × Bool`.  The actual
Cook--Levin transform uses flat `Fin n` variables equipped with a block-coordinate
equivalence.  This file proves the first coordinate bridge: after conjugating by
that equivalence, the raw `Pi+` transform acts on a paired flat coordinate by the
same two-variable Hadamard formulas.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

variable (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (i : D.blockIndex)

/-- Flat variable corresponding to the `false` side of a Cook--Levin `Pi+` block. -/
noncomputable abbrev satBlockFalse :
    Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
  D.coord.symm (i, false)

/-- Flat variable corresponding to the `true` side of a Cook--Levin `Pi+` block. -/
noncomputable abbrev satBlockTrue :
    Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
  D.coord.symm (i, true)

/-- Under the coordinate-lifted raw `Pi+`, a flat `false` coordinate maps to the
sum of the two flat coordinates in its block. -/
theorem piPlusSATBlockAlgEquiv_X_false :
    piPlusSATBlockAlgEquiv M n hn2 htb hns D
      (X (satBlockFalse M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) =
      (X (satBlockFalse M n hn2 htb hns D i) +
        X (satBlockTrue M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) := by
  simp [piPlusSATBlockAlgEquiv, blockPiPlusAlgEquiv, satBlockFalse, satBlockTrue,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

/-- Under the coordinate-lifted raw `Pi+`, a flat `true` coordinate maps to the
difference of the two flat coordinates in its block. -/
theorem piPlusSATBlockAlgEquiv_X_true :
    piPlusSATBlockAlgEquiv M n hn2 htb hns D
      (X (satBlockTrue M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) =
      (X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) := by
  simp [piPlusSATBlockAlgEquiv, blockPiPlusAlgEquiv, satBlockFalse, satBlockTrue,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

/-- Boolean normalization repairs the coordinate-level quadratic leakage of a
mixed flat block monomial exactly as in the abstract block-local theorem. -/
theorem zeroProfileBooleanNormalize_piPlusSATBlockAlgEquiv_mixed :
    zeroProfileBooleanNormalize
      (piPlusSATBlockAlgEquiv M n hn2 htb hns D
        ((X (satBlockFalse M n hn2 htb hns D i)) *
          (X (satBlockTrue M n hn2 htb hns D i)) :
          PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns)) =
      (X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) := by
  rw [map_mul]
  rw [piPlusSATBlockAlgEquiv_X_false, piPlusSATBlockAlgEquiv_X_true]
  have hmul :
      ((X (satBlockFalse M n hn2 htb hns D i) +
          X (satBlockTrue M n hn2 htb hns D i)) *
        (X (satBlockFalse M n hn2 htb hns D i) -
          X (satBlockTrue M n hn2 htb hns D i)) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) =
        X (satBlockFalse M n hn2 htb hns D i) *
          X (satBlockFalse M n hn2 htb hns D i) -
        X (satBlockTrue M n hn2 htb hns D i) *
          X (satBlockTrue M n hn2 htb hns D i) := by
    ring
  rw [hmul, zeroProfileBooleanNormalize_sub]
  rw [zeroProfileBooleanNormalize_X_mul_X, zeroProfileBooleanNormalize_X_mul_X]

/-- Pulling the repaired coordinate-level row back through raw inverse `Pi+`
returns the `true` coordinate of that block. -/
theorem piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns))) =
      (X (satBlockTrue M n hn2 htb hns D i) :
        PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) := by
  rw [zeroProfileBooleanNormalize_piPlusSATBlockAlgEquiv_mixed M n hn2 htb hns D i]
  apply (piPlusSATBlockAlgEquiv M n hn2 htb hns D).injective
  simp [piPlusSATBlockAlgEquiv_X_true]

/-- Coordinate-level row form of the atom: the repaired mixed-block pullback is
exactly the one-extra-derivative source SPDP row. -/
theorem piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_oneDerivativeRow :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns))) =
      mlProj
        ((1 : PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) *
          SPDP.iterDerivList [satBlockFalse M n hn2 htb hns D i]
            (((X (satBlockFalse M n hn2 htb hns D i)) *
              (X (satBlockTrue M n hn2 htb hns D i))) :
              PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns)) := by
  rw [piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed M n hn2 htb hns D i]
  simp [SPDP.iterDerivList, mlProj_X_block]

/-- Membership form of the coordinate atom: provided the singleton derivative
list is block-admissible, the repaired mixed-block pullback is a generator of the
inclusive one-derivative/zero-shift SPDP subspace of the source mixed monomial. -/
theorem piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_mem_inc
    (B : SPDP.BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (hadm : SPDP.isBlockAdmissible B [satBlockFalse M n hn2 htb hns D i]) :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          ((X (satBlockFalse M n hn2 htb hns D i)) *
            (X (satBlockTrue M n hn2 htb hns D i)) :
            PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns))) ∈
      mlBlockedSpdpSubspaceInc B 1 0
        (((X (satBlockFalse M n hn2 htb hns D i)) *
          (X (satBlockTrue M n hn2 htb hns D i))) :
          PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns) := by
  rw [piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_oneDerivativeRow M n hn2 htb hns D i]
  exact Submodule.subset_span
    ⟨[satBlockFalse M n hn2 htb hns D i],
      (1 : PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeSpace M n hn2 htb hns),
      by simp,
      by simp,
      by simp,
      hadm,
      rfl⟩

/-! ## Axiom audit anchors -/

#print axioms piPlusSATBlockAlgEquiv_X_false
#print axioms piPlusSATBlockAlgEquiv_X_true
#print axioms zeroProfileBooleanNormalize_piPlusSATBlockAlgEquiv_mixed
#print axioms piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed
#print axioms piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_oneDerivativeRow
#print axioms piPlusSATBlockAlgEquiv_symm_booleanProjected_mixed_mem_inc

end PallLean.Paper93.DeepMath.PathC
