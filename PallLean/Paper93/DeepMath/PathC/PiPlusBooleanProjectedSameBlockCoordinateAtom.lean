import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSameBlockSignedAtom
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedCoordinateAtoms

/-!
# SAT-coordinate same-block signed atoms

This file transports the same-block signed atom seam from block coordinates to
the flat SAT coordinate surface for an explicit `Pi+` block pair
`(satBlockFalse D i, satBlockTrue D i)`.
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

/-- Flat signed atom whose endpoints are the two sides of one SAT `Pi+` block. -/
noncomputable def satSignedSameBlockAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ) (i : D.blockIndex) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  satSignedCrossAtom M n hn2 htb hns c
    (satBlockFalse M n hn2 htb hns D i)
    (satBlockTrue M n hn2 htb hns D i)

/-- The flat same-block atom is the rename-back of the corresponding block atom. -/
theorem satSignedSameBlockAtom_eq_rename_blockSignedSameBlockAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ) (i : D.blockIndex) :
    satSignedSameBlockAtom M n hn2 htb hns D c i =
      MvPolynomial.rename D.coord.symm (blockSignedSameBlockAtom c i) := by
  unfold satSignedSameBlockAtom satSignedCrossAtom blockSignedSameBlockAtom
  simp [satBlockFalse, satBlockTrue, MvPolynomial.rename_X]

/-- Flat same-block pullback formula: Boolean-projected `Pi+` sends the atom to
`1 - c X_true` after inverse pullback. -/
theorem piPlusSATBlockAlgEquiv_symm_booleanProjected_signedSameBlockAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ) (i : D.blockIndex) :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (satSignedSameBlockAtom M n hn2 htb hns D c i))) =
      (1 : SATDeciderGaugeSpace M n hn2 htb hns) -
        c • X (satBlockTrue M n hn2 htb hns D i) := by
  rw [satSignedSameBlockAtom_eq_rename_blockSignedSameBlockAtom]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  rw [zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  change MvPolynomial.rename D.coord.symm
      (blockPiPlusInvAlgHom D.blockIndex
        (blockBooleanNormalize
          (blockPiPlusAlgHom D.blockIndex (blockSignedSameBlockAtom c i)))) =
    (1 : SATDeciderGaugeSpace M n hn2 htb hns) -
      c • X (satBlockTrue M n hn2 htb hns D i)
  rw [blockPiPlusInvAlgHom_booleanProjected_signedSameBlockAtom]
  simp [MvPolynomial.rename_X, satBlockTrue]

/-- Flat `(1,1)` span certificate for the two endpoints of one SAT `Pi+` block. -/
def PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ) (i : D.blockIndex) : Prop :=
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (satSignedSameBlockAtom M n hn2 htb hns D c i))) ∈
    Submodule.span ℚ
      {q : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * SPDP.iterDerivList S
              (satSignedSameBlockAtom M n hn2 htb hns D c i))}

/-- The flat same-block atom is discharged as a concrete `(1,1)` row span:
zero row, derivative row, and derivative row multiplied by the false endpoint. -/
theorem piPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ) (i : D.blockIndex) :
    PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
      M n hn2 htb hns D c i := by
  classical
  let p : SATDeciderGaugeSpace M n hn2 htb hns :=
    satSignedSameBlockAtom M n hn2 htb hns D c i
  let xf : Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
    satBlockFalse M n hn2 htb hns D i
  let xt : Fin (cook_levin_compilation M n hn2 htb hns).numVars :=
    satBlockTrue M n hn2 htb hns D i
  let r0 : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj ((1 : SATDeciderGaugeSpace M n hn2 htb hns) * SPDP.iterDerivList [] p)
  let rX : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj ((X xf : SATDeciderGaugeSpace M n hn2 htb hns) *
      SPDP.iterDerivList [xf] p)
  let rD : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
      SPDP.iterDerivList [xf] p)
  have hr0_mem : r0 ∈ Submodule.span ℚ
      {q : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * SPDP.iterDerivList S p)} := by
    exact Submodule.subset_span ⟨[], 1, by simp, by simp, rfl⟩
  have hrX_mem : rX ∈ Submodule.span ℚ
      {q : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * SPDP.iterDerivList S p)} := by
    exact Submodule.subset_span ⟨[xf], X xf, by simp,
      by simp [MvPolynomial.totalDegree_X], rfl⟩
  have hrD_mem : rD ∈ Submodule.span ℚ
      {q : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * SPDP.iterDerivList S p)} := by
    exact Submodule.subset_span ⟨[xf], 1, by simp, by simp, rfl⟩
  have hneq : xf ≠ xt := by
    intro h
    have hf : D.coord xf = (i, false) := by simp [xf, satBlockFalse]
    have ht : D.coord xt = (i, true) := by simp [xt, satBlockTrue]
    have hcoords : (i, false) = (i, true) := by
      rw [← hf, ← ht, h]
    cases hcoords
  have hpull : (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D p)) = r0 - rX + rD := by
    subst p r0 rX rD xf xt
    rw [piPlusSATBlockAlgEquiv_symm_booleanProjected_signedSameBlockAtom]
    unfold satSignedSameBlockAtom satSignedCrossAtom SPDP.iterDerivList
    simp only [List.foldl_nil, List.foldl_cons]
    have hderiv :
        pderiv (satBlockFalse M n hn2 htb hns D i)
          ((1 : SATDeciderGaugeSpace M n hn2 htb hns) -
            c • (X (satBlockFalse M n hn2 htb hns D i) *
              X (satBlockTrue M n hn2 htb hns D i))) =
          -(c • (X (satBlockTrue M n hn2 htb hns D i) :
            SATDeciderGaugeSpace M n hn2 htb hns)) := by
      simp
    rw [hderiv]
    have hrow0 :
        mlProj ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          ((1 : SATDeciderGaugeSpace M n hn2 htb hns) -
            c • (X (satBlockFalse M n hn2 htb hns D i) *
              X (satBlockTrue M n hn2 htb hns D i)))) =
        (1 : SATDeciderGaugeSpace M n hn2 htb hns) -
            c • (X (satBlockFalse M n hn2 htb hns D i) *
              X (satBlockTrue M n hn2 htb hns D i)) := by
      rw [one_mul]
      exact mlProj_satSignedCrossAtom M n hn2 htb hns c hneq
    have hrowD :
        mlProj ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
          (-(c • (X (satBlockTrue M n hn2 htb hns D i) :
            SATDeciderGaugeSpace M n hn2 htb hns)))) =
        -(c • (X (satBlockTrue M n hn2 htb hns D i) :
          SATDeciderGaugeSpace M n hn2 htb hns)) := by
      rw [one_mul]
      rw [← neg_one_smul ℚ (c • (X (satBlockTrue M n hn2 htb hns D i) :
        SATDeciderGaugeSpace M n hn2 htb hns)), mlProj_smul, mlProj_smul, mlProj_X_block]
    have hrowX :
        mlProj ((X (satBlockFalse M n hn2 htb hns D i) :
            SATDeciderGaugeSpace M n hn2 htb hns) *
          (-(c • (X (satBlockTrue M n hn2 htb hns D i) :
            SATDeciderGaugeSpace M n hn2 htb hns)))) =
        -(c • (X (satBlockFalse M n hn2 htb hns D i) *
          X (satBlockTrue M n hn2 htb hns D i) :
          SATDeciderGaugeSpace M n hn2 htb hns)) := by
      have hxexpr :
          (X (satBlockFalse M n hn2 htb hns D i) :
              SATDeciderGaugeSpace M n hn2 htb hns) *
            (-(c • (X (satBlockTrue M n hn2 htb hns D i) :
              SATDeciderGaugeSpace M n hn2 htb hns))) =
          -(c • (X (satBlockFalse M n hn2 htb hns D i) *
            X (satBlockTrue M n hn2 htb hns D i) :
            SATDeciderGaugeSpace M n hn2 htb hns)) := by
        simp [Algebra.smul_def]
        ring
      rw [hxexpr]
      rw [← neg_one_smul ℚ (c • (X (satBlockFalse M n hn2 htb hns D i) *
        X (satBlockTrue M n hn2 htb hns D i) : SATDeciderGaugeSpace M n hn2 htb hns)),
        mlProj_smul, mlProj_smul]
      rw [mlProj_X_mul_X_ne (σ := Fin (cook_levin_compilation M n hn2 htb hns).numVars)
        (a := satBlockFalse M n hn2 htb hns D i)
        (b := satBlockTrue M n hn2 htb hns D i) hneq]
    rw [hrow0, hrowX, hrowD]
    ring
  unfold PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
  change (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize (piPlusSATBlockAlgEquiv M n hn2 htb hns D p)) ∈
    Submodule.span ℚ
      {q : SATDeciderGaugeSpace M n hn2 htb hns |
        ∃ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
          (m : SATDeciderGaugeSpace M n hn2 htb hns),
          S.length ≤ 1 ∧ m.totalDegree ≤ 1 ∧
            q = mlProj (m * SPDP.iterDerivList S p)}
  rw [hpull]
  exact Submodule.add_mem _ (Submodule.sub_mem _ hr0_mem hrX_mem) hrD_mem

/-! ## Axiom audit anchors -/

#print axioms satSignedSameBlockAtom_eq_rename_blockSignedSameBlockAtom
#print axioms piPlusSATBlockAlgEquiv_symm_booleanProjected_signedSameBlockAtom
#print axioms piPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
