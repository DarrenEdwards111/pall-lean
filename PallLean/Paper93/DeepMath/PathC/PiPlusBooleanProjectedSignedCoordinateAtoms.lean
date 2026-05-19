import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedAtoms

/-!
# SAT-coordinate signed cross-block atoms for Boolean-projected Pi+

The previous file proved the local block-coordinate signed atom certificate.
This file exposes the corresponding flat SAT-coordinate surface: given a
Cook--Levin block-coordinate equivalence `D`, any two flat variables whose block
indices are distinct form a signed cross-block atom.  Pulling it into block
coordinates gives the local theorem.

For now this is deliberately a packaging seam: it records the exact coordinate
atom and reduces the flat certificate to the already-proved block-local signed
certificate.  This is the bridge needed before matching concrete Cook--Levin
adjacency/transition factors to their `D.coord` endpoints.
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

/-- Flat SAT-coordinate signed cross-block atom. -/
noncomputable def satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    SATDeciderGaugeSpace M n hn2 htb hns :=
  (1 : SATDeciderGaugeSpace M n hn2 htb hns) - c • (X a * X b)

/-- The flat signed atom is the rename-back of the corresponding block atom. -/
theorem satSignedCrossAtom_eq_rename_blockSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    satSignedCrossAtom M n hn2 htb hns c a b =
      MvPolynomial.rename D.coord.symm
        (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
          (D.coord a).2 (D.coord b).2) := by
  unfold satSignedCrossAtom blockSignedCrossAtom
  simp [MvPolynomial.rename_X]

/-- Flat SAT-coordinate signed atom row certificate.  It is stated as a
zero-derivative source row after Boolean-projected `Pi+` and inverse pullback. -/
def PiPlusBooleanProjectedSignedCrossAtomRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  (D.coord a).1 ≠ (D.coord b).1 ∧
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (satSignedCrossAtom M n hn2 htb hns c a b))) =
    mlProj
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
        SPDP.iterDerivList []
          (satSignedCrossAtom M n hn2 htb hns c a b))

/-- A rename-surface version of the local signed certificate.  This theorem is
kept in block-coordinate language but already has the shape produced by
conjugating the SAT transform through `D.coord`. -/
theorem rename_symm_blockSignedCrossAtom_zeroDerivativeRow
    {ι : Type*} [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (c : ℚ) (bi bj : Bool) :
    MvPolynomial.rename (Equiv.refl (ι × Bool))
      (blockPiPlusInvAlgHom ι
        (blockBooleanNormalize
          (blockPiPlusAlgHom ι (blockSignedCrossAtom c i j bi bj)))) =
      MvPolynomial.rename (Equiv.refl (ι × Bool))
        (mlProj
          ((1 : MvPolynomial (ι × Bool) ℚ) *
            blockIterDerivList [] (blockSignedCrossAtom c i j bi bj))) := by
  exact congrArg (MvPolynomial.rename (Equiv.refl (ι × Bool)))
    (blockPiPlus_booleanProjected_signedCrossAtom_pullback_zeroDerivativeRow
      (hij := hij) c bi bj)

/-- The block-local signed certificate gives a flat SAT-coordinate certificate
once the endpoints are in distinct `Pi+` blocks.

This is the named coordinate-packaging seam.  The final proof is the remaining
rename-conjugation bookkeeping between `zeroProfileBooleanNormalize` on flat
`Fin` variables and `blockBooleanNormalize` under `D.coord`; it is isolated as
the single equality below rather than buried in product assembly. -/
def SignedCrossAtomCoordinateConjugation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (piPlusSATBlockAlgEquiv M n hn2 htb hns D
          (satSignedCrossAtom M n hn2 htb hns c a b))) =
    MvPolynomial.rename D.coord.symm
      (blockPiPlusInvAlgHom D.blockIndex
        (blockBooleanNormalize
          (blockPiPlusAlgHom D.blockIndex
            (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
              (D.coord a).2 (D.coord b).2))))

/-- Forward coordinate-conjugation cancellation for the concrete block-built
SAT `Pi+` algebra equivalence. -/
theorem piPlusSATBlockAlgEquiv_rename_symm_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : MvPolynomial (D.blockIndex × Bool) ℚ) :
    piPlusSATBlockAlgEquiv M n hn2 htb hns D (MvPolynomial.rename D.coord.symm p) =
      MvPolynomial.rename D.coord.symm (blockPiPlusAlgEquiv D.blockIndex p) := by
  simp [piPlusSATBlockAlgEquiv, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply]

/-- Inverse coordinate-conjugation cancellation for the concrete block-built
SAT `Pi+` algebra equivalence. -/
theorem piPlusSATBlockAlgEquiv_symm_rename_symm_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (p : MvPolynomial (D.blockIndex × Bool) ℚ) :
    (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
        (MvPolynomial.rename D.coord.symm p) =
      MvPolynomial.rename D.coord.symm ((blockPiPlusAlgEquiv D.blockIndex).symm p) := by
  simp [piPlusSATBlockAlgEquiv, MvPolynomial.renameEquiv_apply]

/-- Boolean exponents commute with renaming along an equivalence. -/
theorem zeroProfileBooleanExponent_mapDomain_equiv
    {n : Nat} {σ : Type*} (e : σ ≃ Fin n) (α : σ →₀ ℕ) :
    zeroProfileBooleanExponent (Finsupp.mapDomain e α) =
      Finsupp.mapDomain e (blockBooleanExponent α) := by
  classical
  ext i
  by_cases hi : e.symm i ∈ α.support
  · have hne : α (e.symm i) ≠ 0 := Finsupp.mem_support_iff.mp hi
    rw [zeroProfileBooleanExponent_apply]
    simp [hne]
    rw [blockBooleanExponent]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro j _hj hji
      have hij : j ≠ e.symm i := fun h => hji h
      exact Finsupp.single_eq_of_ne hij.symm
    · intro hnot
      exact False.elim (hnot hi)
  · have hz : α (e.symm i) = 0 := by
      by_contra hne
      exact hi (Finsupp.mem_support_iff.mpr hne)
    rw [zeroProfileBooleanExponent_apply]
    simp [hz]
    rw [blockBooleanExponent]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_zero]
    intro j _hj
    have hji : j ≠ e.symm i := by
      intro h
      exact hi (h ▸ _hj)
    exact Finsupp.single_eq_of_ne hji.symm

/-- Boolean normalization commutes with renaming block variables into a `Fin`
coordinate space along an equivalence. -/
theorem zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize
    {n : Nat} {σ : Type*} (e : σ ≃ Fin n) (p : MvPolynomial σ ℚ) :
    zeroProfileBooleanNormalize (MvPolynomial.rename e p) =
      MvPolynomial.rename e (blockBooleanNormalize p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
      rw [MvPolynomial.rename_monomial, zeroProfileBooleanNormalize_monomial,
        blockBooleanNormalize_monomial, MvPolynomial.rename_monomial,
        zeroProfileBooleanExponent_mapDomain_equiv e α]
  | add p q hp hq =>
      rw [map_add, zeroProfileBooleanNormalize_add, hp, hq]
      rw [show blockBooleanNormalize (p + q) =
          blockBooleanNormalize p + blockBooleanNormalize q by
        exact map_add blockBooleanNormalizeLinearMap p q]
      rw [map_add]

/-- Boolean-normalization/rename compatibility for the transformed signed atom.
This is the concrete normal-form statement needed to finish coordinate
conjugation. -/
def SignedCrossAtomBooleanNormalizeRenameCompatibility
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  zeroProfileBooleanNormalize
    (MvPolynomial.rename D.coord.symm
      (blockPiPlusAlgHom D.blockIndex
        (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
          (D.coord a).2 (D.coord b).2))) =
    MvPolynomial.rename D.coord.symm
      (blockBooleanNormalize
        (blockPiPlusAlgHom D.blockIndex
          (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
            (D.coord a).2 (D.coord b).2)))

/-- The Boolean-normalization/rename compatibility seam is unconditional: both
normalizers are the same monomial-basis Boolean quotient after transporting
variables along `D.coord`. -/
theorem signedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    SignedCrossAtomBooleanNormalizeRenameCompatibility
      M n hn2 htb hns D c a b := by
  unfold SignedCrossAtomBooleanNormalizeRenameCompatibility
  exact zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize
    D.coord.symm
    (blockPiPlusAlgHom D.blockIndex
      (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
        (D.coord a).2 (D.coord b).2))

/-- The Boolean-normalization/rename compatibility discharges the coordinate
conjugation seam once the coordinate-built algebra-equivalence cancellations are
available. -/
theorem signedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hnorm : SignedCrossAtomBooleanNormalizeRenameCompatibility
      M n hn2 htb hns D c a b) :
    SignedCrossAtomCoordinateConjugation M n hn2 htb hns D c a b := by
  unfold SignedCrossAtomCoordinateConjugation
  rw [satSignedCrossAtom_eq_rename_blockSignedCrossAtom M n hn2 htb hns D c a b]
  rw [piPlusSATBlockAlgEquiv_rename_symm_apply]
  change (piPlusSATBlockAlgEquiv M n hn2 htb hns D).symm
      (zeroProfileBooleanNormalize
        (MvPolynomial.rename D.coord.symm
          (blockPiPlusAlgHom D.blockIndex
            (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
              (D.coord a).2 (D.coord b).2)))) =
    MvPolynomial.rename D.coord.symm
      (blockPiPlusInvAlgHom D.blockIndex
        (blockBooleanNormalize
          (blockPiPlusAlgHom D.blockIndex
            (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
              (D.coord a).2 (D.coord b).2))))
  rw [hnorm]
  rw [piPlusSATBlockAlgEquiv_symm_rename_symm_apply]
  rfl

/-- Remaining flat-row compatibility after coordinate conjugation: renaming the
local zero-derivative row is the same as the flat zero-derivative row.  This is
the exact `mlProj`/rename bookkeeping left after local atom algebra. -/
def SignedCrossAtomMlProjRenameCompatibility
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  MvPolynomial.rename D.coord.symm
      (mlProj
        ((1 : MvPolynomial (D.blockIndex × Bool) ℚ) *
          blockIterDerivList []
            (blockSignedCrossAtom c (D.coord a).1 (D.coord b).1
              (D.coord a).2 (D.coord b).2))) =
    mlProj
      ((1 : SATDeciderGaugeSpace M n hn2 htb hns) *
        SPDP.iterDerivList []
          (satSignedCrossAtom M n hn2 htb hns c a b))

/-- Flat SAT-coordinate signed atoms are multilinear when their endpoints are
distinct. -/
theorem mlProj_satSignedCrossAtom
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (c : ℚ)
    {a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars}
    (hab : a ≠ b) :
    mlProj (satSignedCrossAtom M n hn2 htb hns c a b) =
      satSignedCrossAtom M n hn2 htb hns c a b := by
  unfold satSignedCrossAtom
  have hmul := mlProj_X_mul_X_ne
    (σ := Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (a := a) (b := b) hab
  rw [sub_eq_add_neg, mlProj_add]
  have hone :
      mlProj (1 : SATDeciderGaugeSpace M n hn2 htb hns) = 1 := by
    rw [show (1 : SATDeciderGaugeSpace M n hn2 htb hns) =
        MvPolynomial.monomial 0 1 by rfl, mlProj_monomial]
    have h0 : Finsupp.IsMultilinear
        (0 : Fin (cook_levin_compilation M n hn2 htb hns).numVars →₀ ℕ) := by
      intro x
      simp
    rw [if_pos h0]
  have hneg :
      mlProj (-(c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns))) =
        -(c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns)) := by
    rw [← neg_one_smul ℚ (c • (X a * X b : SATDeciderGaugeSpace M n hn2 htb hns)),
      mlProj_smul, mlProj_smul, hmul]
  rw [hone, hneg]

/-- The `mlProj`/rename compatibility seam is unconditional for signed
cross-block atoms once the two flat endpoints lie in distinct `Pi+` blocks. -/
theorem signedCrossAtomMlProjRenameCompatibility_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : (D.coord a).1 ≠ (D.coord b).1) :
    SignedCrossAtomMlProjRenameCompatibility M n hn2 htb hns D c a b := by
  unfold SignedCrossAtomMlProjRenameCompatibility
  simp [SPDP.iterDerivList, blockIterDerivList]
  rw [mlProj_blockSignedCrossAtom (hij := hab)]
  have habflat : a ≠ b := by
    intro h
    exact hab (by rw [h])
  rw [mlProj_satSignedCrossAtom M n hn2 htb hns c habflat]
  exact (satSignedCrossAtom_eq_rename_blockSignedCrossAtom M n hn2 htb hns D c a b).symm

/-- Coordinate conjugation plus the local signed atom certificate and the
isolated `mlProj`/rename compatibility yields the flat SAT-coordinate signed atom
row certificate. -/
theorem piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : (D.coord a).1 ≠ (D.coord b).1)
    (hconj : SignedCrossAtomCoordinateConjugation M n hn2 htb hns D c a b)
    (hml : SignedCrossAtomMlProjRenameCompatibility M n hn2 htb hns D c a b) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D c a b := by
  refine ⟨hab, ?_⟩
  rw [hconj]
  have hlocal := blockPiPlus_booleanProjected_signedCrossAtom_pullback_zeroDerivativeRow
    (ι := D.blockIndex) (i := (D.coord a).1) (j := (D.coord b).1)
    (hij := hab) c (D.coord a).2 (D.coord b).2
  rw [hlocal]
  exact hml

/-- The signed SAT-coordinate row certificate now follows from only the Boolean
normalization/rename seam; the `mlProj`/rename bookkeeping is unconditional for
distinct blocks. -/
theorem piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : (D.coord a).1 ≠ (D.coord b).1)
    (hnorm : SignedCrossAtomBooleanNormalizeRenameCompatibility
      M n hn2 htb hns D c a b) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D c a b := by
  exact piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
    M n hn2 htb hns D c a b hab
    (signedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
      M n hn2 htb hns D c a b hnorm)
    (signedCrossAtomMlProjRenameCompatibility_unconditional
      M n hn2 htb hns D c a b hab)

/-- Paper-scale abbreviation for the Boolean-normalization/rename seam. -/
abbrev PaperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars) : Prop :=
  SignedCrossAtomBooleanNormalizeRenameCompatibility
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b

/-- Paper-scale coordinate conjugation from the Boolean-normalization/rename
compatibility seam. -/
theorem paperScaleSignedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hnorm : PaperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility
      M htb hns c a b) :
    SignedCrossAtomCoordinateConjugation
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b :=
  signedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b hnorm

/-- The signed cross-atom coordinate-conjugation seam is unconditional.

The algebraic content is exactly that `zeroProfileBooleanNormalize` commutes
with renaming the block-coordinate Boolean ambient into flat SAT coordinates,
together with the concrete `Pi+` algebra-equivalence cancellation lemmas. -/
theorem signedCrossAtomCoordinateConjugation_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    SignedCrossAtomCoordinateConjugation M n hn2 htb hns D c a b :=
  signedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
    M n hn2 htb hns D c a b
    (signedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
      M n hn2 htb hns D c a b)

/-- Paper-scale abbreviation for the coordinate conjugation seam. -/
abbrev PaperScaleSignedCrossAtomCoordinateConjugation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars) : Prop :=
  SignedCrossAtomCoordinateConjugation
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b

/-- Paper-scale abbreviation for the flat `mlProj`/rename compatibility seam. -/
abbrev PaperScaleSignedCrossAtomMlProjRenameCompatibility
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars) : Prop :=
  SignedCrossAtomMlProjRenameCompatibility
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b

/-- Paper-scale coordinate conjugation is unconditional. -/
theorem paperScaleSignedCrossAtomCoordinateConjugation_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars) :
    PaperScaleSignedCrossAtomCoordinateConjugation M htb hns c a b :=
  signedCrossAtomCoordinateConjugation_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b

/-- Paper-scale Boolean-normalization/rename compatibility is unconditional. -/
theorem paperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars) :
    PaperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility M htb hns c a b :=
  signedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b

/-- Paper-scale `mlProj`/rename compatibility is unconditional from distinct
block endpoints. -/
theorem paperScaleSignedCrossAtomMlProjRenameCompatibility_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord a).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord b).1) :
    PaperScaleSignedCrossAtomMlProjRenameCompatibility M htb hns c a b :=
  signedCrossAtomMlProjRenameCompatibility_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b hab

/-- Signed SAT-coordinate row certificate is unconditional for distinct Pi+
blocks. -/
theorem piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hab : (D.coord a).1 ≠ (D.coord b).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M n hn2 htb hns D c a b :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
    M n hn2 htb hns D c a b hab
    (signedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
      M n hn2 htb hns D c a b)

/-- Paper-scale signed coordinate certificate from only the Boolean-normalization
/ rename seam. -/
theorem paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord a).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord b).1)
    (hnorm : PaperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility
      M htb hns c a b) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    c a b hab hnorm

/-- Paper-scale signed coordinate row certificate is unconditional for distinct
Pi+ blocks. -/
theorem paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord a).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord b).1) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    c a b hab

/-- Paper-scale signed coordinate certificate from the isolated conjugation and
`mlProj`/rename seams. -/
theorem paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (c : ℚ)
    (a b : Fin (cook_levin_compilation M (2 ^ 804)
      paperScale_ge_two htb hns).numVars)
    (hab : ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord a).1 ≠
      ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord b).1)
    (hconj : PaperScaleSignedCrossAtomCoordinateConjugation M htb hns c a b)
    (hml : PaperScaleSignedCrossAtomMlProjRenameCompatibility M htb hns c a b) :
    PiPlusBooleanProjectedSignedCrossAtomRowCertificate
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) c a b :=
  piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    c a b hab hconj hml

/-! ## Axiom audit anchors -/

#print axioms satSignedCrossAtom_eq_rename_blockSignedCrossAtom
#print axioms rename_symm_blockSignedCrossAtom_zeroDerivativeRow
#print axioms piPlusSATBlockAlgEquiv_rename_symm_apply
#print axioms piPlusSATBlockAlgEquiv_symm_rename_symm_apply
#print axioms zeroProfileBooleanNormalize_rename_equiv_blockBooleanNormalize
#print axioms signedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
#print axioms signedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
#print axioms signedCrossAtomCoordinateConjugation_unconditional
#print axioms mlProj_satSignedCrossAtom
#print axioms signedCrossAtomMlProjRenameCompatibility_unconditional
#print axioms piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation
#print axioms piPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
#print axioms piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
#print axioms paperScaleSignedCrossAtomCoordinateConjugation_of_booleanNormalizeRename
#print axioms paperScaleSignedCrossAtomCoordinateConjugation_unconditional
#print axioms paperScaleSignedCrossAtomBooleanNormalizeRenameCompatibility_unconditional
#print axioms paperScaleSignedCrossAtomMlProjRenameCompatibility_unconditional
#print axioms paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_of_booleanNormalizeRename
#print axioms paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
#print axioms paperScalePiPlusBooleanProjectedSignedCrossAtomRowCertificate_of_coordinateConjugation

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
